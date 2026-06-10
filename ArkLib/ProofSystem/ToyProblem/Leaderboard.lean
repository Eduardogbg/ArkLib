/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Proximity-Prize "bits of security" leaderboard (ABF26 §6)

A machine-checked **leaderboard contract** for the soundness of the §6 toy
protocol (Construction 6.2 / its simplified IOR Construction 6.9). The
Ethereum Foundation Proximity Prize (proximityprize.org) asks for the gap
between the *provable* security of small-field hash-based SNARGs and the
*best known attack*; at the KoalaBear-sextic regime (`ρ = 1/2`, `t = 128`)
this is the ≈64-vs-≈116-bit frontier (ABF26 §6.3 Tables 2–5, and the
standalone attack of Fenzi–Sanso, eprint 2025/2197).

## The common quantity: a δ-swept frontier

ABF26's §6.3 analysis is a **sweep over the proximity parameter δ**: every
round-by-round analysis of Construction 6.2 must pick an admissible
`δ ∈ (0, δ_min(C))` (the L6.8/L6.10 range), after which round 1's true error
is `winningSetSoundness enc δ` (Definition 6.11, "exactly") and round 2's is
the spot-check `(1-δ)^t`. The best soundness error provable by *any* such
analysis is therefore

  `bestProvableError p = ⨅ δ ∈ (0, δ_min), max (winningSetSoundness p.enc δ) ((1-δ)^t)`

and that single scalar is what the two leaderboard sides bound (the paper's
"Knowledge soundness upperbound" / "Soundness lowerbound" parheads, `.tex`
2798–2825 and 2898–2943). Crucially, the two sides may certify their bounds
at **different δ** — the X side optimizes near `δ = 1 - √ρ - η` (Johnson
regime, `.tex` 2799–2823), the Y side attacks near `δ* = 0.468`
(`tab:elias-lowerbound-thresholds`, `.tex` ~2925) — and the `⨅` makes both
legitimate bounds on the *same* quantity:

* `SecurityLowerBound p` — "we can *prove* `≥ bits` bits":
  `bestProvableError p ≤ 2^(-bits)`. Route: `bestProvableError_le` at your
  chosen δ + an upper bound on both branches of the `max` (the
  `winningSetSoundness` branch via the L6.10 bridge
  `winningSetSoundness_le_epsMCA_add`).
* `SecurityUpperBound p` — "no δ-relaxation analysis can prove `> bits` bits":
  `2^(-bits) ≤ bestProvableError p`. Route: for every admissible δ, floor one
  of the two branches (an attack on `winningSetSoundness` for large δ — the
  **proven** hooks are `epsCA_le_winningSetSoundness` (L6.13) and
  `listDecoding_le_winningSetSoundness` (L6.12) — and the spot-check term
  `(1-δ)^t` for small δ).
* `securityGap lo hi := hi.bits - lo.bits` — the scalar contestants minimise.
  `SecurityLowerBound.bits_le_of` proves `lo.bits ≤ hi.bits` (so the gap is
  `≥ 0`) by transitivity through the common scalar, axiom-cleanly.

**Honesty note.** `bestProvableError` is what δ-relaxation round-by-round
analyses can certify; the protocol's *true* security may exceed it (a
fundamentally different analysis is outside this contract). The leaderboard
narrows *this* quantity, per ABF26 §6.3.

## The pinned encoding

All Definition-6.11 objects are stated against the **fixed-encoding**
relations `relaxedRelationFor enc` / `winningSetFor enc` (the paper's code
*is* its injective encoding; see `Definitions.lean`). `ToyParams` therefore
carries `enc` (with injectivity) and derives the code as `Set.range enc`.
An earlier revision ran on existential-encoding relations, under which the
linear constraint is reparameterisable and the winning-set supremum collapses
— and the proven L6.12 could not even inhabit `ViolatingInstance`.

The Phase-1 grand-challenge framework (`ProximityGap.GrandChallenges`) feeds
the X side: a tighter `MCALowerWitness` shrinks the `ε_mca` term inside the
L6.10 bridge, which raises the provable lower bound `X`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.2 Lemmas 6.6/6.8; §6.4 Lemmas 6.10, 6.12,
  6.13; Definition 6.11; §6.3 Tables 2–5).
* [KKH26] (list-size lower bounds backing the §6.3 attack tables) and
  Fenzi–Sanso, eprint 2025/2197 (Construction 4.2 ≈ C6.2; Lemma 4.4 is a
  similar observation to Lemma 6.12, per ABF26 §6.4.1 footnote).
-/

-- Several plumbing lemmas use only a subset of the `ι`/`F` typeclass instances in their
-- types; suppress the noisy `unused...InType` / `unusedSectionVars` warnings file-wide,
-- matching the idiom in `ProximityGap/GrandChallenges.lean`.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ToyProblem

open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

/-! ## The per-δ soundness scalar (Definition 6.11 reading)

`winningSetSoundness enc δ` is the simplified IOR's actual soundness error at
proximity parameter `δ`: the supremum, over instances `(v, μ₁, μ₂, f₁, f₂)`
that *violate* the relaxed relation `R̃_{C,δ}^2` (fixed encoding `enc`), of
the winning-challenge fraction `|Ω| / |F|`. The violating constraint is
essential — over *all* inputs a valid instance has `Ω = F` (fraction `1`), so
the unrestricted sup is the trivial `1`. -/

/-- An instance of the simplified IOR whose stack `(v, μ₁, μ₂, f₁, f₂)`
violates the relaxed relation `R̃_{C,δ}^2` under the code's fixed encoding
`enc` ([ABF26] Definition 6.3 via `relaxedRelationFor`). This is the index of
the worst-case soundness supremum of Definition 6.11. -/
structure ViolatingInstance {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → F)) (δ : ℝ≥0) where
  /-- The linear-constraint vector. -/
  v : Fin k → F
  /-- First constraint value. -/
  μ₁ : F
  /-- Second constraint value. -/
  μ₂ : F
  /-- First input word. -/
  f₁ : ι → F
  /-- Second input word. -/
  f₂ : ι → F
  /-- The instance violates the relaxed two-row relation `R̃_{C,δ}^2`
  (fixed-encoding form). -/
  violates : ¬ relaxedRelationFor (ℓ := 2) enc δ v ![μ₁, μ₂] ![f₁, f₂]

/-- The winning-challenge fraction `|Ω^{f₁,f₂}_{v,μ₁,μ₂}| / |F|` of a
violating instance ([ABF26] Definition 6.11, fixed-encoding `winningSetFor`).
Always in `[0, 1]` (`winningSetFor enc … ⊆ F`). -/
noncomputable def winningSetRatio {k : ℕ} {enc : (Fin k → F) →ₗ[F] (ι → F)} {δ : ℝ≥0}
    (x : ViolatingInstance enc δ) : ℝ≥0 :=
  ((winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- **Definition 6.11 of [ABF26]** (soundness error of the simplified IOR at
proximity parameter `δ`, with the code's encoding pinned).

The worst-case winning-challenge fraction over violating instances:
`sup_{(v,μ₁,μ₂,f₁,f₂) violating R̃²} |Ω| / |F|`. This is the protocol's
*actual* soundness error after the combination-randomness round — the paper
says the soundness error of Construction 6.9 "is exactly" this quantity. The
leaderboard's common quantity `bestProvableError` sweeps it over δ. -/
noncomputable def winningSetSoundness {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → F))
    (δ : ℝ≥0) : ℝ≥0 :=
  ⨆ x : ViolatingInstance enc δ, winningSetRatio x

/-- The winning-challenge fraction never exceeds `1` (`winningSetFor enc … ⊆ F`;
cf. [ABF26] Definition 6.11). -/
theorem winningSetRatio_le_one {k : ℕ} {enc : (Fin k → F) →ₗ[F] (ι → F)} {δ : ℝ≥0}
    (x : ViolatingInstance enc δ) : winningSetRatio x ≤ 1 := by
  haveI : Nonempty F := ⟨0⟩
  have hpos : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  rw [winningSetRatio, div_le_one hpos]
  have hle : (winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard ≤ Fintype.card F := by
    have := Set.ncard_le_ncard (Set.subset_univ
      (winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂)) (Set.finite_univ)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at this
  exact_mod_cast hle

/-- The family of winning-challenge fractions is bounded above (by `1`), so
its supremum is well-behaved in the conditionally complete order `ℝ≥0`
(cf. [ABF26] Definition 6.11). -/
theorem bddAbove_winningSetRatio {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → F)) (δ : ℝ≥0) :
    BddAbove (Set.range (fun x : ViolatingInstance enc δ ↦ winningSetRatio x)) := by
  refine ⟨1, ?_⟩
  rintro r ⟨x, rfl⟩
  exact winningSetRatio_le_one x

/-- Each violating instance's winning fraction is a lower bound on the
soundness error of [ABF26] Definition 6.11 — the backbone of the attack (Y)
side: an explicit attack witness lower-bounds `winningSetSoundness`. -/
theorem winningSetRatio_le_winningSetSoundness {k : ℕ}
    {enc : (Fin k → F) →ₗ[F] (ι → F)} {δ : ℝ≥0} (x : ViolatingInstance enc δ) :
    winningSetRatio x ≤ winningSetSoundness enc δ :=
  le_ciSup (bddAbove_winningSetRatio enc δ) x

/-! ## The two proven attack hooks (Lemmas 6.13 and 6.12 on the leaderboard) -/

/-- **The correlated-agreement attack lower-bounds the simplified-IOR soundness**
(the §6.4.2 attack chain, end-to-end and machine-checked). For a linear code
`C = range enc` (injective `F`-linear `enc`), the soundness error
`winningSetSoundness enc δ` is at least the correlated agreement error
`ε_ca(C, δ)`. This is **Lemma 6.13 of [ABF26]**
(`simplified_iop_soundness_ca_lb`, fixed-encoding form) packaged as a
`ViolatingInstance` and pushed through `winningSetRatio_le_winningSetSoundness`:
the attack witness's winning fraction `|Ω|/|F| ≥ ε_ca` is a genuine lower bound
on the worst-case soundness.

This is a proven hook for Y-side submissions: a numeric `ε_ca(C, δ) ≥ 2^(-b)`
at an admissible δ floors `winningSetSoundness enc δ`. Axiom-clean (no
`sorryAx`). -/
theorem epsCA_le_winningSetSoundness {k : ℕ} [Nonempty ι] {C : Set (ι → F)} (δ : ℝ≥0)
    (hδpos : (0 : ℝ≥0) < δ) (hδlt : δ < 1)
    (enc : (Fin k → F) →ₗ[F] (ι → F)) (henc_inj : Function.Injective enc)
    (henc_range : Set.range enc = C) :
    epsCA (F := F) (A := F) C δ δ ≤ (winningSetSoundness enc δ : ENNReal) := by
  rcases eq_or_lt_of_le (zero_le (epsCA (F := F) (A := F) C δ δ)) with h | hca
  · rw [← h]; exact zero_le _
  obtain ⟨v, μ₁, μ₂, f₁, f₂, hviol, hbound⟩ :=
    simplified_iop_soundness_ca_lb C δ hδpos hδlt enc henc_inj henc_range hca
  set x : ViolatingInstance enc δ := ⟨v, μ₁, μ₂, f₁, f₂, hviol⟩ with hx
  have hF0 : (Fintype.card F : ENNReal) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hFt : (Fintype.card F : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hWReq : (winningSetRatio x : ENNReal)
      = ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ENNReal)
          / (Fintype.card F : ENNReal) := by
    rw [winningSetRatio, hx, ENNReal.coe_div (by simp [Fintype.card_ne_zero])]
    push_cast; rfl
  have hWR : (winningSetRatio x : ENNReal) ≤ (winningSetSoundness enc δ : ENNReal) := by
    exact_mod_cast winningSetRatio_le_winningSetSoundness x
  refine le_trans ?_ hWR
  rw [hWReq, ENNReal.le_div_iff_mul_le (Or.inl hF0) (Or.inl hFt)]
  exact hbound

/-- **The list-decoding attack lower-bounds the simplified-IOR soundness**
(**Lemma 6.12 of [ABF26]** hosted on the leaderboard; §6.4.1, cf. Fenzi–Sanso
eprint 2025/2197 Lemma 4.4 and the [KKH26]-backed §6.3 tables). Writing
`N := |Λ(C^{≡2}, δ)|`: for a linear code `C = range enc` with `N < |F|`,

  `N / (|F| + 2N)  ≤  winningSetSoundness enc δ`.

Derived from the proven `simplified_iop_soundness_listDecoding_lb` by packaging
its attack instance as a `ViolatingInstance` (the lemma certifies the violation
and `|winningSetFor enc …| ≥ N·|F|/(|F|+2N)`; divide by `|F|`) and pushing it
through `winningSetRatio_le_winningSetSoundness`.

This is the second proven Y-side hook: a numeric list-size lower bound (e.g.
Elias/[KKH26] at the §6.3 parameters) floors `winningSetSoundness enc δ`.
Axiom-clean (no `sorryAx`). -/
theorem listDecoding_le_winningSetSoundness {k : ℕ} [Nonempty ι] {C : Set (ι → F)}
    (δ : ℝ≥0) (hδpos : (0 : ℝ≥0) < δ) (hδlt : δ < 1)
    (enc : (Fin k → F) →ₗ[F] (ι → F)) (henc_inj : Function.Injective enc)
    (henc_range : Set.range enc = C)
    (hF : ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)
      < Fintype.card F) :
    ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
        / ((Fintype.card F : ℝ≥0)
            + 2 * ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0))
      ≤ winningSetSoundness enc δ := by
  obtain ⟨v, μ₁, μ₂, f₁, f₂, hviol, hbound⟩ :=
    simplified_iop_soundness_listDecoding_lb C δ hδpos hδlt enc henc_inj henc_range hF
  rw [ge_iff_le] at hbound
  set N : ℕ := (Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat with hN
  set x : ViolatingInstance enc δ := ⟨v, μ₁, μ₂, f₁, f₂, hviol⟩ with hx
  refine le_trans ?_ (winningSetRatio_le_winningSetSoundness x)
  have hcardF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hden : (0 : ℝ) < (Fintype.card F : ℝ) + 2 * N := by positivity
  have hkey : (N : ℝ) * Fintype.card F
      ≤ ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ℝ)
          * ((Fintype.card F : ℝ) + 2 * N) := (div_le_iff₀ hden).mp hbound
  have hreal : (N : ℝ) / ((Fintype.card F : ℝ) + 2 * N)
      ≤ ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) / (Fintype.card F : ℝ) := by
    rw [div_le_div_iff₀ hden hcardF]
    linarith [hkey]
  have hratio : winningSetRatio x
      = ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ℝ≥0) / (Fintype.card F : ℝ≥0) := rfl
  rw [hratio, ← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_div, NNReal.coe_add,
    NNReal.coe_mul]
  push_cast
  exact hreal

/-! ## The X-side vehicle (full protocol C6.2; Lemmas 6.6 / 6.8 / 6.10)

`toySoundnessError` reuses the *exact* per-round error terms of
`Spec.General.protocol62_knowledgeSound` / `protocol62_rbrKnowledgeSound`
(Lemmas 6.6 / 6.8): the `γ`-round error `ε_mca(C,δ) + |Λ(C^{≡2},δ)| / |F|` and
the spot-check error `(1-δ)^t`. The bridge from `winningSetSoundness` to its
first branch is the error-bound content of Lemma 6.10. -/

/-- The round-by-round soundness upper bound of **Lemmas 6.6 / 6.8 of [ABF26]**
(the *full* protocol C6.2) at proximity parameter `δ`: the `max` of the
combination-randomness error `ε_mca(C,δ) + |Λ(C^{≡2},δ)| / |F|` and the
spot-check error `(1-δ)^t`. These are the *exact* per-round terms of
`protocol62_knowledgeSound`. It is the X-side proof vehicle: an analysis picks
an admissible δ and bounds `bestProvableError` through it (via
`winningSetSoundness_le_toySoundnessError` and `bestProvableError_le`). -/
noncomputable def toySoundnessError (C : Set (ι → F)) (δ : ℝ≥0) (t : ℕ) : ℝ≥0 :=
  max ((epsMCA (F := F) (A := F) C δ).toNNReal +
        ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0))
      ((1 - δ) ^ t)

/-- **Error-bound content of Lemma 6.10 of [ABF26]** (`.tex` 2627–2634:
Construction 6.9 has knowledge soundness with error `ε_mca(C,δ) + Λ/|F|`).
The Definition-6.11 soundness scalar is at most the L6.10 error term:
`winningSetSoundness enc δ ≤ ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|`.

This is *only* the error bound; the full knowledge-soundness *game* of L6.10
(extractor, `O(enc + ecor)` extraction recast cost-free) is
`ToyProblem.SimplifiedIOR.simplifiedIOR_knowledgeSound` in
`Spec/SimplifiedIOR.lean` — cross-reference it (an earlier revision mislabeled
this inequality itself as "L6.10"). Paper-proof-owed (ABF26's own §6.4
result). -/
theorem winningSetSoundness_le_epsMCA_add {k : ℕ} {C : Set (ι → F)} (δ : ℝ≥0)
    (enc : (Fin k → F) →ₗ[F] (ι → F)) (henc_range : Set.range enc = C) :
    winningSetSoundness enc δ
      ≤ (epsMCA (F := F) (A := F) C δ).toNNReal
        + ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0) := by
  -- ABF26-L6.10; paper-proof-owed. `winningSetSoundness ≤ ε_mca + |Λ|/|F|` is the
  -- error-bound content of the soundness of Construction 6.9 (the 1-round form of
  -- the L6.8 γ-round analysis); the KS-game statement is
  -- `SimplifiedIOR.simplifiedIOR_knowledgeSound`.
  sorry

/-- **The simplified-IOR soundness is below the full-protocol RBR bound**
(corollary of the L6.10 bridge `winningSetSoundness_le_epsMCA_add` of [ABF26];
the bridge's `ε_mca + |Λ|/|F|` term is the first branch of the `max`). -/
theorem winningSetSoundness_le_toySoundnessError {k : ℕ} {C : Set (ι → F)}
    (δ : ℝ≥0) (t : ℕ)
    (enc : (Fin k → F) →ₗ[F] (ι → F)) (henc_range : Set.range enc = C) :
    winningSetSoundness enc δ ≤ toySoundnessError C δ t :=
  le_trans (winningSetSoundness_le_epsMCA_add δ enc henc_range) (le_max_left _ _)

/-! ## Bits of security -/

/-- Provable security in bits of a soundness error `e`: `-log₂ e`. At `e = 0`
(perfect soundness) `Real.logb 2 0 = 0`, so `bitsOfSecurity 0 = 0`; callers
exhibiting genuine perfect soundness should special-case it. For the prize
regime `e ∈ (0, 1)` so `bitsOfSecurity e > 0`. -/
noncomputable def bitsOfSecurity (e : ℝ≥0) : ℝ := -Real.logb 2 (e : ℝ)

/-! ## Parameter record (KoalaBear-sextic regime)

`ToyParams` bundles the ambient field/index, the code's **pinned injective
encoding** (the operational object — the code is `Set.range enc`), and the
plain-data numeric regime (KoalaBear field size `q`, sextic extension, rate
`ρ`, and `s, n, t`). There is deliberately **no δ field**: δ is swept inside
`bestProvableError`, per the §6.3 frontier. Full numeric population — and
swapping the placeholder encoding for the genuine KoalaBear-sextic RS/IRS
encoder — is Phase 5. -/

/-- The KoalaBear-sextic parameter regime plus its code interpretation. The
operational fields `(F, ι, k, enc, enc_injective, t)` feed `bestProvableError`;
the documentary fields `(q, ext, ρ, s, n)` record the §6.3 numeric regime for
Phase 5 and the wiki. All carrier types are pinned to `Type 0`
(`epsMCA`/`Λ` need their code at `Type 0`). -/
structure ToyParams where
  /-- Ambient field (`Type 0`; KoalaBear sextic at Phase 5). -/
  F : Type
  /-- Codeword index type (`Type 0`; `Fin n`). -/
  ι : Type
  [field : Field F]
  [fintypeF : Fintype F]
  [decEqF : DecidableEq F]
  [fintypeι : Fintype ι]
  [nonemptyι : Nonempty ι]
  /-- Message dimension `k` (gives `winningSetFor`'s `v : Fin k → F`). -/
  k : ℕ
  /-- The code's fixed `F`-linear encoding (the paper's "code as the
  injective map"; the code itself is `ToyParams.code = Set.range enc`). -/
  enc : (Fin k → F) →ₗ[F] (ι → F)
  /-- The encoding is injective (Definition 6.1's "code as injective map"). -/
  enc_injective : Function.Injective enc
  /-- Number of spot-check repetitions `t`. -/
  t : ℕ
  /-- Documentary: field characteristic-prime size `q` (KoalaBear: `2^31 - 2^24 + 1`). -/
  q : ℕ := 2 ^ 31 - 2 ^ 24 + 1
  /-- Documentary: extension degree (KoalaBear sextic: `6`). -/
  ext : ℕ := 6
  /-- Documentary: rate `ρ = k/n` (prize regime `1/2`). -/
  ρ : ℝ≥0 := 1 / 2
  /-- Documentary: interleaving / codeword symbol size `s`. -/
  s : ℕ := 1
  /-- Documentary: intended block length `n` (the intended rate is `ρ = k/n`).
  Need not equal `|ι|` for stand-in parameters. -/
  n : ℕ := 0

attribute [instance] ToyParams.field ToyParams.fintypeF ToyParams.decEqF ToyParams.fintypeι
  ToyParams.nonemptyι

/-- The interpreted base code at a parameter point: the image of the pinned
encoding ([ABF26] Definition 6.1's code-as-injective-map reading). -/
def ToyParams.code (p : ToyParams) : Set (p.ι → p.F) := Set.range p.enc

/-! ## The leaderboard's common quantity: the δ-swept frontier -/

/-- **The leaderboard's common quantity** ([ABF26] §6.3, the "Knowledge
soundness upperbound" and "Soundness lowerbound" parheads, `.tex` 2798–2825
and 2898–2943): the best soundness error provable by **any** δ-relaxation
round-by-round analysis of Construction 6.2,

  `⨅ δ ∈ (0, δ_min(C)), max (winningSetSoundness enc δ) ((1-δ)^t)`.

Reading: an analysis must pick an admissible `δ ∈ (0, δ_min(C))` (the
L6.8/L6.10 range); round 1's true error at that δ is `winningSetSoundness enc δ`
(Definition 6.11, "exactly" per the paper), round 2's is the spot-check
`(1-δ)^t`; the analysis's error is the `max`, and the best analysis takes the
infimum over δ. The protocol's *true* security may exceed this quantity (an
analysis that is not a δ-relaxation round-by-round argument is out of scope) —
the leaderboard narrows **this** quantity, per §6.3.

X-side submissions bound it from above via `bestProvableError_le` at one
chosen δ; Y-side submissions bound it from below by flooring the `max` at
*every* admissible δ (attack hooks `epsCA_le_winningSetSoundness`,
`listDecoding_le_winningSetSoundness` for the first branch; the spot-check
term floors the second). -/
noncomputable def bestProvableError (p : ToyParams) : ℝ≥0 :=
  ⨅ δ ∈ Set.Ioo (0 : ℝ≥0) ((minRelHammingDistCode p.code : ℝ≥0)),
    max (winningSetSoundness p.enc δ) ((1 - δ) ^ p.t)

/-- **The X-side entry point** (cf. [ABF26] §6.3): for any admissible
`δ ∈ (0, δ_min(C))`, the δ-swept `bestProvableError` is at most that δ's
analysis error `max (winningSetSoundness p.enc δ) ((1-δ)^t)`. A provable-
security submission picks its δ, bounds both branches of the `max` (the first
via the L6.10 bridge `winningSetSoundness_le_epsMCA_add` + an `ε_mca`/`Λ`
analysis), and concludes through this lemma. Axiom-clean. -/
theorem bestProvableError_le (p : ToyParams) {δ : ℝ≥0}
    (hδ : δ ∈ Set.Ioo (0 : ℝ≥0) ((minRelHammingDistCode p.code : ℝ≥0))) :
    bestProvableError p ≤ max (winningSetSoundness p.enc δ) ((1 - δ) ^ p.t) :=
  le_trans (ciInf_le' _ δ) (ciInf_le' _ hδ)

/-! ## The two leaderboard interfaces

Both are stated against the **same** common quantity `bestProvableError p`. A
submission is an *inhabitant*. -/

/-- **Provable security lower bound** at parameter point `p`: a number `bits`
and a proof that the δ-swept analysis frontier is `≤ 2^(-bits)` — i.e. "we
can *prove* at least `bits` bits of security" (cf. [ABF26] §6.3). The intended
route is `bestProvableError_le` at a chosen δ, then `winningSetSoundness_le_`
`toySoundnessError` / `winningSetSoundness_le_epsMCA_add` (Lemmas 6.10 / 6.6 /
6.8) plus numerics. `bits : ℝ` because the security level *is*
`bitsOfSecurity e = -log₂ e`, a real for any soundness error `e ∈ (0,1)`
(almost never an integer); the §6.3 figures the anchors quote are themselves
fractional (the attack is `2^(-116.49)`, the C6.9 MCA branch `≈ 2^(-71.5)`,
the spot-check `(1-δ)^128 ≈ 2^(-64.00)`). -/
structure SecurityLowerBound (p : ToyParams) where
  /-- The provable security level, in bits. -/
  bits : ℝ
  /-- The δ-swept analysis frontier is at most `2^(-bits)`. -/
  proof : bestProvableError p ≤ (2 : ℝ≥0) ^ (-bits)

/-- **Provable security upper bound** at parameter point `p`: a number `bits`
and a proof that the δ-swept analysis frontier is `≥ 2^(-bits)` — i.e. "no
δ-relaxation round-by-round analysis can prove *more* than `bits` bits of
security" (cf. [ABF26] §6.3–6.4). The witness floors the `max` at every
admissible δ: winning-set attacks (Lemmas 6.12 / 6.13, hooks
`listDecoding_le_winningSetSoundness` / `epsCA_le_winningSetSoundness`) for
large δ, the spot-check term `(1-δ)^t` for small δ. -/
structure SecurityUpperBound (p : ToyParams) where
  /-- The provable security ceiling, in bits. -/
  bits : ℝ
  /-- The δ-swept analysis frontier is at least `2^(-bits)`. -/
  proof : (2 : ℝ≥0) ^ (-bits) ≤ bestProvableError p

/-! ## The leaderboard metric -/

/-- **The leaderboard metric.** The scalar gap `Y − X` between the best known
attack (`hi`) and the best provable security (`lo`), both bounds on
`bestProvableError` (cf. [ABF26] §6.3 Tables 2–5). Contestants minimise this
— at the KoalaBear-sextic regime it is the ≈116 − 64 = 52-bit frontier. -/
def securityGap {p : ToyParams} (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) : ℝ :=
  hi.bits - lo.bits

/-- **The [ABF26] §6 prize gap is honest** (`lo.bits ≤ hi.bits`, so
`securityGap ≥ 0`). Proved by pure transitivity through the common scalar:
`2^(-hi.bits) ≤ bestProvableError ≤ 2^(-lo.bits)`, and `x ↦ 2^(-x)` is
strictly antitone, so `lo.bits ≤ hi.bits`. No degenerate `error = 0` case
arises: the two `2^(-·)` terms are positive and are chained transitively,
never divided by the error. Axiom-clean. -/
theorem SecurityLowerBound.bits_le_of {p : ToyParams}
    (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) :
    lo.bits ≤ hi.bits := by
  -- `2^(-hi.bits) ≤ bestProvableError ≤ 2^(-lo.bits)` in `ℝ≥0`.
  have hchain : (2 : ℝ≥0) ^ (-hi.bits) ≤ (2 : ℝ≥0) ^ (-lo.bits) :=
    le_trans hi.proof lo.proof
  -- Cast to `ℝ` and use strict monotonicity of `2^(·)`.
  have hchainR : (2 : ℝ) ^ (-hi.bits) ≤ (2 : ℝ) ^ (-lo.bits) := by
    have := (NNReal.coe_le_coe.mpr hchain)
    rwa [NNReal.coe_rpow, NNReal.coe_rpow, NNReal.coe_ofNat] at this
  have hexp : -hi.bits ≤ -lo.bits :=
    (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hchainR
  linarith

/-- `securityGap` is non-negative (cf. [ABF26] §6.3; the two sides bound the
same scalar). -/
theorem securityGap_nonneg {p : ToyParams}
    (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) :
    0 ≤ securityGap lo hi := by
  have := lo.bits_le_of hi
  simp only [securityGap]; linarith

/-! ### The `bits` interpretation

A `SecurityLowerBound`/`SecurityUpperBound` `bits` field is exactly a bound on
the true bits-of-security `bitsOfSecurity (bestProvableError p)`. Together
these read: `lo.bits ≤ bitsOfSecurity (bestProvableError p) ≤ hi.bits` (when
the error is positive), i.e. the certified provable level sits below the true
frontier level, which sits below the attack ceiling. -/

/-- A provable lower bound's `bits` is at most the true bits-of-security of
the [ABF26] §6.3 frontier (equivalently to `lo.proof`, when the error is
positive). -/
theorem SecurityLowerBound.le_bitsOfSecurity {p : ToyParams} (lo : SecurityLowerBound p)
    (h : 0 < bestProvableError p) : lo.bits ≤ bitsOfSecurity (bestProvableError p) := by
  rw [bitsOfSecurity, le_neg, Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast h)]
  have := NNReal.coe_le_coe.mpr lo.proof
  rwa [NNReal.coe_rpow, NNReal.coe_ofNat] at this

/-- A provable upper bound's `bits` is at least the true bits-of-security of
the [ABF26] §6.3 frontier (equivalently to `hi.proof`, when the error is
positive). -/
theorem SecurityUpperBound.bitsOfSecurity_le {p : ToyParams} (hi : SecurityUpperBound p)
    (h : 0 < bestProvableError p) : bitsOfSecurity (bestProvableError p) ≤ hi.bits := by
  rw [bitsOfSecurity, neg_le, Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast h)]
  have := NNReal.coe_le_coe.mpr hi.proof
  rwa [NNReal.coe_rpow, NNReal.coe_ofNat] at this

/-! ## Anchor parameter point and the two current entries

`koalaIRS` fixes the KoalaBear-sextic regime numerics (`q = 2^31 - 2^24 + 1`,
sextic extension, `ρ = 1/2`, `t = 128`). Two design points keep the anchors
*honest* (no `sorry` hiding a provably-false goal):

1. **The carrier field is large.** The per-δ soundness error is a fraction
   `|Ω|/|F|`, so to even *represent* a value in the target window
   `[2^(-117), 2^(-64)]` the field must satisfy `|F| ≥ 2^117`. We use
   `GaloisField 2 128` (size `2^128`) — a stand-in of the right *order* for
   the genuine KoalaBear-sextic field (size `≈2^186`), which Phase 5
   substitutes. (Over a tiny field, `|Ω|/|F|` lives in `{0, 1/2, 1}` and the
   two anchors would be *jointly* unsatisfiable.)
2. **The encoding is opaque.** `koalaEnc`'s fine structure is hidden, so
   `bestProvableError koalaIRS` is irreducible — neither anchor's inequality
   is provably true *or* false; they are genuine owed obligations (Phase 5
   supplies the genuine RS/IRS encoder and numerics). `opaque` is axiom-clean
   (no `sorryAx`); only `koalaEnc_injective` is a tagged sorry (true of the
   genuine encoder, consistent for the opaque stand-in).

The two anchors below are `sorry`-backed by design (like Phase 1's
`MCALowerWitness.ofJohnsonBCHKS25`). -/

/-- `𝔽₂` primality, for the `GaloisField 2 128` anchor carrier. Kept `local`
so it does not leak `Fact (Nat.Prime 2)` into downstream importers. -/
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Opaque placeholder encoding over the KoalaBear-sextic-sized field
`GF(2^128)`; its fine structure is deferred to Phase 5 (the genuine RS/IRS
encoder). Keeping it `opaque` makes `bestProvableError koalaIRS` irreducible,
so the anchor inequalities are genuine owed obligations rather than computable
(and hence provably true/false) at this stand-in. The supplied witness is used
only for non-emptiness and is never unfolded. -/
noncomputable opaque koalaEnc : (Fin 2 → GaloisField 2 128) →ₗ[GaloisField 2 128]
    (Fin 3 → GaloisField 2 128) := 0

/-- Injectivity of the opaque stand-in encoder ([ABF26] Definition 6.1's
"code as the injective map" reading; true of the genuine Phase-5
KoalaBear-sextic RS/IRS encoder, and consistent for the opaque `koalaEnc` —
an injective linear `(GF(2^128))² → (GF(2^128))³` exists). Owed at Phase 5
together with the encoder itself. -/
theorem koalaEnc_injective : Function.Injective koalaEnc := by
  -- ABF26-Phase5; owed with the genuine KoalaBear-sextic encoder (any RS/IRS
  -- encoding is injective). Unprovable for the opaque stand-in by design.
  sorry

/-- The Proximity-Prize anchor parameter point: the KoalaBear-sextic regime
(`q = 2^31 - 2^24 + 1`, sextic extension, `ρ = 1/2`, `t = 128`). There is no
pinned δ — δ is swept inside `bestProvableError` per the §6.3 frontier (the
X side optimizes near `δ = 1 - √ρ - η`, the Y side attacks at `δ* = 0.468`;
a single shared δ cannot represent the frontier). The carrier is the
`2^128`-element field `GaloisField 2 128` (a same-order stand-in for the
`≈2^186`-element KoalaBear sextic; Phase 5 substitutes the real field and
encoder). The documentary numeric fields `(q, ext, ρ, s, n)` state the
*intended* KoalaBear-sextic regime (rate `ρ = k/n = 2/4 = 1/2`); the
operational stand-in `(F = GF(2^128), ι = Fin 3, k = 2, opaque enc)` does not
yet realise it — Phase 5 reconciles the two. -/
noncomputable def koalaIRS : ToyParams := by
  haveI : Fintype (GaloisField 2 128) := Fintype.ofFinite _
  classical
  exact
    { F := GaloisField 2 128
      ι := Fin 3
      k := 2
      enc := koalaEnc
      enc_injective := koalaEnc_injective
      t := 128
      q := 2 ^ 31 - 2 ^ 24 + 1
      ext := 6
      ρ := 1 / 2
      s := 1
      n := 4 }

/-- **ArkLib provable lower bound (≈64 bits) at the IRS/KoalaBear/`t=128`
point.** Cites **Lemmas 6.10 / 6.6 / 6.8 of [ABF26]** and the §6.3.1
"Knowledge soundness upperbound" analysis (`.tex` 2798–2825,
`tab:interleaved-security-analysis`): pick `δ := 1 - 1/√2 - η` with
`η = 1/|L| ≈ 2^(-18)…2^(-21)` (the tables' minimizing slack), apply
`bestProvableError_le` at that δ, bound the first `max`-branch by the L6.10
bridge + the Johnson-regime `ε_mca`/`Λ` numerics (`≈ 2^(-71.5)`), and the
spot-check branch by `(1/√2 + η)^128 ≈ 2^(-64.00)`. The binding cap is the
spot-check, so the analysis certifies ≈64 bits; `bits := 64` is the headline
integer (the certified value is marginally below 64.00 — Phase 5's numeric
chain pins it down). `sorry`-backed: the §6.3.1 numeric evaluation is
Phase-5-owed. -/
noncomputable def arklib_lowerBound_irs_t128 : SecurityLowerBound koalaIRS where
  bits := 64
  proof := by
    -- ABF26-§6.3.1; Phase-5-owed numerics. Route: `bestProvableError_le` at
    -- `δ := 1 - 1/√2 - η` (η ≈ 2^-18…2^-21, tab:interleaved-security-analysis),
    -- then `winningSetSoundness_le_epsMCA_add` (L6.10 bridge) + Johnson `ε_mca`/`Λ`
    -- numerics on the first branch and `(1/√2 + η)^128 ≤ 2^(-64)` on the second.
    sorry

/-- **List-decoding attack upper bound (≈116 bits) at the IRS/KoalaBear/`t=128`
point.** Cites **Lemma 6.12 of [ABF26]** (§6.4.1) with the [KKH26]/Elias list
bounds, cf. Fenzi–Sanso eprint 2025/2197 Lemma 4.4 (the paper's §6.4.1
footnote). The two-branch floor over the δ sweep:

* for `δ ≤ δ* = 0.468` the spot-check branch dominates:
  `(1-δ)^128 ≥ (0.532)^128 ≈ 2^(-116.6)`;
* for `δ ∈ [δ*, δ_min)` the L6.12 + Elias attack
  (`listDecoding_le_winningSetSoundness` at the §6.3 numerics) floors round 1
  at `≈ 2^(-116.49)` (`tab:elias-lowerbound-thresholds`, `.tex` ~2925).

The certified min over the sweep is `≈ 2^(-116.6)`, i.e. a ceiling of
`≈116.5–116.6` bits; `bits := 116` is the headline integer anchor (matching
the paper's ≈116-bit frontier) pending the Phase-5 sharpening that closes the
fractional overhang at the genuine KoalaBear code. `sorry`-backed: the §6.3.1
numeric evaluation (and the overhang) is Phase-5-owed. -/
noncomputable def listDecoding_upperBound_attack : SecurityUpperBound koalaIRS where
  bits := 116
  proof := by
    -- ABF26-§6.3.1-lowerbound; Phase-5-owed numerics. Route: for every admissible
    -- δ floor `max (winningSetSoundness koalaEnc δ) ((1-δ)^128)`: spot-check branch
    -- `(1-δ)^128 ≥ 0.532^128 ≈ 2^-116.6` for δ ≤ δ* = 0.468; attack branch via the
    -- PROVEN hook `listDecoding_le_winningSetSoundness` + Elias/[KKH26] list-size
    -- numerics (tab:elias-lowerbound-thresholds, ≈ 2^-116.49) for δ ≥ δ*. The
    -- integer anchor 116 additionally owes the ≈0.5-bit sharpening (certified
    -- floor ≈ 2^-116.6 < 2^-116) at the genuine Phase-5 code.
    sorry

/-- **The current leaderboard frontier.** At the KoalaBear-sextic anchor the
provable security is ≈64 bits and the best known attack ceiling is ≈116 bits,
so the gap the prize asks contestants to close is `116 − 64 = 52` bits (see
[ABF26] §6.3 Tables 2–5). The value is a pure arithmetic readoff of the two
`bits` fields — it does not depend on the anchors' owed §6 *proofs* being
correct (though, naming the anchor defs, this lemma inherits their tagged
`sorry`; the metric lemma `bits_le_of` is the anchor-independent, axiom-clean
guarantee). -/
theorem securityGap_koalaIRS_anchors :
    securityGap arklib_lowerBound_irs_t128 listDecoding_upperBound_attack = 52 := by
  simp only [securityGap, arklib_lowerBound_irs_t128, listDecoding_upperBound_attack]
  norm_num

end ToyProblem
