/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Grand Challenges from ABF26 §1

The paper *Open Problems in List Decoding and Correlated Agreement* (Arnon, Boneh, Fenzi;
April 8, 2026) frames its survey around two open problems, stated on page 5:

1. **Grand MCA Challenge.** Given a Reed-Solomon code `C := RS[F, L, k]` over a smooth
   evaluation domain `L`, with constant rate `ρ(C) := k/|L| ∈ {1/2, 1/4, 1/8, 1/16}` and a
   threshold `ε*` (e.g. `2^(-128)`), determine the largest `δ*_C ∈ [0, 1]` such that
   `ε_mca(C, δ*_C) ≤ ε*`, assuming `|F|` is sufficiently large so that such a `δ*_C` exists.

2. **Grand List Decoding Challenge.** With the same RS setup and a constant interleaving
   parameter `m`, determine the largest `δ*_C ∈ [0, 1]` such that
   `|Λ(C^≡m, δ*_C)| ≤ ε* · |F|`, again assuming sufficiently large `|F|`.

The paper notes that resolving these challenges does not require an efficient
list-decoding algorithm; the questions are purely combinatorial.

## Formalisation choices

Both challenges are stated as `Prop`-valued predicates over generic codes. The rate
constraints `ρ ∈ {1/2, 1/4, 1/8, 1/16}` and the threshold `ε* = 2^(-128)` are paper-level
parameter regimes; the Lean statement leaves `ε*` as an arbitrary `ℝ≥0` so a future
caller can plug in concrete values. Likewise the `|F|`-sufficiently-large hypothesis is a
meta-comment, not a Lean hypothesis — instantiating the predicate at a specific code
either constructs the witness `δ*_C` or rules it out.

Resolution paths:

- **Upper-bound progress**: any theorem of the form `ε_mca(RS[F, L, k], δ) ≤ ε*` for some
  computable `δ`-expression in terms of `(F, L, k, ε*)` yields a constructive witness.
  This is exactly what Table 1 of the paper summarizes, with the various `BCIKS20`,
  `BCHKS25`, `GG25`, … bounds filling in the picture.
- **Lower-bound progress**: any theorem `ε_mca(RS[F, L, k], δ) > ε*` for `δ` above some
  threshold rules out witnesses above that threshold, tightening the search.

The two challenges sit at the centre of the dependency graph of the paper: §3 list-decoding
bounds feed into the list-decoding challenge directly, and §4 / §5 results bound `ε_mca`
either above (for the upper-bound direction) or below (for the lower-bound direction).
-/

-- Several framework lemmas use only a subset of the `ι`/`F` typeclass instances in their
-- types; suppress the noisy `unused...InType` / `unusedSectionVars` warnings file-wide here,
-- matching the idiom in `Errors.lean` and `CapacityBounds.lean`.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal

universe u

/-- **ABF26 §1 Grand MCA Challenge.**

There exists a maximal `δ*_C ∈ [0, 1]` such that `ε_mca(C, δ*_C) ≤ ε*` and the bound fails
strictly above `δ*_C`. The paper poses this for `C := RS[F, L, k]` with `ρ(C)` in a
specific small set and `ε* = 2^(-128)`; in Lean we leave `C` and `ε*` generic and
specialise at the call site.

Resolution would require either constructing an explicit `δ*_C` witness with the bound and
maximality, or proving no such `δ*_C` exists for some parameter regime. Both directions
are open at the time of the paper. -/
def grandMCAChallenge {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C : LinearCode ι F) (ε_star : ℝ≥0) : Prop :=
  ∃ δ_C_star : ℝ≥0,
    δ_C_star ≤ 1 ∧
    epsMCA (F := F) (A := F) ((C : Set (ι → F))) δ_C_star ≤ (ε_star : ENNReal) ∧
    ∀ δ : ℝ≥0, δ_C_star < δ → δ ≤ 1 →
      epsMCA (F := F) (A := F) ((C : Set (ι → F))) δ > (ε_star : ENNReal)

/-- **ABF26 §1 Grand List Decoding Challenge.**

There exists a maximal `δ*_C ∈ [0, 1]` such that `|Λ(C^≡m, δ*_C)| ≤ ε* · |F|` and the
bound fails strictly above `δ*_C`. The paper poses this for `C := RS[F, L, k]` with
`ρ(C)` in a specific small set, constant interleaving parameter `m`, and `ε* = 2^(-128)`.

`|Λ(C^≡m, δ)|` is the maximised list size from `ABF26-D2.8`. The bound `ε* · |F|` is read
in `ENNReal` to handle the `Lambda = ⊤` edge case uniformly. -/
def grandListDecodingChallenge {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) : Prop :=
  ∃ δ_C_star : ℝ≥0,
    δ_C_star ≤ 1 ∧
    (ListDecodable.Lambda (C^⋈ (Fin m)) (δ_C_star : ℝ) : ENNReal) ≤
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) ∧
    ∀ δ : ℝ≥0, δ_C_star < δ → δ ≤ 1 →
      (ListDecodable.Lambda (C^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
        ((ε_star : ENNReal) * (Fintype.card F : ENNReal))

/-! ## Prize parameter regime (ABF26 §1)

The two grand-challenge boxes fix the rate to one of `{1/2, 1/4, 1/8, 1/16}` and the
threshold to `ε* = 2^(-128)`. These are paper-level numeric choices; we expose them as
`ℝ≥0` constants so the prize can be stated as a `Fin 4`-indexed family. -/

open scoped NNReal

/-- **ABF26 §1 prize rates** `{1/2, 1/4, 1/8, 1/16}`, indexed by `Fin 4` via
`ρ_j := 2^(-(j+1))`. -/
noncomputable def prizeRates (j : Fin 4) : ℝ≥0 := 1 / 2 ^ (j.val + 1)

/-- **ABF26 §1 negligibility threshold** `ε* := 2^(-128)`. -/
noncomputable def epsStar : ℝ≥0 := 1 / 2 ^ (128 : ℕ)

namespace GrandChallenges

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## Reed-Solomon + rate targets

The grand challenges are posed for `C := RS[F, L, k]` **over a smooth evaluation
domain** `L` — both prize boxes in ABF26 §1 fix "a Reed-Solomon code defined over some
smooth evaluation domain `L ⊆ F`" (a multiplicative coset of a subgroup of `F*` of
power-of-two order, ABF26 Definition 2.x / `def:smooth`). We carry this as a
`ReedSolomon.Smooth domain` instance argument — the same in-tree encoding used by
`rs_epsCA_lower_capacity_kkh26` in `CapacityBounds` — so a claimed prize resolution
cannot target a non-smooth domain. These specialisations plug the Reed-Solomon code
directly into the generic predicates; a rate-addressed companion sets `k := ⌊ρ · |L|⌋`. -/

/-- The **Grand MCA Challenge** for `C := RS[F, domain, k]` over a smooth domain. -/
def grandMCAChallengeRS (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (k : ℕ) (ε_star : ℝ≥0) : Prop :=
  grandMCAChallenge (ReedSolomon.code domain k) ε_star

/-- The **Grand MCA Challenge** for the Reed-Solomon code of rate `ρ` over a smooth
domain, i.e. `k := ⌊ρ · |L|⌋`. -/
def grandMCAChallengeRSrate (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (ρ ε_star : ℝ≥0) : Prop :=
  grandMCAChallengeRS domain ⌊ρ * (Fintype.card ι : ℝ≥0)⌋₊ ε_star

/-- The **Grand List Decoding Challenge** for `C := RS[F, domain, k]` over a smooth
domain, `m`-fold interleaved. -/
def grandListDecodingChallengeRS (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (k m : ℕ) (ε_star : ℝ≥0) : Prop :=
  grandListDecodingChallenge (ReedSolomon.code domain k : Set (ι → F)) m ε_star

/-- The **ABF26 §1 MCA prize**: resolve the Grand MCA Challenge (over a smooth domain)
at *every* prize rate `ρ ∈ {1/2,1/4,1/8,1/16}` with `ε* = 2^(-128)`. -/
def mcaPrize (domain : ι ↪ F) [ReedSolomon.Smooth domain] : Prop :=
  ∀ j : Fin 4, grandMCAChallengeRSrate domain (prizeRates j) epsStar

/-- The **ABF26 §1 list-decoding prize** at interleaving `m`: resolve the Grand List
Decoding Challenge (over a smooth domain) at every prize rate with `ε* = 2^(-128)`. -/
def listDecodingPrize (domain : ι ↪ F) [ReedSolomon.Smooth domain] (m : ℕ) : Prop :=
  ∀ j : Fin 4,
    grandListDecodingChallengeRS domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ m epsStar

/-! ## Witness-carrying resolutions for the Grand MCA Challenge

A `GrandMCAResolution` is the full data the challenge asks for: a maximal threshold `δ*`
with the MCA bound below it and strict failure above it. The two one-sided witnesses
record *partial* progress — a verified lower bound on `δ*` (an upper bound on `ε_mca`
holding at some `δ ≤ 1`) or a verified upper bound on `δ*` (a lower bound on `ε_mca`
exceeding `ε*` at some `δ`). Each one-sided witness pins one end of the search interval
for `δ*`, and accumulates monotonically as the bounds in `CapacityBounds` tighten. -/

/-- A full resolution of the Grand MCA Challenge for `C` at threshold `ε*`. -/
structure GrandMCAResolution (C : Set (ι → F)) (ε_star : ℝ≥0) where
  /-- The maximal threshold `δ*`. -/
  δStar : ℝ≥0
  /-- `δ* ∈ [0, 1]`. -/
  le_one : δStar ≤ 1
  /-- `ε_mca(C, δ*) ≤ ε*`. -/
  bound : epsMCA (F := F) (A := F) C δStar ≤ (ε_star : ENNReal)
  /-- `ε_mca(C, δ) > ε*` for every `δ ∈ (δ*, 1]`. -/
  maximal : ∀ δ : ℝ≥0, δStar < δ → δ ≤ 1 →
    epsMCA (F := F) (A := F) C δ > (ε_star : ENNReal)

/-- **Lower one-sided progress.** A radius `δ ≤ 1` at which `ε_mca` is still within `ε*`.
Forces `δ* ≥ δ` for any resolution. -/
structure MCALowerWitness (C : Set (ι → F)) (ε_star : ℝ≥0) where
  /-- The certified radius. -/
  δ : ℝ≥0
  /-- `δ ∈ [0, 1]`. -/
  le_one : δ ≤ 1
  /-- `ε_mca(C, δ) ≤ ε*`. -/
  bound : epsMCA (F := F) (A := F) C δ ≤ (ε_star : ENNReal)

/-- **Upper one-sided progress.** A radius `δ` at which `ε_mca` already exceeds `ε*`.
Forces `δ* ≤ δ` for any resolution. -/
structure MCAUpperWitness (C : Set (ι → F)) (ε_star : ℝ≥0) where
  /-- The certified radius. -/
  δ : ℝ≥0
  /-- `ε_mca(C, δ) > ε*`. -/
  exceeds : epsMCA (F := F) (A := F) C δ > (ε_star : ENNReal)

/-- A resolution of `RS[F, domain, k]` *is* a proof of the Grand MCA Challenge predicate. -/
theorem grandMCAChallenge_of_resolution {C : LinearCode ι F} {ε_star : ℝ≥0}
    (R : GrandMCAResolution (C : Set (ι → F)) ε_star) :
    grandMCAChallenge C ε_star :=
  ⟨R.δStar, R.le_one, R.bound, R.maximal⟩

/-- A lower witness bounds every resolution's threshold from below: `δ ≤ δ*`. -/
theorem MCALowerWitness.le_δStar {C : Set (ι → F)} {ε_star : ℝ≥0}
    (w : MCALowerWitness C ε_star) (R : GrandMCAResolution C ε_star) :
    w.δ ≤ R.δStar := by
  by_contra h
  push Not at h
  exact absurd w.bound (not_le.mpr (R.maximal w.δ h w.le_one))

/-- An upper witness bounds every resolution's threshold from above: `δ* ≤ δ`. Uses
`epsMCA_mono` (monotonicity of `ε_mca` in `δ`). -/
theorem MCAUpperWitness.δStar_le {C : Set (ι → F)} {ε_star : ℝ≥0}
    (w : MCAUpperWitness C ε_star) (R : GrandMCAResolution C ε_star) :
    R.δStar ≤ w.δ := by
  by_contra h
  push Not at h
  exact absurd (le_trans (epsMCA_mono C (le_of_lt h)) R.bound) (not_le.mpr w.exceeds)

/-! ## Generic bridges: a single `ε_mca` / `ε_ca` bound is a one-sided witness

These are the connective edges from `CapacityBounds`. Each is pure plumbing — sorry-free
even though the bounds they will consume are external admits. -/

/-- **Bridge (upper bound ⇒ lower witness).** Any `ε_mca(C, δ) ≤ ε*` at `δ ≤ 1` is an
`MCALowerWitness`. -/
def MCALowerWitness.ofLe {C : Set (ι → F)} {ε_star δ : ℝ≥0}
    (hδ : δ ≤ 1) (h : epsMCA (F := F) (A := F) C δ ≤ (ε_star : ENNReal)) :
    MCALowerWitness C ε_star := ⟨δ, hδ, h⟩

/-- **Bridge (lower bound ⇒ upper witness).** Any `ε_mca(C, δ) > ε*` is an
`MCAUpperWitness`. -/
def MCAUpperWitness.ofGt {C : Set (ι → F)} {ε_star δ : ℝ≥0}
    (h : epsMCA (F := F) (A := F) C δ > (ε_star : ENNReal)) :
    MCAUpperWitness C ε_star := ⟨δ, h⟩

/-- **Bridge (CA lower bound ⇒ upper witness).** For a `Submodule` code, `ε_ca(C, δ, δ) > ε*`
forces `ε_mca(C, δ) > ε*` via `ε_ca ≤ ε_mca` (ABF26 Fact 4.5, `epsCA_le_epsMCA`). This is
the connective used by the §4 *lower* bounds, which are stated in terms of `ε_ca`. -/
def MCAUpperWitness.ofEpsCAGt {MC : Submodule F (ι → F)} {ε_star δ : ℝ≥0}
    (h : epsCA (F := F) (A := F) (MC : Set (ι → F)) δ δ > (ε_star : ENNReal)) :
    MCAUpperWitness (MC : Set (ι → F)) ε_star :=
  ⟨δ, lt_of_lt_of_le h (epsCA_le_epsMCA MC δ)⟩

/-! ## Concrete bridges from `CapacityBounds`

One representative of each direction, consuming an actual external-admit bound. The
numeric hypotheses (`hle` / `h_gt`) — that the explicit symbolic right-hand side compares
to `ε*` as required — are the Phase-5 computations; here we wire the symbolic edge. -/

/-- **Bridge from ABF26 Theorem 4.12 [BCHKS25 Thm 4.6].** When the Johnson-range MCA bound
for `RS[F, domain, k]` lands within `ε*` at radius `δ`, it certifies an `MCALowerWitness`.
The hypothesis `hle` is the Phase-5 numeric check that the explicit BCHKS25 RHS is `≤ ε*`. -/
def MCALowerWitness.ofJohnsonBCHKS25
    (domain : ι ↪ F) (k : ℕ) (η δ ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) - (η : ℝ))
    (hδ_le_one : δ ≤ 1)
    (hle :
        ENNReal.ofReal
          (let n : ℝ := Fintype.card ι
           let ρ_plus : ℝ := k / n + 1 / n
           let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
           ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * δ * ρ_plus)
              / (3 * ρ_plus ^ ((3 : ℝ) / 2)) * n
            + (m + 1/2) / ρ_plus ^ ((1 : ℝ) / 2))
             / (Fintype.card F : ℝ)) ≤ (ε_star : ENNReal)) :
    MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star :=
  MCALowerWitness.ofLe hδ_le_one
    (le_trans (CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ_johnson) hle)

/-! ## §4.5 conjecture and its positive-direction link to the prize

ABF26 Conjecture `conj:mca-conjecture` posits a uniform polynomial upper bound on `ε_mca`
for *all* Reed-Solomon codes. If it holds, every radius `δ < 1 - ρ` whose conjectural bound
is `≤ ε*` is a lower witness — the conjecture would directly fuel one-sided MCA progress. -/

/-- The right-hand side of the §4.5 MCA conjecture, as a real number:
`(1/|F|) · |L|^{c₁} / (ρ^{c₂} · η^{c₃})` with `ρ := k/|L|` and `η := 1 - ρ - δ`. -/
noncomputable def mcaConjectureBound (n q k : ℕ) (δ : ℝ≥0) (c₁ c₂ c₃ : ℝ) : ℝ :=
  (1 / (q : ℝ)) * (n : ℝ) ^ c₁
    / (((k : ℝ) / n) ^ c₂ * (1 - (k : ℝ) / n - (δ : ℝ)) ^ c₃)

/-- **ABF26 §4.5 Conjecture (`conj:mca-conjecture`).** There exist constants `c₁, c₂, c₃`
such that for every Reed-Solomon code `RS[F, L, k]` of rate `ρ := k/|L|` and every
`δ < 1 - ρ`, `ε_mca(C, δ) ≤ (1/|F|) · |L|^{c₁} / (ρ^{c₂} · η^{c₃})` with `η := 1 - ρ - δ`.
The constants are existentially quantified *over all RS codes*, matching the paper.

**Positive-rate hypothesis `0 < k`.** The bound has `ρ^{c₂}` in a denominator, so it is
only meaningful for positive rate `ρ = k/|L| > 0`; the prize regime `ρ ∈ {1/2,…,1/16}` is
positive anyway. We make this explicit (cf. the explicit denominator-positivity hypotheses
in `CapacityBounds`): without it the `k = 0` case would, under real division's `x/0 = 0`
convention, collapse the right-hand side to `0` and assert `ε_mca ≤ 0` (a degenerate
*strengthening*, not the intended trivially-true `+∞`).

**Source status (verified 2026-06-03).** In the current `[ABF26]` `.tex` source this
conjecture lives inside an `\ignore{…}` block (around line 2030), i.e. it is a *draft*
statement not rendered in the compiled paper. The term-by-term content here is faithful to
that draft; treat it as tracking a draft conjecture, not a stable rendered theorem. -/
def mcaConjecture : Prop :=
  ∃ c₁ c₂ c₃ : ℝ,
    ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
      {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
      (domain : ιC ↪ FC) (k : ℕ) (δ : ℝ≥0),
      0 < k →
      (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC →
      epsMCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC))) δ ≤
        ENNReal.ofReal
          (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃)

/-- **Positive-direction link to the prize.** Under the §4.5 MCA conjecture, for the
exposed constants, any RS code and radius `δ < 1 - ρ` with `δ ≤ 1` whose conjectural bound
is `≤ ε*` admits an `MCALowerWitness`. (`MCALowerWitness` is data, so the conclusion is its
`Nonempty`-ification — the constants `c₁ c₂ c₃` come from the conjecture's `Prop`-level
existential.) See `[ABF26]` §4.5, Conjecture `conj:mca-conjecture`. -/
theorem nonempty_mcaLowerWitness_of_mcaConjecture (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (k : ℕ) (ε_star δ : ℝ≥0),
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC → δ ≤ 1 →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (ε_star : ENNReal) →
        Nonempty (MCALowerWitness (ReedSolomon.code domain k : Set (ιC → FC)) ε_star) := by
  obtain ⟨c₁, c₂, c₃, hbound⟩ := h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain k ε_star δ hk hδ hδ1 hle
  exact ⟨⟨δ, hδ1, le_trans (hbound domain k δ hk hδ) hle⟩⟩

/-! ## Witness-carrying resolutions for the Grand List Decoding Challenge

The list-decoding mirror of the MCA framework. The maximised list size `Λ(C^⋈m, δ)`
(ABF26 D2.8) plays the role of `ε_mca`, the threshold is `ε* · |F|`, and monotonicity of
`Λ` in the radius (`ListDecodable.Lambda_mono`) replaces `epsMCA_mono`. -/

/-- A full resolution of the Grand List Decoding Challenge for `C`, `m`-fold interleaved. -/
structure GrandListResolution (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  /-- The maximal threshold `δ*`. -/
  δStar : ℝ≥0
  /-- `δ* ∈ [0, 1]`. -/
  le_one : δStar ≤ 1
  /-- `|Λ(C^⋈m, δ*)| ≤ ε* · |F|`. -/
  bound : (ListDecodable.Lambda (C^⋈ (Fin m)) (δStar : ℝ) : ENNReal) ≤
    ((ε_star : ENNReal) * (Fintype.card F : ENNReal))
  /-- `|Λ(C^⋈m, δ)| > ε* · |F|` for every `δ ∈ (δ*, 1]`. -/
  maximal : ∀ δ : ℝ≥0, δStar < δ → δ ≤ 1 →
    (ListDecodable.Lambda (C^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal))

/-- **Lower one-sided progress** for list decoding. A radius `δ ≤ 1` at which the list
size is still within `ε* · |F|`. Forces `δ* ≥ δ`. -/
structure ListLowerWitness (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  /-- The certified radius. -/
  δ : ℝ≥0
  /-- `δ ∈ [0, 1]`. -/
  le_one : δ ≤ 1
  /-- `|Λ(C^⋈m, δ)| ≤ ε* · |F|`. -/
  bound : (ListDecodable.Lambda (C^⋈ (Fin m)) (δ : ℝ) : ENNReal) ≤
    ((ε_star : ENNReal) * (Fintype.card F : ENNReal))

/-- **Upper one-sided progress** for list decoding. A radius `δ` at which the list size
already exceeds `ε* · |F|`. Forces `δ* ≤ δ`. -/
structure ListUpperWitness (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  /-- The certified radius. -/
  δ : ℝ≥0
  /-- `|Λ(C^⋈m, δ)| > ε* · |F|`. -/
  exceeds : (ListDecodable.Lambda (C^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
    ((ε_star : ENNReal) * (Fintype.card F : ENNReal))

/-- A list-decoding resolution of `RS[F, domain, k]` *is* a proof of the Grand List
Decoding Challenge predicate. -/
theorem grandListDecodingChallenge_of_resolution {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (R : GrandListResolution C m ε_star) :
    grandListDecodingChallenge C m ε_star :=
  ⟨R.δStar, R.le_one, R.bound, R.maximal⟩

/-- Monotonicity of the (coerced) maximised list size in the radius — the list-decoding
analogue of `epsMCA_mono`, lifted from `ListDecodable.Lambda_mono`. -/
theorem lambda_coe_mono {C : Set (ι → F)} {m : ℕ} {a b : ℝ≥0} (hab : a ≤ b) :
    (ListDecodable.Lambda (C^⋈ (Fin m)) (a : ℝ) : ENNReal) ≤
    (ListDecodable.Lambda (C^⋈ (Fin m)) (b : ℝ) : ENNReal) := by
  have hr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  exact_mod_cast ListDecodable.Lambda_mono (C := C^⋈ (Fin m)) hr

/-- A list lower witness bounds every resolution's threshold from below: `δ ≤ δ*`. -/
theorem ListLowerWitness.le_δStar {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (w : ListLowerWitness C m ε_star) (R : GrandListResolution C m ε_star) :
    w.δ ≤ R.δStar := by
  by_contra h
  push Not at h
  exact absurd w.bound (not_le.mpr (R.maximal w.δ h w.le_one))

/-- A list upper witness bounds every resolution's threshold from above: `δ* ≤ δ`. -/
theorem ListUpperWitness.δStar_le {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (w : ListUpperWitness C m ε_star) (R : GrandListResolution C m ε_star) :
    R.δStar ≤ w.δ := by
  by_contra h
  push Not at h
  exact absurd (le_trans (lambda_coe_mono (le_of_lt h)) R.bound) (not_le.mpr w.exceeds)

/-! ## First instantiation: the symbolic ρ = 1/2 interval (Phase 1 scaffold)

Phase 1 wires the *symbolic* search interval for `δ*`; the numeric endpoints (which prize
rate, which `δ` make the explicit RHS compare to `ε*`) are Phase 5. The lemma below records
that the two one-sided witnesses bracket the maximal threshold of any resolution — the
shape `[δ* ≥ Johnson-range lower witness (T4.12 [BCHKS25], [Hab25]), δ* ≤ capacity upper
witness (T4.16 [BCHKS25], [KK25])]` that one-sided progress accumulates into.
See `[ABF26]` §1 (Grand MCA Challenge) and §4.2. -/

/-- **Symbolic interval (ρ = 1/2 scaffold).** For an RS code at threshold `ε*`, a
Johnson-range lower witness and a capacity upper witness bracket the maximal MCA threshold
of any resolution: `δ_lo ≤ δ* ≤ δ_hi`. This is the connective the per-rate prize progress
accumulates into; instantiate `wlo` via `MCALowerWitness.ofJohnsonBCHKS25` and `whi` via
`MCAUpperWitness.ofEpsCAGt` once Phase-5 supplies the numeric checks.
See `[ABF26]` §1 (Grand MCA Challenge). -/
theorem mca_threshold_bracketed
    (domain : ι ↪ F) (k : ℕ) (ε_star : ℝ≥0)
    (wlo : MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (whi : MCAUpperWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (R : GrandMCAResolution (ReedSolomon.code domain k : Set (ι → F)) ε_star) :
    wlo.δ ≤ R.δStar ∧ R.δStar ≤ whi.δ :=
  ⟨wlo.le_δStar R, whi.δStar_le R⟩

end GrandChallenges

end ProximityGap
