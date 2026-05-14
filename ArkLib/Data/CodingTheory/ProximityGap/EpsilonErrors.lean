/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic

/-!
# Numeric ε-error functions: ε_ca and ε_mca

Numeric versions of the proximity gap, correlated agreement (CA), and mutual correlated
agreement (MCA) error functions as defined in
*Open Problems in List Decoding and Correlated Agreement*
(Arnon, Boneh, Fenzi; April 8, 2026), Section 4.

This file implements the **numeric error-function API** for CA and MCA. It coexists with the
predicate-style API in [`Basic.lean`](Basic.lean); each predicate has a bridging
`*_iff_eps*_le` lemma elsewhere in this directory.

## Main definitions

- `ProximityGap.epsPG` — proximity gap error, introduced informally in paper §4.1.
- `ProximityGap.epsCA` — ABF26 Definition 4.1: correlated agreement error
  `ε_ca(C, δ_fld, δ_int)`.
- `ProximityGap.epsCA'` — Convenience alias for the no-proximity-loss case
  `ε_ca(C, δ) := ε_ca(C, δ, δ)`.
- `ProximityGap.epsMCA` — ABF26 Definition 4.3: mutual correlated agreement error.

## Note on MCA with proximity loss (ABF26 Remark 4.4)

The paper intentionally does **not** define a proximity-loss variant of `ε_mca` analogous to
`ε_ca(C, δ_fld, δ_int)`. Per Remark 4.4 this remains to be thoroughly explored, so this file
exposes only the no-loss `ε_mca(C, δ)`.

## Open follow-ups

The following items from ABF26 Section 4 are tracked in `ABF26_PLAN.md` §7 and remain to be
added on top of this file's definitions. Each is in scope for Phase 1 of the plan:

- **Monotonicity / antitonicity of `epsCA`** (ABF26-D4.1 sub-tasks 4–5). `epsCA` is
  *monotone* in `δ_fld` (larger fold-distance ⇒ more `γ` in the event) and **antitone**
  in `δ_int` (larger interleaved-distance ⇒ stricter `Δ_joint > δ_int` condition).
- **ABF26 Remark 4.2** — discretization: `epsCA C δ (δ + β) = epsCA C δ (δ + β')` for
  `β, β' ∈ [0, 1/n)`. Follows from `Δ ∈ {0, 1/n, ..., 1}`.
- **ABF26 Fact 4.5** — `ε_pg ≤ ε_ca ≤ ε_mca`. Requires defining `epsPG` first.
- **ABF26 Lemma 4.6** — `ε_mca = ε_ca` below `δ_min(C)/2`. Proof leans on the helper
  predicates `pairJointAgreesOn` and `mcaEvent` defined here.
- **ABF26 Lemma 4.7** — `ε_mca(C^≡t, δ) ≤ t · ε_mca(C, δ)` via union bound.
- **Bridging lemmas**: `δ_ε_correlatedAgreementAffineLines C δ ε ↔ epsCA C δ δ ≤ ε` (and
  similar for `Curves`, `AffineSpaces`) connecting the predicate API in `Basic.lean` to the
  numeric API here.

## Design notes worth flagging

- **`F` is implicit in `epsCA` but does not appear in its return type**, so callers that
  invoke `epsCA` without an explicit pair `(f₁, f₂)` (e.g. inside `epsCA'`) need
  `epsCA (F := F) C δ δ` to thread `F` through. If this becomes painful in proofs,
  switching `epsCA` to take `F` as an explicit argument is a cheap refactor.
- **`epsMCA` and `mcaEvent` are `Fin 2`-only** (the affine-line case). Paper Section 4
  considers more general interleavings; generalizing to `Fin ℓ` is a future extension,
  not required for F4.5 or L4.6.
- **`pairJointAgreesOn` and `mcaEvent` are intentionally public**, exposed as named
  anchors for the planned L4.6 proof and bridging lemmas. If they prove unhelpful in
  practice they can be inlined / marked `private`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

section

-- Universe constraints: `PMF` (used by the `Pr_{...}` notation) is universe-monomorphic at
-- `Type 0`, so `ι`, `F`, and `A` must live in `Type`, matching the existing predicate-style API
-- in `Basic.lean` (`δ_ε_correlatedAgreementAffineLines` and friends).
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **ABF26 Section 4.1 (proximity gap error).** Worst-case "bad fraction" of `γ`-points
for which a line `f₁ + γ·f₂` is `δ`-close to `C` while the line is *not* entirely `δ`-close.

Paper §4.1 page 17 introduces this informally: a code has proximity gap `ε_pg(C, δ)` if
every line is either entirely `δ`-close to `C` (i.e. every `γ ∈ F` gives a δ-close point)
or at most `ε_pg` fraction of it is — a dichotomy. The strict comparison with `ε_ca`
(`epsPG ≤ epsCA`, paper Fact 4.5) is that the "bad" set for `epsPG` (`¬ ∀ γ, line close`)
is contained in the "bad" set for `epsCA` (`¬ jointProximity`) when `C` is closed under
linear combination, since any joint codeword pair `(v₀, v₁)` produces a line of codewords
`v₀ + γ·v₁ ∈ C`. -/
noncomputable def epsPG (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if (∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ) then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ]

open Classical in
/-- **ABF26 Definition 4.1.** Correlated agreement (CA) error of an `F`-additive code `C`
with respect to fold-distance `δ_fld` and interleaved-distance `δ_int`.

The worst-case probability over pairs of words `(f₁, f₂)` and over `γ ← $ᵖ F` that

- the line `f₁ + γ·f₂` is `δ_fld`-close to `C`, **and**
- the pair `(f₁, f₂)` is **not** `δ_int`-close to the interleaved code `C^⋈ (Fin 2)`.

The second condition is `γ`-independent, so the formula simplifies to `0` when `(f₁, f₂)`
is jointly close, and to the line probability otherwise. Cf. paper Section 4.1. -/
noncomputable def epsCA (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ_fld]

/-- No-proximity-loss specialization: `ε_ca(C, δ) := ε_ca(C, δ, δ)`. Matches the paper's
short-form notation when both fold-distance and interleaved-distance coincide.

By definition `epsCA C δ δ ≡ epsCA' C δ`; no explicit `epsCA_self` simp lemma is needed
because the two forms are definitionally equal. -/
noncomputable def epsCA' (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  epsCA (F := F) C δ δ

/-- The pair `(u₀, u₁)` jointly agrees with two codewords of `C` on every position in `S`.
Equivalent in spirit to `Δ_S((u₀, u₁), C^≡2) = 0` from the paper. -/
def pairJointAgreesOn (C : Set (ι → A)) (S : Finset ι) (u₀ u₁ : ι → A) : Prop :=
  ∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ S, v₀ i = u₀ i ∧ v₁ i = u₁ i

/-- The "bad" event in ABF26 Definition 4.3: there is a witness set `S` of size at least
`(1-δ)·n` on which the line `u₀ + γ • u₁` exactly equals some codeword of `C`, but no
joint pair of codewords agrees with `(u₀, u₁)` on `S`. -/
def mcaEvent (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
    ¬ pairJointAgreesOn C S u₀ u₁

open Classical in
/-- **ABF26 Definition 4.3.** Mutual correlated agreement (MCA) error.

The worst-case probability over pairs `(f₁, f₂)` and over `γ ← $ᵖ F` of the
`mcaEvent`: a single set `S` of size `≥ (1-δ)·n` witnesses both that the line
`f₁ + γ·f₂` exactly equals some codeword of `C` on `S` **and** that no joint pair
of codewords agrees with `(f₁, f₂)` on `S`. MCA strengthens CA (Definition 4.1)
by requiring the witness set for closeness and non-agreement to coincide.

Per Remark 4.4, the paper intentionally does not define a proximity-loss variant. -/
noncomputable def epsMCA (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]

/-! ## Helpers toward ABF26 Fact 4.5

Fact 4.5 says `ε_pg ≤ ε_ca ≤ ε_mca`. The first inequality requires the underlying code to
be closed under linear combination, so we state the helper lemmas with a `Submodule F (ι → A)`
hypothesis. -/

/-- **Helper for ABF26 Fact 4.5.** If the pair `(u 0, u 1)` is jointly `δ`-close to the
interleaved code from a `Submodule` `MC`, then for *every* scalar `γ`, the line
`u 0 + γ • u 1` is `δ`-close to `MC`. The proof uses the witness codeword pair
`(v 0, v 1)` to build a single line of codewords `v 0 + γ • v 1 ∈ MC`. -/
theorem jointProximity_imp_line_close
    (MC : Submodule F (ι → A)) (u : WordStack A (Fin 2) ι) (δ : ℝ≥0)
    (h : jointProximity (C := (MC : Set (ι → A))) (u := u) δ) :
    ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ := by
  rw [← jointAgreement_iff_jointProximity] at h
  obtain ⟨S, hS_card, v, hv⟩ := h
  -- Common: pointwise agreement of `v i` and `u i` on `S`.
  have h_agree : ∀ j ∈ S, v 0 j = u 0 j ∧ v 1 j = u 1 j := by
    intro j hj
    refine ⟨?_, ?_⟩
    · have : j ∈ Finset.filter (fun k => v 0 k = u 0 k) Finset.univ := (hv 0).2 hj
      exact (Finset.mem_filter.mp this).2
    · have : j ∈ Finset.filter (fun k => v 1 k = u 1 k) Finset.univ := (hv 1).2 hj
      exact (Finset.mem_filter.mp this).2
  intro γ
  have hv_γ_mem : (v 0 + γ • v 1) ∈ (MC : Set (ι → A)) :=
    MC.add_mem (hv 0).1 (MC.smul_mem γ (hv 1).1)
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨v 0 + γ • v 1, hv_γ_mem, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, (relDist_floor_bound_iff_complement_bound _ _ _).mpr hS_card, ?_⟩
  intro j
  refine ⟨fun hj_in => ?_, fun hne hj_in => ?_⟩
  · obtain ⟨h0, h1⟩ := h_agree j hj_in
    simp [Pi.add_apply, Pi.smul_apply, h0, h1]
  · obtain ⟨h0, h1⟩ := h_agree j hj_in
    exact hne (by simp [Pi.add_apply, Pi.smul_apply, h0, h1])

end

end ProximityGap
