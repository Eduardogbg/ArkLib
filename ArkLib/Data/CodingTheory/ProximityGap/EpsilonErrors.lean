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

- `ProximityGap.epsCA` — ABF26 Definition 4.1: correlated agreement error
  `ε_ca(C, δ_fld, δ_int)`.
- `ProximityGap.epsCA'` — Convenience alias for the no-proximity-loss case
  `ε_ca(C, δ) := ε_ca(C, δ, δ)`.

## Note on MCA with proximity loss (ABF26 Remark 4.4)

The paper intentionally does **not** define a proximity-loss variant of `ε_mca` analogous to
`ε_ca(C, δ_fld, δ_int)`. Per Remark 4.4 this remains to be thoroughly explored, so this file
exposes only the no-loss `ε_mca(C, δ)` (added in a follow-up commit).

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
short-form notation when both fold-distance and interleaved-distance coincide. -/
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

end

end ProximityGap
