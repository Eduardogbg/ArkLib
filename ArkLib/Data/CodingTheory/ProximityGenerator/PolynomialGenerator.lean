/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
import ArkLib.Data.CodingTheory.ProximityGenerator.MCAGenerator
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.Data.Probability.Instances
import ArkLib.Data.CodingTheory.Prelims
import Mathlib


/-!
## Main Results

-

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BCGM25]. Full paper : https://eprint.iacr.org/2025/2051}
-/

namespace RSCode

open unitInterval CoreDefinitions

variable {F : Type} [Field F] [Fintype F]
         {ι : Type} [Fintype ι]
         (k : ℕ) -- degree of the polynomials
         (D : ι ↪ F) -- the domain of evaluation


/-- Definition 9.1 [BCGM25]. -/
noncomputable def ε_mca_RS (n d m : ℕ) : I → ℝ :=
  let ρ_sqrt := ReedSolomon.sqrtRate k D
  fun γ =>
    if γ ≤ 1 - (1 + (1 / 2 * m : ℝ)) * ρ_sqrt then
      (|Fintype.card F| : ℝ)⁻¹  *  (m + 1/2) ^ 7  * (3 * (ρ_sqrt) ^ 3)⁻¹.toReal * d * n ^ 2
    else
      1

/-- Lemma 9.3 [BCGM25]. -/
lemma univarite_powers_MCA (n d m : ℕ) (hm : 3 ≤ m) :
    IsMCAGenerator (UnivariatePowers d) (ε_mca_RS k D n d m) (ReedSolomon.code D k) := by
  sorry

/-- A function assinging the maximum degree in the `i`-the variable of the collection of
polynomials `P`. -/
noncomputable def deg_max {s : ℕ} {ℓ : Type} [Fintype ℓ] (P : ℓ → MvPolynomial (Fin s) F) :
    Fin s → ℕ :=
  fun i => Finset.sup Fintype.elems (fun j ↦ (P j).degreeOf i)

/-- For a Reed–Solomon code and define ρ:= k/n. Let `G` be a polynomial generator where each `S` is
the whole field `F`. Then, for every `m ≥ 3`, `G` has MCA for with error `∑ i, ε_mca_RS`.
Theorem 9.2 [BCGM25]. -/
lemma PolyGen_MCA_RScode (n d m : ℕ) (hm : 3 ≤ m) {ℓ : Type} [Fintype ℓ] {s : ℕ}
    {P : ℓ → MvPolynomial (Fin s) F} (G : Generator ((Fin s) → F) ℓ F)
    (hG : IsPolynomialGeneratorOfFull G P) :
    letI ε := ∑ i : Fin s, ε_mca_RS k D n (deg_max P i) m
    IsMCAGenerator G ε (ReedSolomon.code D k) := by sorry



end RSCode
