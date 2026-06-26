/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PowerSeries.Substitution

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
/-!
# Function Fields and Rings of Regular Functions

We define the notions of Appendix A of [BCIKS20].

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/

set_option linter.style.longFile 4200

open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace BCIKS20AppendixA

section

variable {F : Type} [CommRing F] [IsDomain F]

/-- Construction of the monicized polynomial `H_tilde` in Appendix A.1 of [BCIKS20].
Note: Here `H ∈ F[X][Y]` translates to `H ∈ F[Z][Y]` in [BCIKS20], and `H_tilde` in
`Polynomial (RatFunc F)` translates to `H_tilde ∈ F(Z)[T]` in [BCIKS20]. -/
noncomputable def H_tilde (H : F[X][Y]) : Polynomial (RatFunc F) :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := (RingHom.comp Polynomial.C univPolyHom) (hᵢ d)
  let S : Polynomial (RatFunc F) := Polynomial.X / W
  let H' := Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom) S H
  W ^ (d - 1) * H'

section FieldIrreducibility

variable {F : Type} [Field F]

private lemma univPolyHom_injective :
    Function.Injective (univPolyHom (F := F)) := by
  simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))

private lemma irreducible_comp_C_mul_X_iff {K : Type} [Field K] (a : K) (ha : a ≠ 0)
    (p : K[X]) :
    Irreducible (p.comp (Polynomial.C a * Polynomial.X)) ↔ Irreducible p := by
  letI : Invertible a := invertibleOfNonzero ha
  let e : K[X] ≃ₐ[K] K[X] := Polynomial.algEquivCMulXAddC a 0
  have hp : e p = p.comp (Polynomial.C a * Polynomial.X) := by
    simp [e, ← Polynomial.comp_eq_aeval]
  rw [← hp]
  exact MulEquiv.irreducible_iff (f := (e : K[X] ≃* K[X])) (x := p)

private lemma irreducible_map_univPolyHom_of_irreducible
    {H : Polynomial (Polynomial F)} (hdeg : H.natDegree ≠ 0)
    (hH : Irreducible H) :
    Irreducible (H.map (univPolyHom (F := F))) := by
  have hprim : H.IsPrimitive := Irreducible.isPrimitive hH hdeg
  simpa [ToRatFunc.univPolyHom] using
    (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map
      (K := RatFunc F) hprim).mp hH

/-- Corrected irreducibility statement for `H_tilde`: the paper assumes positive `Y`-degree.
Without this hypothesis, a constant irreducible in `F[Z][Y]` can become a unit in `F(Z)[T]`. -/
lemma irreducibleHTildeOfIrreducible_of_natDegree_pos
    {H : Polynomial (Polynomial F)} (hdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (H_tilde H) := by
  classical
  let d : ℕ := H.natDegree
  let a : RatFunc F := univPolyHom (F := F) H.leadingCoeff
  let W : Polynomial (RatFunc F) := Polynomial.C a
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hdeg
  have hlead_ne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH_ne
  have ha_ne : a ≠ 0 := by
    intro ha
    exact hlead_ne (univPolyHom_injective (by simpa [a] using ha))
  have hmap_irreducible : Irreducible (H.map (univPolyHom (F := F))) :=
    irreducible_map_univPolyHom_of_irreducible (Nat.ne_of_gt hdeg) hH
  have hsub :
      Polynomial.X / W = Polynomial.C a⁻¹ * (Polynomial.X : Polynomial (RatFunc F)) := by
    calc
      Polynomial.X / W = Polynomial.X / Polynomial.C a := rfl
      _ = Polynomial.X * Polynomial.C a⁻¹ := Polynomial.div_C
      _ = Polynomial.C a⁻¹ * Polynomial.X := by rw [mul_comm]
  have hcomp_irreducible :
      Irreducible
        ((H.map (univPolyHom (F := F))).comp
          (Polynomial.C a⁻¹ * (Polynomial.X : Polynomial (RatFunc F)))) := by
    exact (irreducible_comp_C_mul_X_iff (a := a⁻¹) (inv_ne_zero ha_ne)
      (H.map (univPolyHom (F := F)))).mpr hmap_irreducible
  have heval :
      Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W) H =
        (H.map (univPolyHom (F := F))).comp (Polynomial.X / W) := by
    simpa [Polynomial.comp] using
      (Polynomial.eval₂_map (p := H) (f := univPolyHom (F := F))
        (g := (Polynomial.C : RatFunc F →+* Polynomial (RatFunc F)))
        (x := Polynomial.X / W)).symm
  have heval_irreducible :
      Irreducible
        (Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W)
          H) := by
    rw [heval, hsub]
    exact hcomp_irreducible
  have hunitW : IsUnit (W ^ (d - 1)) := by
    exact (isUnit_C.mpr (Ne.isUnit ha_ne)).pow (d - 1)
  rcases hunitW with ⟨u, hu⟩
  have htilde :
      H_tilde H =
        W ^ (d - 1) *
          Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / W)
            H := by
    rfl
  rw [htilde, ← hu]
  exact (irreducible_units_mul (M := Polynomial (RatFunc F)) (u := u)).2 heval_irreducible

end FieldIrreducibility

/-- The monicized version `H_tilde` is irreducible if the original polynomial `H` is irreducible
and has positive degree in `Y`, as assumed in Appendix A.1 of [BCIKS20]. -/
lemma irreducibleHTildeOfIrreducible {F : Type} [Field F] {H : Polynomial (Polynomial F)}
    (hHdeg : 0 < H.natDegree) :
    Irreducible H → Irreducible (H_tilde H) :=
  irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg

/-- The function field `𝕃` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilde H})

/-- The function field `𝕃` is a field when `H` is irreducible and has positive `Y`-degree. -/
lemma isField_of_irreducible_of_natDegree_pos {F : Type} [Field F] {H : F[X][Y]}
    (hHdeg : 0 < H.natDegree) (hH : Irreducible H) : IsField (𝕃 H) := by
  unfold 𝕃
  erw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient, principal_is_maximal_iff_irred]
  exact irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg hH

/-- The function field `𝕃` is a field under the standard Appendix A irreducibility hypothesis. -/
lemma isField_of_irreducible {F : Type} [Field F] {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Irreducible H → IsField (𝕃 H) := by
  intro h
  unfold 𝕃
  erw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient, principal_is_maximal_iff_irred]
  exact irreducibleHTildeOfIrreducible hHdeg h

/-- The function field `𝕃` is a field under positive-degree irreducibility assumptions. -/
noncomputable instance {F : Type} [Field F] {H : F[X][Y]} [hHdeg : Fact (0 < H.natDegree)]
    [inst : Fact (Irreducible H)] : Field (𝕃 H) :=
  IsField.toField (isField_of_irreducible hHdeg.out inst.out)

/-- The integral monicized polynomial corresponding to `H_tilde`, with coefficients in `F[X]`. -/
noncomputable def H_tilde' (H : F[X][Y]) : F[X][Y] :=
  if H.natDegree = 0 then
    Polynomial.C (H.coeff 0)
  else
    let hᵢ (i : ℕ) := H.coeff i
    let d := H.natDegree
    let W := hᵢ d
    Polynomial.X ^ d +
      ∑ i ∈ Finset.range d,
        Polynomial.C (hᵢ i * W ^ (d - 1 - i)) * Polynomial.X ^ i

omit [IsDomain F] in
/-- If `H` has positive degree in `Y`, then `H_tilde' H` is monic. -/
lemma H_tilde'_monic (H : F[X][Y]) (hH : 0 < H.natDegree) :
    (H_tilde' H).Monic := by
  classical
  have hdeg : H.natDegree ≠ 0 := Nat.ne_of_gt hH
  rw [H_tilde', if_neg hdeg]
  exact Polynomial.monic_X_pow_add <| (Polynomial.degree_sum_le _ _).trans_lt <| by
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe H.natDegree)).2 <| by
      intro i hi
      exact (Polynomial.degree_C_mul_X_pow_le i _).trans_lt
        (WithBot.coe_lt_coe.2 (Finset.mem_range.mp hi))

private lemma monicize_term {K : Type} [Field K] (a b : K) (i d : ℕ)
    (ha : a ≠ 0) (hi : i < d) :
    (Polynomial.C a ^ (d - 1)) * (Polynomial.C b * (Polynomial.X / Polynomial.C a) ^ i) =
      Polynomial.C (b * a ^ (d - 1 - i)) * Polynomial.X ^ i := by
  rw [Polynomial.div_C, mul_pow]
  rw [show Polynomial.C a ^ (d - 1) = Polynomial.C (a ^ (d - 1)) by rw [Polynomial.C_pow]]
  rw [show Polynomial.C a⁻¹ ^ i = Polynomial.C (a⁻¹ ^ i) by rw [Polynomial.C_pow]]
  have hscalar : a ^ (d - 1) * b * a⁻¹ ^ i = b * a ^ (d - 1 - i) := by
    have hsplit : d - 1 = (d - 1 - i) + i := by omega
    rw [hsplit, pow_add, inv_pow]
    field_simp [ha]
    have hexp : d - 1 - i + i - i = d - 1 - i := by omega
    rw [hexp]
    ring_nf
  have hscalar' : a ^ (d - 1) * (b * a⁻¹ ^ i) = b * a ^ (d - 1 - i) := by
    simpa [mul_assoc] using hscalar
  calc
    Polynomial.C (a ^ (d - 1)) * (Polynomial.C b * (Polynomial.X ^ i * Polynomial.C (a⁻¹ ^ i))) =
        Polynomial.X ^ i * Polynomial.C (a ^ (d - 1) * (b * a⁻¹ ^ i)) := by
          calc
            Polynomial.C (a ^ (d - 1)) *
                (Polynomial.C b * (Polynomial.X ^ i * Polynomial.C (a⁻¹ ^ i))) =
                Polynomial.X ^ i *
                  (Polynomial.C (a ^ (d - 1)) * Polynomial.C b * Polynomial.C (a⁻¹ ^ i)) := by
                    ring
            _ = Polynomial.X ^ i * Polynomial.C (a ^ (d - 1) * (b * a⁻¹ ^ i)) := by
                  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
                  simp [mul_assoc]
    _ = Polynomial.X ^ i * Polynomial.C (b * a ^ (d - 1 - i)) := by rw [hscalar']
    _ = Polynomial.C (b * a ^ (d - 1 - i)) * Polynomial.X ^ i := by rw [mul_comm]

private lemma monicize_leading_term {K : Type} [Field K] (a : K) (d : ℕ)
    (ha : a ≠ 0) (hd : 0 < d) :
    (Polynomial.C a ^ (d - 1)) * (Polynomial.C a * (Polynomial.X / Polynomial.C a) ^ d) =
      Polynomial.X ^ d := by
  rw [Polynomial.div_C, mul_pow]
  rw [show Polynomial.C a ^ (d - 1) = Polynomial.C (a ^ (d - 1)) by rw [Polynomial.C_pow]]
  rw [show Polynomial.C a⁻¹ ^ d = Polynomial.C (a⁻¹ ^ d) by rw [Polynomial.C_pow]]
  have hscalar : a ^ (d - 1) * a * a⁻¹ ^ d = (1 : K) := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', pow_add, pow_one, inv_pow]
    field_simp [ha]
    have hexp : d - 1 + 1 - 1 = d - 1 := by omega
    rw [hexp]
  have hscalar' : a ^ (d - 1) * (a * a⁻¹ ^ d) = (1 : K) := by
    simpa [mul_assoc] using hscalar
  calc
    Polynomial.C (a ^ (d - 1)) * (Polynomial.C a * (Polynomial.X ^ d * Polynomial.C (a⁻¹ ^ d))) =
        Polynomial.X ^ d * Polynomial.C (a ^ (d - 1) * (a * a⁻¹ ^ d)) := by
          calc
            Polynomial.C (a ^ (d - 1)) *
                (Polynomial.C a * (Polynomial.X ^ d * Polynomial.C (a⁻¹ ^ d))) =
                Polynomial.X ^ d *
                  (Polynomial.C (a ^ (d - 1)) * Polynomial.C a * Polynomial.C (a⁻¹ ^ d)) := by
                    ring
            _ = Polynomial.X ^ d * Polynomial.C (a ^ (d - 1) * (a * a⁻¹ ^ d)) := by
                  rw [← Polynomial.C_mul, ← Polynomial.C_mul]
                  simp [mul_assoc]
    _ = Polynomial.X ^ d * Polynomial.C (1 : K) := by rw [hscalar']
    _ = Polynomial.X ^ d := by simp

/-- The polynomial `H_tilde'` agrees with the monicization `H_tilde` after embedding into
`Polynomial (RatFunc F)`. -/
lemma map_H_tilde'_eq_H_tilde (H : F[X][Y]) : (H_tilde' H).map univPolyHom = H_tilde H := by
  classical
  by_cases hdeg : H.natDegree = 0
  · simp only [H_tilde', hdeg, ↓reduceIte, map_C]
    have hconst : H = Polynomial.C (H.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero (by omega)
    rw [hconst, H_tilde]
    simp
  · have hH_ne : H ≠ 0 := by
      intro hzero
      apply hdeg
      simp [hzero]
    have hw_ne_zero : univPolyHom H.leadingCoeff ≠ 0 := by
      apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      rw [mem_nonZeroDivisors_iff_ne_zero]
      exact Polynomial.leadingCoeff_ne_zero.mpr hH_ne
    have hd : 0 < H.natDegree := Nat.pos_of_ne_zero hdeg
    have hEval :
        Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom)
          (Polynomial.X /
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) H =
        ∑ i ∈ Finset.range (H.natDegree + 1),
          Polynomial.C (univPolyHom (H.coeff i)) *
            (Polynomial.X /
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^ i := by
      simpa using
        (Polynomial.eval₂_eq_sum_range
          (p := H) (f := RingHom.comp Polynomial.C univPolyHom)
          (x := Polynomial.X /
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)))
    simp only [H_tilde', hdeg, ↓reduceIte, coeff_natDegree, map_mul, map_pow,
      Polynomial.map_add, Polynomial.map_pow, map_X]
    rw [H_tilde, hEval, Finset.sum_range_succ, mul_add, Finset.mul_sum, Polynomial.map_sum]
    have hsum :
        ∑ i ∈ Finset.range H.natDegree,
          ((RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
              (H.natDegree - 1)) *
            (Polynomial.C (univPolyHom (H.coeff i)) *
              (Polynomial.X /
                (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^ i) =
        ∑ i ∈ Finset.range H.natDegree,
          Polynomial.map univPolyHom
            (Polynomial.C (H.coeff i) * Polynomial.C H.leadingCoeff ^ (H.natDegree - 1 - i) *
              Polynomial.X ^ i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [Polynomial.coeff_natDegree, map_mul, map_pow] using
        monicize_term (univPolyHom H.leadingCoeff) (univPolyHom (H.coeff i)) i H.natDegree
          hw_ne_zero (Finset.mem_range.mp hi)
    have hlead :
        ((RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
            (H.natDegree - 1)) *
          (Polynomial.C (univPolyHom (H.coeff H.natDegree)) *
            (Polynomial.X /
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
              H.natDegree) =
        Polynomial.X ^ H.natDegree := by
      simpa [Polynomial.coeff_natDegree] using
        monicize_leading_term (univPolyHom H.leadingCoeff) H.natDegree hw_ne_zero hd
    rw [hlead]
    calc
      Polynomial.X ^ H.natDegree +
          ∑ i ∈ Finset.range H.natDegree,
            Polynomial.map univPolyHom
              (Polynomial.C (H.coeff i) * Polynomial.C H.leadingCoeff ^ (H.natDegree - 1 - i) *
                Polynomial.X ^ i) =
          Polynomial.X ^ H.natDegree +
            ∑ i ∈ Finset.range H.natDegree,
              (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
                  (H.natDegree - 1) *
                (Polynomial.C (univPolyHom (H.coeff i)) *
                  (Polynomial.X /
                    (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
                    i) := by
              exact congrArg (fun p => Polynomial.X ^ H.natDegree + p) hsum.symm
      _ =
          ∑ i ∈ Finset.range H.natDegree,
            (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree) ^
                (H.natDegree - 1) *
              (Polynomial.C (univPolyHom (H.coeff i)) *
                (Polynomial.X /
                  (RingHom.comp Polynomial.C univPolyHom) ((fun i => H.coeff i) H.natDegree)) ^
                  i) +
            Polynomial.X ^ H.natDegree := by
              rw [add_comm]

section IntegralIrreducibility

variable {F : Type} [Field F]

/-- The integral monicized polynomial `H_tilde'` is irreducible whenever `H` is irreducible and has
positive degree in `Y`. -/
lemma irreducibleHTilde'OfIrreducible {H : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hH : Irreducible H) :
    Irreducible (H_tilde' H) := by
  have hmap : Irreducible ((H_tilde' H).map (univPolyHom (F := F))) := by
    simpa [map_H_tilde'_eq_H_tilde] using
      irreducibleHTildeOfIrreducible_of_natDegree_pos hHdeg hH
  exact (H_tilde'_monic H hHdeg).isPrimitive.irreducible_of_irreducible_map_of_injective
    (univPolyHom_injective (F := F)) hmap

end IntegralIrreducibility

/-- The ring of regular elements `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilde' H})

/-- The ring of regular elements `𝒪` is a ring. -/
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) :=
  Ideal.Quotient.ring (Ideal.span {H_tilde' H})

/-- The ring homomorphism defining the embedding of `𝒪` into `𝕃`. -/
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) : 𝒪 H →+* 𝕃 H :=
  Ideal.quotientMap
    (I := Ideal.span {H_tilde' H}) (Ideal.span {H_tilde H})
    bivPolyHom (by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      change bivPolyHom (H_tilde' H) ∈ span {H_tilde H}
      rw [show bivPolyHom (H_tilde' H) = (H_tilde' H).map univPolyHom from rfl,
        map_H_tilde'_eq_H_tilde]
      exact Ideal.subset_span rfl)

section FieldEmbedding

variable {F : Type} [Field F]

private lemma H_tilde'_dvd_of_map_dvd_H_tilde {H p : F[X][Y]} (hHdeg : 0 < H.natDegree)
    (hp : H_tilde H ∣ p.map (univPolyHom (F := F))) :
    H_tilde' H ∣ p := by
  let q : F[X][Y] := H_tilde' H
  have hqmonic : q.Monic := H_tilde'_monic H hHdeg
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hqmonic]
  rw [← Polynomial.map_eq_zero_iff (univPolyHom_injective (F := F))]
  have hqmap_dvd_p : q.map (univPolyHom (F := F)) ∣ p.map (univPolyHom (F := F)) := by
    simpa [q, map_H_tilde'_eq_H_tilde] using hp
  have hqmap_dvd_rem :
      q.map (univPolyHom (F := F)) ∣
        (p %ₘ q).map (univPolyHom (F := F)) := by
    have hrem :
        (p %ₘ q).map (univPolyHom (F := F)) =
          p.map (univPolyHom (F := F)) -
            q.map (univPolyHom (F := F)) * (p /ₘ q).map (univPolyHom (F := F)) := by
      have h := congrArg (fun r : F[X][Y] => r.map (univPolyHom (F := F)))
        (Polynomial.modByMonic_add_div p q)
      simp only [Polynomial.map_add, Polynomial.map_mul] at h
      rw [← h]
      ring
    rw [hrem]
    exact dvd_sub hqmap_dvd_p (dvd_mul_right _ _)
  have hdegree :
      ((p %ₘ q).map (univPolyHom (F := F))).degree <
        (q.map (univPolyHom (F := F))).degree := by
    rw [Polynomial.degree_map_eq_of_injective (univPolyHom_injective (F := F))]
    rw [Polynomial.degree_map_eq_of_injective (univPolyHom_injective (F := F))]
    exact Polynomial.degree_modByMonic_lt p hqmonic
  exact Polynomial.eq_zero_of_dvd_of_degree_lt hqmap_dvd_rem hdegree

private lemma mem_span_H_tilde'_of_bivPolyHom_mem_span_H_tilde {H p : F[X][Y]}
    (hHdeg : 0 < H.natDegree)
    (hp : bivPolyHom p ∈ Ideal.span {H_tilde H}) :
    p ∈ Ideal.span {H_tilde' H} := by
  rw [Ideal.mem_span_singleton] at hp ⊢
  exact H_tilde'_dvd_of_map_dvd_H_tilde hHdeg (by
    simpa [show bivPolyHom p = p.map (univPolyHom (F := F)) from rfl] using hp)

/-- The regular quotient embeds injectively into the function-field quotient when `H` has positive
degree in `Y`. -/
lemma embeddingOf𝒪Into𝕃_injective {H : F[X][Y]} (hHdeg : 0 < H.natDegree) :
    Function.Injective (embeddingOf𝒪Into𝕃 H) := by
  unfold embeddingOf𝒪Into𝕃
  apply Ideal.quotientMap_injective'
  intro p hp
  exact mem_span_H_tilde'_of_bivPolyHom_mem_span_H_tilde hHdeg hp

end FieldEmbedding

/-- The set of regular elements inside `𝕃 H`, i.e. the set of elements of `𝕃 H`
that in fact lie in `𝒪 H`. -/
def regularElementsSet (H : F[X][Y]) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- The regular elements inside `𝕃 H`, i.e. the elements of `𝕃 H` that in fact lie in `𝒪 H`
as Type. -/
def regularElements (H : F[X][Y]) : Type :=
  {a : 𝕃 H // ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- Zero is regular. -/
@[simp]
lemma regularElementsSet_zero (H : F[X][Y]) : (0 : 𝕃 H) ∈ regularElementsSet H :=
  ⟨0, by simp⟩

/-- One is regular. -/
@[simp]
lemma regularElementsSet_one (H : F[X][Y]) : (1 : 𝕃 H) ∈ regularElementsSet H :=
  ⟨1, by simp⟩

/-- The regular elements are closed under addition. -/
lemma regularElementsSet_add {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (hb : b ∈ regularElementsSet H) :
    a + b ∈ regularElementsSet H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' + b', by simp⟩

/-- The regular elements are closed under negation. -/
lemma regularElementsSet_neg {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElementsSet H) : -a ∈ regularElementsSet H := by
  rcases ha with ⟨a', rfl⟩
  exact ⟨-a', by simp⟩

/-- The regular elements are closed under subtraction. -/
lemma regularElementsSet_sub {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (hb : b ∈ regularElementsSet H) :
    a - b ∈ regularElementsSet H := by
  simpa [sub_eq_add_neg] using regularElementsSet_add ha (regularElementsSet_neg hb)

/-- The regular elements are closed under multiplication. -/
lemma regularElementsSet_mul {H : F[X][Y]} {a b : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (hb : b ∈ regularElementsSet H) :
    a * b ∈ regularElementsSet H := by
  rcases ha with ⟨a', rfl⟩
  rcases hb with ⟨b', rfl⟩
  exact ⟨a' * b', by simp⟩

/-- The regular elements are closed under natural powers. -/
lemma regularElementsSet_pow {H : F[X][Y]} {a : 𝕃 H}
    (ha : a ∈ regularElementsSet H) (n : ℕ) : a ^ n ∈ regularElementsSet H := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [pow_succ] using regularElementsSet_mul ih ha

/-- The regular elements are closed under finite sums. -/
lemma regularElementsSet_sum {ι : Type} {H : F[X][Y]} (s : Finset ι) {f : ι → 𝕃 H}
    (hf : ∀ i ∈ s, f i ∈ regularElementsSet H) :
    (∑ i ∈ s, f i) ∈ regularElementsSet H := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simp
  · intro a s ha ih hf
    rw [Finset.sum_insert ha]
    exact regularElementsSet_add
      (hf a (by simp [ha]))
      (ih fun i hi => hf i (by simp [hi]))

/-- Finite products of regular elements are regular. -/
lemma regularElementsSet_prod {ι : Type} {H : F[X][Y]} (s : Finset ι) {f : ι → 𝕃 H}
    (hf : ∀ i ∈ s, f i ∈ regularElementsSet H) :
    (∏ i ∈ s, f i) ∈ regularElementsSet H := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simpa using regularElementsSet_one H
  · intro a s ha ih hf
    rw [Finset.prod_insert ha]
    exact regularElementsSet_mul
      (hf a (by simp [ha]))
      (ih fun i hi => hf i (by simp [hi]))

/-- Given an element `z ∈ F`, `t_z ∈ F` is a rational root of a bivariate polynomial if the pair
`(z, t_z)` is a root of the bivariate polynomial. -/
def rationalRoot (H : F[X][Y]) (z : F) : Type :=
  {t_z : F // evalEval z t_z H = 0}

/-- The rational substitution `π_z` from Appendix A.3 defined on the whole ring of
bivariate polynomials. -/
noncomputable def π_z_lift {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
    F[X][Y] →+* F :=
  Polynomial.evalEvalRingHom z root.1

/-- The rational substitution `π_z` from Appendix A.3 of [BCIKS20] is a well-defined map on the
quotient ring `𝒪`. -/
noncomputable def π_z {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
    𝒪 H →+* F :=
  Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift z root) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    simp only [π_z_lift, map_mul]
    rw [show (Polynomial.evalEvalRingHom z root.1) (H_tilde' H) = 0 from root.2]
    ring)

/-- The canonical representative of an element of `F[X][Y]` inside the ring of regular elements
`𝒪`, defined when `H` has positive degree in `Y`. -/
noncomputable def canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) : F[X][Y] :=
  let _hHt := H_tilde'_monic H hH
  Polynomial.modByMonic β.out (H_tilde' H)

/-- The canonical representative has degree strictly smaller than the defining relation. -/
lemma canonicalRepOf𝒪_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).degree < (H_tilde' H).degree := by
  rw [canonicalRepOf𝒪]
  exact Polynomial.degree_modByMonic_lt _ (H_tilde'_monic H hH)

omit [IsDomain F] in
/-- The canonical representative has natural degree bounded by the defining relation. -/
lemma canonicalRepOf𝒪_natDegree_le {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).natDegree ≤ (H_tilde' H).natDegree := by
  rw [canonicalRepOf𝒪]
  exact Polynomial.natDegree_modByMonic_le _ (H_tilde'_monic H hH)

omit [IsDomain F] in
/-- The canonical representative maps back to the original quotient element of `𝒪`. -/
@[simp]
lemma mk_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (canonicalRepOf𝒪 hH β) = β := by
  let I : Ideal F[X][Y] := Ideal.span {H_tilde' H}
  let q : F[X][Y] := H_tilde' H
  let p : F[X][Y] := β.out
  have hq_zero : Ideal.Quotient.mk I (q * (p /ₘ q)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  calc
    Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (canonicalRepOf𝒪 hH β)
        = Ideal.Quotient.mk I (p %ₘ q) := by
            simp [canonicalRepOf𝒪, I, q, p]
    _ = Ideal.Quotient.mk I (p %ₘ q) + Ideal.Quotient.mk I (q * (p /ₘ q)) := by
            simp [hq_zero]
    _ = Ideal.Quotient.mk I (p %ₘ q + q * (p /ₘ q)) := by
            rw [map_add]
    _ = Ideal.Quotient.mk I p := by
            rw [Polynomial.modByMonic_add_div]
    _ = β := by
            simp [I, p]

omit [IsDomain F] in
/-- Canonical representatives of quotient constructors are computed by `modByMonic`. -/
lemma canonicalRepOf𝒪_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y]) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) =
      p %ₘ H_tilde' H := by
  apply Polynomial.modByMonic_eq_of_dvd_sub (H_tilde'_monic H hH)
  rw [← Ideal.mem_span_singleton]
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  calc
    Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        ((Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H).out)
        = (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) := by simp
    _ = Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p := rfl

omit [IsDomain F] in
/-- The canonical representative of zero is zero. -/
@[simp]
lemma canonicalRepOf𝒪_zero {H : F[X][Y]} (hH : 0 < H.natDegree) :
    canonicalRepOf𝒪 hH (0 : 𝒪 H) = 0 := by
  simpa using (canonicalRepOf𝒪_mk (H := H) hH 0)

/-- A polynomial whose degree is already below the relation is its own canonical representative. -/
lemma canonicalRepOf𝒪_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (H_tilde' H).degree) :
    canonicalRepOf𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) = p := by
  rw [canonicalRepOf𝒪_mk]
  exact (Polynomial.modByMonic_eq_self_iff (H_tilde'_monic H hH)).2 hp

/-- `Λ` is a weight function on the ring of bivariate polynomials `F[X][Y]`. The weight of
a polynomial is the maximal weight of all monomials appearing in it with non-zero coefficients.
The weight of the zero polynomial is `−∞`.
Requires `D ≥ Bivariate.totalDegree H` to match definition in [BCIKS20]. -/
noncomputable def weight_Λ (f H : F[X][Y]) (D : ℕ) : WithBot ℕ :=
  Finset.sup
    f.support
    (fun deg =>
      WithBot.some <| deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree
    )

omit [IsDomain F] in
/-- The zero polynomial has bottom `Λ`-weight. -/
@[simp]
lemma weight_Λ_zero (H : F[X][Y]) (D : ℕ) :
    weight_Λ (0 : F[X][Y]) H D = ⊥ := by
  simp [weight_Λ]

/-- The weight function `Λ` on regular elements is the weight of their canonical representatives
in `F[X][Y]`. -/
noncomputable def weight_Λ_over_𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree) (f : 𝒪 H) (D : ℕ) :
    WithBot ℕ := weight_Λ (canonicalRepOf𝒪 hH f) H D

omit [IsDomain F] in
/-- The `𝒪`-weight of zero is bottom. -/
@[simp]
lemma weight_Λ_over_𝒪_zero {H : F[X][Y]} (hH : 0 < H.natDegree) (D : ℕ) :
    weight_Λ_over_𝒪 hH (0 : 𝒪 H) D = ⊥ := by
  simp [weight_Λ_over_𝒪]

omit [IsDomain F] in
/-- The `𝒪`-weight of a quotient constructor is computed on its canonical remainder. -/
lemma weight_Λ_over_𝒪_mk {H : F[X][Y]} (hH : 0 < H.natDegree) (p : F[X][Y])
    (D : ℕ) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D =
      weight_Λ (p %ₘ H_tilde' H) H D := by
  simp [weight_Λ_over_𝒪, canonicalRepOf𝒪_mk]

/-- If a representative is already reduced, its `𝒪`-weight is its polynomial `Λ`-weight. -/
lemma weight_Λ_over_𝒪_mk_eq_self_of_degree_lt {H : F[X][Y]} (hH : 0 < H.natDegree)
    {p : F[X][Y]} (hp : p.degree < (H_tilde' H).degree) (D : ℕ) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D =
      weight_Λ p H D := by
  simp [weight_Λ_over_𝒪, canonicalRepOf𝒪_mk_eq_self_of_degree_lt hH hp]

/-! ### Λ-weight calculus

Algebraic identities for the bivariate `Λ`-weight from Appendix A.2 of [BCIKS20]. The weight
`m := D + 1 − natDegreeY H` is the per-Y-power contribution; constants in `F[X]` contribute their
`natDegree`. -/

omit [IsDomain F] in
/-- A monomial `n` in `f`'s support contributes a lower bound on `Λ(f)`. -/
lemma le_weight_Λ_of_mem_support {f H : F[X][Y]} {D : ℕ} {n : ℕ} (hn : n ∈ f.support) :
    (WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree) :
      WithBot ℕ) ≤ weight_Λ f H D := by
  classical
  exact Finset.le_sup (f := fun deg =>
    (WithBot.some (deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree) :
      WithBot ℕ)) hn

omit [IsDomain F] in
/-- Characterization: `Λ(f) ≤ b` iff every monomial in `f`'s support contributes at most `b`. -/
lemma weight_Λ_le_iff {f H : F[X][Y]} {D b : ℕ} :
    weight_Λ f H D ≤ (WithBot.some b : WithBot ℕ) ↔
      ∀ n ∈ f.support,
        n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree ≤ b := by
  classical
  refine ⟨fun h n hn => ?_, fun h => ?_⟩
  · have := (le_weight_Λ_of_mem_support hn).trans h
    exact_mod_cast this
  · refine Finset.sup_le (fun n hn => ?_)
    exact_mod_cast (h n hn)

omit [IsDomain F] in
/-- `Λ(C c) ≤ c.natDegree`. -/
lemma weight_Λ_C_le (H : F[X][Y]) (D : ℕ) (c : F[X]) :
    weight_Λ (Polynomial.C c) H D ≤ (WithBot.some c.natDegree : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  intro n hn
  have : (Polynomial.C c : F[X][Y]).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hn0 : n = 0 := by
    by_contra h
    simp [Polynomial.coeff_C, h] at this
  subst hn0
  simp [Polynomial.coeff_C]

omit [IsDomain F] in
/-- `Λ(Y^k) ≤ k · m`. -/
lemma weight_Λ_X_pow_le (H : F[X][Y]) (D k : ℕ) :
    weight_Λ ((Polynomial.X : F[X][Y]) ^ k) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  intro n hn
  have : ((Polynomial.X : F[X][Y]) ^ k).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hnk : n = k := by
    by_contra h
    simp [Polynomial.coeff_X_pow, h] at this
  subst hnk
  simp [Polynomial.coeff_X_pow]

omit [IsDomain F] in
/-- `Λ(C c · Y^k) ≤ k · m + c.natDegree`. -/
lemma weight_Λ_C_mul_X_pow_le (H : F[X][Y]) (D : ℕ) (c : F[X]) (k : ℕ) :
    weight_Λ (Polynomial.C c * Polynomial.X ^ k) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree) : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  intro n hn
  have : (Polynomial.C c * Polynomial.X ^ k : F[X][Y]).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  have hnk : n = k := by
    by_contra h
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, h] at this
  subst hnk
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

omit [IsDomain F] in
/-- The `Λ`-weight is invariant under negation. -/
@[simp]
lemma weight_Λ_neg (f H : F[X][Y]) (D : ℕ) : weight_Λ (-f) H D = weight_Λ f H D := by
  classical
  unfold weight_Λ
  rw [Polynomial.support_neg]
  refine Finset.sup_congr rfl (fun n _ => ?_)
  simp [Polynomial.coeff_neg]

omit [IsDomain F] in
/-- `Λ(f + g) ≤ max(Λ(f), Λ(g))`. -/
lemma weight_Λ_add_le (f g H : F[X][Y]) (D : ℕ) :
    weight_Λ (f + g) H D ≤ max (weight_Λ f H D) (weight_Λ g H D) := by
  classical
  refine Finset.sup_le (fun n hn => ?_)
  -- The contribution at `n` to weight_Λ (f + g) is bounded by f's or g's contribution.
  have hcoeff : (f + g).coeff n = f.coeff n + g.coeff n := Polynomial.coeff_add _ _ _
  have hsum_ne : f.coeff n + g.coeff n ≠ 0 := by
    rw [← hcoeff]
    exact Polynomial.mem_support_iff.mp hn
  by_cases hf : f.coeff n = 0
  · -- f.coeff n = 0, so g.coeff n ≠ 0
    have hg : g.coeff n ≠ 0 := by simpa [hf] using hsum_ne
    have hng : n ∈ g.support := Polynomial.mem_support_iff.mpr hg
    have heq : (f + g).coeff n = g.coeff n := by simp [hcoeff, hf]
    change (WithBot.some _ : WithBot ℕ) ≤ _
    rw [heq]
    exact (le_weight_Λ_of_mem_support hng).trans (le_max_right _ _)
  · have hnf : n ∈ f.support := Polynomial.mem_support_iff.mpr hf
    by_cases hg : g.coeff n = 0
    · have heq : (f + g).coeff n = f.coeff n := by simp [hcoeff, hg]
      change (WithBot.some _ : WithBot ℕ) ≤ _
      rw [heq]
      exact (le_weight_Λ_of_mem_support hnf).trans (le_max_left _ _)
    · have hng : n ∈ g.support := Polynomial.mem_support_iff.mpr hg
      have hdeg : ((f + g).coeff n).natDegree ≤
          max (f.coeff n).natDegree (g.coeff n).natDegree := by
        rw [hcoeff]
        exact Polynomial.natDegree_add_le _ _
      rcases le_total (f.coeff n).natDegree (g.coeff n).natDegree with h | h
      · -- bound by g's contribution
        have hbound : ((f + g).coeff n).natDegree ≤ (g.coeff n).natDegree :=
          hdeg.trans_eq (max_eq_right h)
        have hle : n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) + (g.coeff n).natDegree :=
          Nat.add_le_add_left hbound _
        calc (WithBot.some
                (n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree) :
                WithBot ℕ)
            ≤ WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (g.coeff n).natDegree) :=
              by exact_mod_cast hle
          _ ≤ weight_Λ g H D := le_weight_Λ_of_mem_support hng
          _ ≤ max (weight_Λ f H D) (weight_Λ g H D) := le_max_right _ _
      · have hbound : ((f + g).coeff n).natDegree ≤ (f.coeff n).natDegree :=
          hdeg.trans_eq (max_eq_left h)
        have hle : n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree :=
          Nat.add_le_add_left hbound _
        calc (WithBot.some
                (n * (D + 1 - Bivariate.natDegreeY H) + ((f + g).coeff n).natDegree) :
                WithBot ℕ)
            ≤ WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (f.coeff n).natDegree) :=
              by exact_mod_cast hle
          _ ≤ weight_Λ f H D := le_weight_Λ_of_mem_support hnf
          _ ≤ max (weight_Λ f H D) (weight_Λ g H D) := le_max_left _ _

omit [IsDomain F] in
/-- `Λ(f − g) ≤ max(Λ(f), Λ(g))`. -/
lemma weight_Λ_sub_le (f g H : F[X][Y]) (D : ℕ) :
    weight_Λ (f - g) H D ≤ max (weight_Λ f H D) (weight_Λ g H D) := by
  rw [sub_eq_add_neg]
  exact (weight_Λ_add_le f (-g) H D).trans_eq (by rw [weight_Λ_neg])

omit [IsDomain F] in
/-- `Λ` of a finite sum is bounded by the max of the summands' weights. -/
lemma weight_Λ_sum_le {ι : Type} (s : Finset ι) (f : ι → F[X][Y]) (H : F[X][Y]) (D : ℕ) :
    weight_Λ (∑ i ∈ s, f i) H D ≤ s.sup (fun i => weight_Λ (f i) H D) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert]
      exact (weight_Λ_add_le _ _ _ _).trans (max_le_max le_rfl ih)

omit [IsDomain F] in
/-- Bound on the `X`-degree of a coefficient of `H` from a `totalDegree` bound. -/
lemma natDegree_coeff_le_of_totalDegree_le (f : F[X][Y]) {D : ℕ}
    (hD : Bivariate.totalDegree f ≤ D) (i : ℕ) :
    (f.coeff i).natDegree ≤ D - i := by
  classical
  by_cases hi : f.coeff i = 0
  · simp [hi]
  · have hi_in : i ∈ f.support := Polynomial.mem_support_iff.mpr hi
    have h1 : (f.coeff i).natDegree + i ≤ Bivariate.totalDegree f :=
      Bivariate.coeff_totalDegree_le f hi_in
    omega

omit [IsDomain F] in
/-- Sub-additivity for `C c · Y^k · f`: given `Λ(f) ≤ b`, multiplying by `C c · Y^k` adds
`k · m + c.natDegree` to the weight. -/
lemma weight_Λ_C_mul_X_pow_mul_le {c : F[X]} {k : ℕ} {f H : F[X][Y]} {D b : ℕ}
    (hf : weight_Λ f H D ≤ (WithBot.some b : WithBot ℕ)) :
    weight_Λ (Polynomial.C c * Polynomial.X ^ k * f) H D ≤
      (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree + b) :
        WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  rw [weight_Λ_le_iff] at hf
  intro n hn
  have hcoeff_ne : (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  have hcoeff_eq :
      (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]).coeff n =
        (if k ≤ n then c * f.coeff (n - k) else 0) := by
    rw [show (Polynomial.C c * Polynomial.X ^ k * f : F[X][Y]) =
           Polynomial.C c * (f * Polynomial.X ^ k) by ring]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
    split <;> simp
  by_cases hkn : k ≤ n
  · rw [hcoeff_eq, if_pos hkn] at hcoeff_ne
    have hf_ne : f.coeff (n - k) ≠ 0 := by
      intro h0
      apply hcoeff_ne
      rw [h0, mul_zero]
    have hn_k_in : n - k ∈ f.support := Polynomial.mem_support_iff.mpr hf_ne
    have hf_bound := hf (n - k) hn_k_in
    rw [hcoeff_eq, if_pos hkn]
    have hdeg : (c * f.coeff (n - k)).natDegree ≤ c.natDegree + (f.coeff (n - k)).natDegree :=
      Polynomial.natDegree_mul_le
    have hsplit : n = k + (n - k) := (Nat.add_sub_cancel' hkn).symm
    have hgoal :
        n * (D + 1 - Bivariate.natDegreeY H) + (c * f.coeff (n - k)).natDegree ≤
          k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree + b := by
      have h1 :
          n * (D + 1 - Bivariate.natDegreeY H) + (c * f.coeff (n - k)).natDegree ≤
            n * (D + 1 - Bivariate.natDegreeY H) +
              (c.natDegree + (f.coeff (n - k)).natDegree) :=
        Nat.add_le_add_left hdeg _
      have h2 :
          n * (D + 1 - Bivariate.natDegreeY H) +
              (c.natDegree + (f.coeff (n - k)).natDegree) =
            k * (D + 1 - Bivariate.natDegreeY H) + c.natDegree +
              ((n - k) * (D + 1 - Bivariate.natDegreeY H) +
                (f.coeff (n - k)).natDegree) := by
        have hnk : k + (n - k) = n := Nat.add_sub_cancel' hkn
        conv_lhs => rw [hsplit, Nat.add_mul]
        rw [show k + (n - k) - k = n - k from by omega]
        ring
      rw [h2] at h1
      exact h1.trans (Nat.add_le_add_left hf_bound _)
    exact hgoal
  · rw [hcoeff_eq, if_neg hkn] at hcoeff_ne
    exact (hcoeff_ne rfl).elim

/-- The `natDegree` of `H_tilde' H` matches that of `H` when `0 < H.natDegree`. -/
lemma natDegree_H_tilde' {H : F[X][Y]} (hH : 0 < H.natDegree) :
    (H_tilde' H).natDegree = H.natDegree := by
  classical
  rw [H_tilde', if_neg (Nat.ne_of_gt hH)]
  have hsum_deg :
      (∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i : F[X][Y]).degree < (H.natDegree : WithBot ℕ) :=
    (Polynomial.degree_sum_le _ _).trans_lt <|
      (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr <| by
        intro i hi
        exact (Polynomial.degree_C_mul_X_pow_le i _).trans_lt
          (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi))
  rw [show (Polynomial.X ^ H.natDegree +
        ∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i : F[X][Y]) =
      (∑ i ∈ Finset.range H.natDegree,
          Polynomial.C (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)) *
            Polynomial.X ^ i) + Polynomial.X ^ H.natDegree by ring]
  have hX_deg : (Polynomial.X ^ H.natDegree : F[X][Y]).degree = (H.natDegree : WithBot ℕ) :=
    Polynomial.degree_X_pow _
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [Polynomial.degree_add_eq_right_of_degree_lt (hsum_deg.trans_eq hX_deg.symm), hX_deg]

/-- The canonical representative has `Y`-degree strictly smaller than `H`. -/
lemma canonicalRepOf𝒪_natDegree_lt_H {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
    (canonicalRepOf𝒪 hH β).natDegree < H.natDegree := by
  classical
  by_cases hβ : canonicalRepOf𝒪 hH β = 0
  · simp [hβ, hH]
  · have hdeg := canonicalRepOf𝒪_degree_lt hH β
    have hq_ne : H_tilde' H ≠ 0 := (H_tilde'_monic H hH).ne_zero
    rw [Polynomial.degree_eq_natDegree hβ, Polynomial.degree_eq_natDegree hq_ne] at hdeg
    exact_mod_cast (by simpa [natDegree_H_tilde' hH] using hdeg)

omit [IsDomain F] in
/-- The `Λ`-weight of `H_tilde' H` is bounded by `d_H · m`, where `d_H = H.natDegree`. -/
lemma weight_Λ_H_tilde'_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    weight_Λ (H_tilde' H) H D ≤
      (WithBot.some (H.natDegree * (D + 1 - Bivariate.natDegreeY H)) : WithBot ℕ) := by
  classical
  have hbY : Bivariate.natDegreeY H = H.natDegree := rfl
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hH_in : H.natDegree ∈ H.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
  have hd_le_D : H.natDegree ≤ D := by
    have : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    omega
  rw [H_tilde', if_neg (Nat.ne_of_gt hH)]
  refine (weight_Λ_add_le _ _ _ _).trans ?_
  refine max_le ?_ ?_
  · -- weight_Λ Y^d ≤ d · m
    refine (weight_Λ_X_pow_le H D _).trans ?_
    rw [WithBot.coe_le_coe]
  · -- weight_Λ (∑ ... · Y^i) ≤ d · m
    refine (weight_Λ_sum_le _ _ _ _).trans ?_
    refine Finset.sup_le (fun i hi => ?_)
    have hi_lt : i < H.natDegree := Finset.mem_range.mp hi
    refine (weight_Λ_C_mul_X_pow_le H D _ _).trans ?_
    -- Goal: WithBot.some (i·m + (H.coeff i · W^(d-1-i)).natDegree) ≤ WithBot.some (d·m)
    rw [WithBot.coe_le_coe]
    rw [hbY]
    have hcoeff_natDeg :
        (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
          (D - i) + (H.natDegree - 1 - i) * (D - H.natDegree) := by
      have h1 :
          (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
            (H.coeff i).natDegree +
              (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree :=
        Polynomial.natDegree_mul_le
      have h2 :
          (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
            (H.natDegree - 1 - i) * (H.coeff H.natDegree).natDegree :=
        Polynomial.natDegree_pow_le
      have hi_deg : (H.coeff i).natDegree ≤ D - i :=
        natDegree_coeff_le_of_totalDegree_le H hD i
      have hd_deg : (H.coeff H.natDegree).natDegree ≤ D - H.natDegree :=
        natDegree_coeff_le_of_totalDegree_le H hD H.natDegree
      calc (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree
          ≤ (H.coeff i).natDegree +
              (H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree := h1
        _ ≤ (D - i) + (H.natDegree - 1 - i) * (H.coeff H.natDegree).natDegree := by
            exact Nat.add_le_add hi_deg h2
        _ ≤ (D - i) + (H.natDegree - 1 - i) * (D - H.natDegree) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hd_deg) _
    -- numeric bound: i·m + (D-i) + (d-1-i)(D-d) = d·m
    have hadd : i * (D + 1 - H.natDegree) +
        (H.coeff i * H.coeff H.natDegree ^ (H.natDegree - 1 - i)).natDegree ≤
          i * (D + 1 - H.natDegree) +
            ((D - i) + (H.natDegree - 1 - i) * (D - H.natDegree)) :=
      Nat.add_le_add_left hcoeff_natDeg _
    refine hadd.trans ?_
    -- Numeric identity: i*(D+1-d) + (D-i) + (d-1-i)(D-d) = d*(D+1-d)
    have hkey : i * (D + 1 - H.natDegree) +
        ((D - i) + (H.natDegree - 1 - i) * (D - H.natDegree)) =
        H.natDegree * (D + 1 - H.natDegree) := by
      have hi_le : i ≤ H.natDegree - 1 := by omega
      have hi_le_D : i ≤ D := by omega
      have hd_le_D1 : H.natDegree ≤ 1 + D := by omega
      have hd_le_D' : H.natDegree ≤ D + 1 := by omega
      zify [hd_le_D, hd_le_D', hi_le, hi_le_D, hH]
      ring
    omega

omit [IsDomain F] in
/-- One reduction step in `modByMonic` does not increase `Λ`-weight: subtracting
`C(p.leadingCoeff) · Y^(p.natDegree - d_H) · H_tilde' H` from `p` keeps the weight bounded by
`Λ(p)`. -/
lemma weight_Λ_sub_leadingCoeff_mul_H_tilde'_le {p H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hp_deg : H.natDegree ≤ p.natDegree) :
    weight_Λ (p - Polynomial.C p.leadingCoeff *
        Polynomial.X ^ (p.natDegree - H.natDegree) * H_tilde' H) H D ≤
      weight_Λ p H D := by
  classical
  refine (weight_Λ_sub_le _ _ _ _).trans ?_
  refine max_le le_rfl ?_
  refine (weight_Λ_C_mul_X_pow_mul_le (weight_Λ_H_tilde'_le hD hH)).trans ?_
  by_cases hp : p = 0
  · subst hp
    simp at hp_deg
    omega
  · have hp_lead_ne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hp_in : p.natDegree ∈ p.support := Polynomial.mem_support_iff.mpr hp_lead_ne
    refine le_trans ?_ (le_weight_Λ_of_mem_support hp_in)
    rw [WithBot.coe_le_coe]
    change (p.natDegree - H.natDegree) * (D + 1 - Bivariate.natDegreeY H) +
        (p.coeff p.natDegree).natDegree + H.natDegree * (D + 1 - Bivariate.natDegreeY H) ≤
        p.natDegree * (D + 1 - Bivariate.natDegreeY H) + (p.coeff p.natDegree).natDegree
    have hsum : (p.natDegree - H.natDegree) + H.natDegree = p.natDegree := by omega
    have hadd_mul :
        (p.natDegree - H.natDegree) * (D + 1 - Bivariate.natDegreeY H) +
            H.natDegree * (D + 1 - Bivariate.natDegreeY H) =
          p.natDegree * (D + 1 - Bivariate.natDegreeY H) := by
      rw [← Nat.add_mul, hsum]
    linarith [hadd_mul]

/-- Reduction modulo `H_tilde' H` does not increase `Λ`-weight. -/
lemma weight_Λ_modByMonic_H_tilde'_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    ∀ p : F[X][Y], weight_Λ (p %ₘ H_tilde' H) H D ≤ weight_Λ p H D
  | p => by
      classical
      have hq : (H_tilde' H).Monic := H_tilde'_monic H hH
      unfold Polynomial.modByMonic Polynomial.divModByMonicAux
      rw [dif_pos hq]
      by_cases h : (H_tilde' H).degree ≤ p.degree ∧ p ≠ 0
      · have _wf := Polynomial.div_wf_lemma h hq
        simp only [ne_eq, dite_eq_ite, ge_iff_le, p, h]
        let z := Polynomial.C p.leadingCoeff *
          Polynomial.X ^ (p.natDegree - (H_tilde' H).natDegree)
        have ih := weight_Λ_modByMonic_H_tilde'_le hD hH (p - H_tilde' H * z)
        have ih' :
            weight_Λ ((Polynomial.divModByMonicAux (p - H_tilde' H * z) hq).2) H D ≤
              weight_Λ (p - H_tilde' H * z) H D := by
          simpa [Polynomial.modByMonic, hq, z] using ih
        have hqnat : (H_tilde' H).natDegree = H.natDegree := natDegree_H_tilde' hH
        have hp_deg : H.natDegree ≤ p.natDegree := by
          have hdeg := h.1
          rw [Polynomial.degree_eq_natDegree h.2, Polynomial.degree_eq_natDegree hq.ne_zero]
            at hdeg
          exact_mod_cast (by simpa [hqnat] using hdeg)
        have hstep0 :=
          weight_Λ_sub_leadingCoeff_mul_H_tilde'_le (p := p) (H := H) hD hH hp_deg
        have hstep : weight_Λ (p - H_tilde' H * z) H D ≤ weight_Λ p H D := by
          have hz :
              z = Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - H.natDegree) := by
            simp [z, hqnat]
          rw [hz]
          convert hstep0 using 1
          ring_nf
        exact ih'.trans hstep
      · simp only [ne_eq, dite_eq_ite, ge_iff_le, p, h]
        exact le_rfl
termination_by p => p

/-- The `𝒪`-weight of a quotient constructor is bounded by any representative's `Λ`-weight. -/
lemma weight_Λ_over_𝒪_mk_le {H : F[X][Y]} {D : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (p : F[X][Y]) :
    weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) D ≤
      weight_Λ p H D := by
  rw [weight_Λ_over_𝒪_mk]
  exact weight_Λ_modByMonic_H_tilde'_le hD hH p

/-- The set `S_β` from the statement of Lemma A.1 in Appendix A of [BCIKS20].
Note: Here `F[X][Y]` is `F[Z][T]`. -/
noncomputable def S_β {H : F[X][Y]} (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot (H_tilde' H) z, (π_z z root) β = 0}

omit [IsDomain F] in
/-- The rational substitution `π_z` can be computed on the canonical representative. -/
lemma π_z_eq_eval_canonicalRepOf𝒪 {H : F[X][Y]} (hH : 0 < H.natDegree)
    (z : F) (root : rationalRoot (H_tilde' H) z) (β : 𝒪 H) :
    (π_z z root) β = Polynomial.evalEvalRingHom z root.1 (canonicalRepOf𝒪 hH β) := by
  conv_lhs => rw [← mk_canonicalRepOf𝒪 hH β]
  rfl

end

section LemmaA1

variable {F : Type} [Field F]

theorem H_tilde_prime_coeff_natDegree_le_of_totalDegree {H : F[X][Y]} {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) {j : ℕ}
    (hj : j ∈ (H_tilde' H).support) :
  j * (D + 1 - Bivariate.natDegreeY H) +
    ((H_tilde' H).coeff j).natDegree ≤
      H.natDegree * (D + 1 - Bivariate.natDegreeY H) := by
  exact (weight_Λ_le_iff.mp (weight_Λ_H_tilde'_le hD hH)) j hj

theorem canonicalRep_coeff_natDegree_le_of_weight_bound {H : F[X][Y]} (hH : 0 < H.natDegree) {D B : ℕ} (β : 𝒪 H)
    (hβw : weight_Λ_over_𝒪 hH β D ≤ (WithBot.some B : WithBot ℕ))
    {i : ℕ} (hi : i ∈ (canonicalRepOf𝒪 hH β).support) :
  i * (D + 1 - Bivariate.natDegreeY H) +
    ((canonicalRepOf𝒪 hH β).coeff i).natDegree ≤ B := by
  unfold weight_Λ_over_𝒪 at hβw
  exact (weight_Λ_le_iff.mp hβw) i hi

theorem embedding_eq_zero_of_resultant_zero {H : F[X][Y]} [Fact (Irreducible H)] (hH : 0 < H.natDegree) (β : 𝒪 H)
    (hres : Polynomial.resultant (canonicalRepOf𝒪 hH β) (H_tilde' H) = 0) :
  embeddingOf𝒪Into𝕃 H β = 0 := by
  classical
  let p : F[X][Y] := canonicalRepOf𝒪 hH β
  have hres_map : Polynomial.resultant (p.map (univPolyHom (F := F))) (H_tilde H) = 0 := by
    have h := congrArg (univPolyHom (F := F)) hres
    rw [← Polynomial.resultant_map_map (p) (H_tilde' H) p.natDegree (H_tilde' H).natDegree (univPolyHom (F := F))] at h
    rw [map_H_tilde'_eq_H_tilde H] at h
    have hn : (H_tilde H).natDegree = (H_tilde' H).natDegree := by
      rw [← map_H_tilde'_eq_H_tilde H]
      exact Polynomial.natDegree_map_eq_of_injective (univPolyHom_injective (F := F)) (H_tilde' H)
    simpa only [p, Polynomial.natDegree_map_eq_of_injective (univPolyHom_injective (F := F)), map_zero, hn] using h
  have hnot_coprime : ¬ IsCoprime (p.map (univPolyHom (F := F))) (H_tilde H) := by
    exact (Polynomial.resultant_eq_zero_iff.mp hres_map).2
  have hHT_irred : Irreducible (H_tilde H) :=
    irreducibleHTildeOfIrreducible_of_natDegree_pos hH (Fact.out)
  have hdvd_map : H_tilde H ∣ p.map (univPolyHom (F := F)) := by
    exact (Irreducible.dvd_iff_not_isCoprime hHT_irred).2 (by
      intro hc
      exact hnot_coprime hc.symm)
  have hdvd : H_tilde' H ∣ p := H_tilde'_dvd_of_map_dvd_H_tilde hH hdvd_map
  have hp_zero : p = 0 := by
    by_contra hp_ne
    have hdegp : p.natDegree < (H_tilde' H).natDegree := by
      simpa only [p, natDegree_H_tilde' hH] using canonicalRepOf𝒪_natDegree_lt_H hH β
    exact (Polynomial.not_dvd_of_natDegree_lt (p := H_tilde' H) (q := p) hp_ne hdegp) hdvd
  rw [← mk_canonicalRepOf𝒪 hH β]
  change embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) = 0
  rw [hp_zero]
  simp

theorem natDegree_det_le_of_perm_products_le {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F[X]) {N : ℕ}
    (h : ∀ σ : Equiv.Perm ι, (∏ i : ι, M (σ i) i).natDegree ≤ N) :
  M.det.natDegree ≤ N := by
  classical
  rw [Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  exact le_trans (Polynomial.natDegree_C_mul_le ((Equiv.Perm.sign σ : ℤ) : F) (∏ i : ι, M (σ i) i)) (h σ)

theorem natDegree_resultant_le_weight_bound {H : F[X][Y]} (hH : 0 < H.natDegree) {D B : ℕ}
    (hD : Bivariate.totalDegree H ≤ D) (β : 𝒪 H)
    (hβw : weight_Λ_over_𝒪 hH β D ≤ (WithBot.some B : WithBot ℕ)) :
  (Polynomial.resultant (canonicalRepOf𝒪 hH β) (H_tilde' H)).natDegree ≤ B * H.natDegree := by
  classical
  set p : F[X][Y] := canonicalRepOf𝒪 hH β
  set q : F[X][Y] := H_tilde' H
  set e : ℕ := p.natDegree
  set d : ℕ := H.natDegree
  set lam : ℕ := D + 1 - Bivariate.natDegreeY H
  have hqdeg : q.natDegree = d := by
    simpa [q, d] using natDegree_H_tilde' (H := H) hH
  let M : Matrix (Fin (e + d)) (Fin (e + d)) F[X] := Polynomial.sylvester p q e d
  rw [Polynomial.resultant]
  rw [hqdeg]
  change M.det.natDegree ≤ B * H.natDegree
  rw [show H.natDegree = d by rfl]
  apply natDegree_det_le_of_perm_products_le (M := M)
  intro σ
  by_cases hzero : ∃ i : Fin (e + d), M (σ i) i = 0
  · rcases hzero with ⟨i, hi⟩
    have hprod : (∏ i : Fin (e + d), M (σ i) i) = 0 := by
      exact Finset.prod_eq_zero (s := Finset.univ) (by simp) hi
    rw [hprod]
    simp
  · have hne (i : Fin (e + d)) : M (σ i) i ≠ 0 := by
      intro hi
      exact hzero ⟨i, hi⟩
    let lidx : Fin e → ℕ := fun j => ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ)
    let ridx : Fin d → ℕ := fun j => ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ)
    let ldeg : Fin e → ℕ := fun j => (M (σ (Fin.castAdd d j)) (Fin.castAdd d j)).natDegree
    let rdeg : Fin d → ℕ := fun j => (M (σ (Fin.natAdd e j)) (Fin.natAdd e j)).natDegree
    have hleft_Icc (j : Fin e) :
        ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + d) := by
      have hentry : M (σ (Fin.castAdd d j)) (Fin.castAdd d j) =
          if ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + d) then
            q.coeff (((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ))
          else 0 := by
        simp [M, Polynomial.sylvester]
      by_contra hc
      have hentry_zero : M (σ (Fin.castAdd d j)) (Fin.castAdd d j) = 0 := by
        simpa [hentry, hc]
      exact hne (Fin.castAdd d j) hentry_zero
    have hright_Icc (j : Fin d) :
        ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + e) := by
      have hentry : M (σ (Fin.natAdd e j)) (Fin.natAdd e j) =
          if ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + e) then
            p.coeff (((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ))
          else 0 := by
        simp [M, Polynomial.sylvester]
      by_contra hc
      have hentry_zero : M (σ (Fin.natAdd e j)) (Fin.natAdd e j) = 0 := by
        simpa [hentry, hc]
      exact hne (Fin.natAdd e j) hentry_zero
    have hleft (j : Fin e) : lidx j * lam + ldeg j ≤ d * lam := by
      dsimp [lidx, ldeg]
      have hentry : M (σ (Fin.castAdd d j)) (Fin.castAdd d j) =
          if ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + d) then
            q.coeff (((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ))
          else 0 := by
        simp [M, Polynomial.sylvester]
      have hc := hleft_Icc j
      have hcoeff_ne : q.coeff (((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ)) ≠ 0 := by
        have hne' := hne (Fin.castAdd d j)
        rwa [hentry, if_pos hc] at hne'
      have hsup : (((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ)) ∈ q.support :=
        Polynomial.mem_support_iff.mpr hcoeff_ne
      have hbound := H_tilde_prime_coeff_natDegree_le_of_totalDegree (F := F) (H := H) (D := D) hD hH (j := (((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) - (j : ℕ))) (by simpa [q] using hsup)
      simpa [q, d, lam, hentry, hc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hbound
    have hright (j : Fin d) : ridx j * lam + rdeg j ≤ B := by
      dsimp [ridx, rdeg]
      have hentry : M (σ (Fin.natAdd e j)) (Fin.natAdd e j) =
          if ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + e) then
            p.coeff (((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ))
          else 0 := by
        simp [M, Polynomial.sylvester]
      have hc := hright_Icc j
      have hcoeff_ne : p.coeff (((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ)) ≠ 0 := by
        have hne' := hne (Fin.natAdd e j)
        rwa [hentry, if_pos hc] at hne'
      have hsup : (((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ)) ∈ p.support :=
        Polynomial.mem_support_iff.mpr hcoeff_ne
      have hbound := canonicalRep_coeff_natDegree_le_of_weight_bound (F := F) (H := H) hH β hβw (i := (((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) - (j : ℕ))) (by simpa [p] using hsup)
      simpa [p, lam, hentry, hc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hbound
    have hleft_sum : (∑ j : Fin e, (lidx j * lam + ldeg j)) ≤ e * (d * lam) := by
      calc
        (∑ j : Fin e, (lidx j * lam + ldeg j)) ≤ ∑ j : Fin e, d * lam := by
          exact Finset.sum_le_sum (by intro j _; exact hleft j)
        _ = e * (d * lam) := by simp
    have hright_sum : (∑ j : Fin d, (ridx j * lam + rdeg j)) ≤ d * B := by
      calc
        (∑ j : Fin d, (ridx j * lam + rdeg j)) ≤ ∑ j : Fin d, B := by
          exact Finset.sum_le_sum (by intro j _; exact hright j)
        _ = d * B := by simp
    have hidxsum : (∑ j : Fin e, lidx j) + (∑ j : Fin d, ridx j) = d * e := by
      have hleft_row (j : Fin e) :
          ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ) = (j : ℕ) + lidx j := by
        dsimp [lidx]
        have hle := (Set.mem_Icc.mp (hleft_Icc j)).1
        omega
      have hright_row (j : Fin d) :
          ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ) = (j : ℕ) + ridx j := by
        dsimp [ridx]
        have hle := (Set.mem_Icc.mp (hright_Icc j)).1
        omega
      have hsum_left_rows :
          (∑ j : Fin e, ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ)) =
            (∑ j : Fin e, (j : ℕ)) + (∑ j : Fin e, lidx j) := by
        calc
          (∑ j : Fin e, ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ)) =
              (∑ j : Fin e, ((j : ℕ) + lidx j)) := by
                refine Finset.sum_congr rfl ?_
                intro j _
                exact hleft_row j
          _ = (∑ j : Fin e, (j : ℕ)) + (∑ j : Fin e, lidx j) := by
                rw [Finset.sum_add_distrib]
      have hsum_right_rows :
          (∑ j : Fin d, ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ)) =
            (∑ j : Fin d, (j : ℕ)) + (∑ j : Fin d, ridx j) := by
        calc
          (∑ j : Fin d, ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ)) =
              (∑ j : Fin d, ((j : ℕ) + ridx j)) := by
                refine Finset.sum_congr rfl ?_
                intro j _
                exact hright_row j
          _ = (∑ j : Fin d, (j : ℕ)) + (∑ j : Fin d, ridx j) := by
                rw [Finset.sum_add_distrib]
      have hperm_sum : (∑ i : Fin (e + d), ((σ i : Fin (e + d)) : ℕ)) = ∑ i : Fin (e + d), (i : ℕ) := by
        simpa using (Equiv.sum_comp σ (fun i : Fin (e + d) => (i : ℕ)))
      have hrows_split : (∑ i : Fin (e + d), ((σ i : Fin (e + d)) : ℕ)) =
          (∑ j : Fin e, ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ)) +
          (∑ j : Fin d, ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ)) := by
        simpa using (Fin.sum_univ_add (fun i : Fin (e + d) => ((σ i : Fin (e + d)) : ℕ)))
      have hcols_split : (∑ i : Fin (e + d), (i : ℕ)) =
          (∑ j : Fin e, (j : ℕ)) + (∑ j : Fin d, (e + (j : ℕ))) := by
        simpa using (Fin.sum_univ_add (fun i : Fin (e + d) => (i : ℕ)))
      have hright_cols : (∑ j : Fin d, (e + (j : ℕ))) = d * e + ∑ j : Fin d, (j : ℕ) := by
        simp [Finset.sum_add_distrib, Finset.sum_const, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have hmain :
          (∑ j : Fin e, ((σ (Fin.castAdd d j) : Fin (e + d)) : ℕ)) +
          (∑ j : Fin d, ((σ (Fin.natAdd e j) : Fin (e + d)) : ℕ)) =
          (∑ j : Fin e, (j : ℕ)) + (d * e + ∑ j : Fin d, (j : ℕ)) := by
        rw [← hrows_split, hperm_sum, hcols_split, hright_cols]
      omega
    have hweighted :
        ((∑ j : Fin e, lidx j) + (∑ j : Fin d, ridx j)) * lam +
          ((∑ j : Fin e, ldeg j) + (∑ j : Fin d, rdeg j)) ≤ e * (d * lam) + d * B := by
      have h := Nat.add_le_add hleft_sum hright_sum
      have hleft_expand : (∑ j : Fin e, (lidx j * lam + ldeg j)) = (∑ j : Fin e, lidx j) * lam + ∑ j : Fin e, ldeg j := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.sum_mul]
      have hright_expand : (∑ j : Fin d, (ridx j * lam + rdeg j)) = (∑ j : Fin d, ridx j) * lam + ∑ j : Fin d, rdeg j := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.sum_mul]
      rw [hleft_expand, hright_expand] at h
      nlinarith [h]
    have hdeg_parts : (∑ j : Fin e, ldeg j) + (∑ j : Fin d, rdeg j) ≤ d * B := by
      rw [hidxsum] at hweighted
      have hrew : e * (d * lam) = (d * e) * lam := by ring
      rw [hrew] at hweighted
      omega
    have hsum_deg_split :
        (∑ i : Fin (e + d), (M (σ i) i).natDegree) =
          (∑ j : Fin e, ldeg j) + (∑ j : Fin d, rdeg j) := by
      simpa only [ldeg, rdeg] using (Fin.sum_univ_add (fun i : Fin (e + d) => (M (σ i) i).natDegree))
    calc
      (∏ i : Fin (e + d), M (σ i) i).natDegree ≤
          ∑ i : Fin (e + d), (M (σ i) i).natDegree := by
            simpa using (Polynomial.natDegree_prod_le (s := Finset.univ) (f := fun i : Fin (e + d) => M (σ i) i))
      _ = (∑ j : Fin e, ldeg j) + (∑ j : Fin d, rdeg j) := hsum_deg_split
      _ ≤ B * d := by simpa [Nat.mul_comm] using hdeg_parts

theorem poly_eq_zero_of_ncard_gt_bound_of_subset_roots {p : F[X]} {S : Set F} {N : ℕ}
    (hS : S ⊆ {z | p.eval z = 0})
    (hdeg : p.natDegree ≤ N)
    (hcard : Set.ncard S > N) :
  p = 0 := by
  by_contra hp
  have hsubset : S ⊆ p.rootSet F := by
    intro z hz
    have hzroot : p.eval z = 0 := hS hz
    exact (Polynomial.mem_rootSet_of_ne hp).2 (by simpa using hzroot)
  have hncard : Set.ncard S ≤ Set.ncard (p.rootSet F) := by
    exact Set.ncard_le_ncard hsubset
  have hrootcard : Set.ncard (p.rootSet F) ≤ p.natDegree := Polynomial.ncard_rootSet_le p F
  omega

theorem resultant_eval_eq_resultant_map_eval_fixed_degrees (p q : F[X][Y]) (z : F) :
  (Polynomial.resultant p q).eval z =
    Polynomial.resultant (p.map (Polynomial.evalRingHom z))
      (q.map (Polynomial.evalRingHom z)) p.natDegree q.natDegree := by
  exact (Polynomial.resultant_map_map p q p.natDegree q.natDegree (Polynomial.evalRingHom z)).symm

theorem resultant_fixed_degree_eq_zero_of_common_root_of_monic_right {p q : F[X]} {m n : ℕ} {t : F}
    (hm : p.natDegree ≤ m) (hqmonic : q.Monic) (hn : q.natDegree = n)
    (hp : p.eval t = 0) (hq : q.eval t = 0) :
  Polynomial.resultant p q m n = 0 := by
  have hres0 : Polynomial.resultant p q = 0 := by
    rw [Polynomial.resultant_eq_zero_iff]
    constructor
    · exact Or.inr hqmonic.ne_zero
    · intro hcop
      rcases hcop with ⟨a, b, hab⟩
      have h_eval := congrArg (fun r : F[X] => r.eval t) hab
      simp [eval_add, eval_mul, hp, hq] at h_eval
  have hdeg : p.natDegree + (m - p.natDegree) = m := Nat.add_sub_of_le hm
  rw [← hdeg]
  rw [← hn]
  rw [Polynomial.resultant_add_left_deg]
  · simp [hres0]
  · exact le_rfl

theorem Sbeta_subset_resultant_roots {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) :
  S_β β ⊆
    {z | (Polynomial.resultant (canonicalRepOf𝒪 hH β) (H_tilde' H)).eval z = 0} := by
  intro z hz
  rcases hz with ⟨root, hβ⟩
  let p : F[X][Y] := canonicalRepOf𝒪 hH β
  let q : F[X][Y] := H_tilde' H
  have hp : (p.map (Polynomial.evalRingHom z)).eval root.1 = 0 := by
    have h := π_z_eq_eval_canonicalRepOf𝒪 hH z root β
    rw [h] at hβ
    rw [Polynomial.map_evalRingHom_eval]
    simpa [p, Polynomial.coe_evalEvalRingHom] using hβ
  have hq : (q.map (Polynomial.evalRingHom z)).eval root.1 = 0 := by
    rw [Polynomial.map_evalRingHom_eval]
    exact root.2
  have hqmonic : (q.map (Polynomial.evalRingHom z)).Monic := by
    exact (H_tilde'_monic H hH).map (Polynomial.evalRingHom z)
  have hn : (q.map (Polynomial.evalRingHom z)).natDegree = q.natDegree := by
    exact (H_tilde'_monic H hH).natDegree_map (Polynomial.evalRingHom z)
  have hres : Polynomial.resultant (p.map (Polynomial.evalRingHom z)) (q.map (Polynomial.evalRingHom z)) p.natDegree q.natDegree = 0 := by
    exact resultant_fixed_degree_eq_zero_of_common_root_of_monic_right
      (Polynomial.natDegree_map_le (f := Polynomial.evalRingHom z) (p := p)) hqmonic hn hp hq
  change (Polynomial.resultant p q).eval z = 0
  rw [resultant_eval_eq_resultant_map_eval_fixed_degrees]
  exact hres

theorem weight_bot_embedding_zero {H : F[X][Y]} (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ)
    (hw : weight_Λ_over_𝒪 hH β D = ⊥) :
  embeddingOf𝒪Into𝕃 H β = 0 := by
  classical
  let p : F[X][Y] := canonicalRepOf𝒪 hH β
  have hp : p = 0 := by
    by_contra hp_ne
    have hsup : p.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      exact hp_ne (Polynomial.support_eq_empty.mp h_empty)
    rcases hsup with ⟨n, hn⟩
    have hle : (WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (p.coeff n).natDegree) : WithBot ℕ) ≤ weight_Λ p H D :=
      le_weight_Λ_of_mem_support hn
    have hle_bot : (WithBot.some (n * (D + 1 - Bivariate.natDegreeY H) + (p.coeff n).natDegree) : WithBot ℕ) ≤ (⊥ : WithBot ℕ) := by
      exact hle.trans (by simpa [p, weight_Λ_over_𝒪] using le_of_eq hw)
    exact (not_le_of_gt (WithBot.bot_lt_coe _)) hle_bot
  rw [← mk_canonicalRepOf𝒪 hH β]
  change embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) = 0
  rw [hp]
  simp


/-- The statement of Lemma A.1 in Appendix A.3 of [BCIKS20]. -/
lemma lemmaA1_embedding_eq_zero_of_many_rational_roots {H : F[X][Y]}
    [hHirreducible : Fact (Irreducible H)]
    (hH : 0 < H.natDegree) (β : 𝒪 H) (D : ℕ)
    (hD : D ≥ Bivariate.totalDegree H)
    (S_β_card : Set.ncard (S_β β) > (weight_Λ_over_𝒪 hH β D) * H.natDegree) :
  embeddingOf𝒪Into𝕃 _ β = 0 := by
  classical
  set R : F[X] := Polynomial.resultant (canonicalRepOf𝒪 hH β) (H_tilde' H)
  cases hweight : weight_Λ_over_𝒪 hH β D with
  | bot =>
      exact weight_bot_embedding_zero hH β D hweight
  | coe B =>
      have hβw : weight_Λ_over_𝒪 hH β D ≤ (WithBot.some B : WithBot ℕ) := by
        rw [hweight]
      have hdeg : R.natDegree ≤ B * H.natDegree := by
        dsimp [R]
        exact natDegree_resultant_le_weight_bound hH hD β hβw
      have hcard : Set.ncard (S_β β) > B * H.natDegree := by
        rw [hweight] at S_β_card
        change ((B * H.natDegree : ℕ) : WithBot ℕ) < ((Set.ncard (S_β β) : ℕ) : WithBot ℕ) at S_β_card
        exact WithBot.coe_lt_coe.mp S_β_card
      have hRzero : R = 0 := by
        apply poly_eq_zero_of_ncard_gt_bound_of_subset_roots
        · dsimp [R]
          exact Sbeta_subset_resultant_roots hH β
        · exact hdeg
        · exact hcard
      apply embedding_eq_zero_of_resultant_zero hH β
      dsimp [R] at hRzero
      exact hRzero

end LemmaA1

section

variable {F : Type} [CommRing F] [IsDomain F]

/-- The embedding of the coefficients of a bivariate polynomial into the bivariate polynomial ring
with rational coefficients. -/
noncomputable def coeffAsRatFunc : F[X] →+* Polynomial (RatFunc F) :=
  RingHom.comp bivPolyHom Polynomial.C

/-- The embedding of coefficient polynomials into the function field `𝕃`. -/
noncomputable def liftToFunctionField {H : F[X][Y]} : F[X] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) coeffAsRatFunc

/-- The embedding of bivariate polynomials into the function field `𝕃`. -/
noncomputable def liftBivariate {H : F[X][Y]} : F[X][Y] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) bivPolyHom

/-- The image of the polynomial variable `T` in the function field `𝕃 H`. -/
noncomputable def functionFieldT {H : F[X][Y]} : 𝕃 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde H}) Polynomial.X

/-- Quotient constructors in `𝒪` embed by applying the bivariate lift. -/
@[simp]
lemma embeddingOf𝒪Into𝕃_mk (H : F[X][Y]) (p : F[X][Y]) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p : 𝒪 H) =
      liftBivariate (H := H) p := by
  rfl

/-- Every bivariate polynomial representative gives a regular element of the function field. -/
lemma regular_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    ∃ pre : 𝒪 H, embeddingOf𝒪Into𝕃 H pre = liftBivariate (H := H) p :=
  ⟨Ideal.Quotient.mk (Ideal.span {H_tilde' H}) p, by simp⟩

/-- Bivariate-polynomial images are regular elements of the function field. -/
lemma regularElementsSet_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    liftBivariate (H := H) p ∈ regularElementsSet H := by
  rcases regular_liftBivariate H p with ⟨pre, hpre⟩
  exact ⟨pre, hpre.symm⟩

/-- Coefficients embedded into `𝕃` are regular elements. -/
lemma regular_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    ∃ pre : 𝒪 H, embeddingOf𝒪Into𝕃 H pre = liftToFunctionField (H := H) p :=
  regular_liftBivariate H (Polynomial.C p)

/-- Coefficient-polynomial images are regular elements of the function field. -/
lemma regularElementsSet_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    liftToFunctionField (H := H) p ∈ regularElementsSet H := by
  simpa using regularElementsSet_liftBivariate H (Polynomial.C p)

/-- Nonzero coefficient polynomials remain nonzero after embedding into the function field. -/
lemma liftToFunctionField_ne_zero {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p : F[X]} (hp : p ≠ 0) :
    liftToFunctionField (H := H) p ≠ 0 := by
  intro hzero
  have hmem : coeffAsRatFunc p ∈ Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F))) := by
    simpa [liftToFunctionField] using (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  rw [Ideal.mem_span_singleton] at hmem
  have hp_map : univPolyHom (F := F) p ≠ 0 := by
    intro hp_zero
    exact hp (univPolyHom_injective (F := F) (by simpa using hp_zero))
  have hunit : IsUnit (coeffAsRatFunc p) := by
    have hunitC : IsUnit (Polynomial.C (univPolyHom (F := F) p) :
        Polynomial (RatFunc F)) :=
      Polynomial.isUnit_C.mpr (Ne.isUnit hp_map)
    simpa only [coeffAsRatFunc, RingHom.comp_apply, ToRatFunc.bivPolyHom,
      Polynomial.coe_mapRingHom, Polynomial.map_C] using hunitC
  exact (irreducibleHTildeOfIrreducible_of_natDegree_pos H_natDegree_pos.out
    H_irreducible.out).not_dvd_isUnit hunit hmem

/-- The leading coefficient `W` of a positive-`Y`-degree `H` is nonzero in the function field. -/
lemma liftToFunctionField_leadingCoeff_ne_zero {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)] :
    liftToFunctionField (H := H) H.leadingCoeff ≠ 0 := by
  exact liftToFunctionField_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out))

/-- If `q ∣ p` in `F[X]`, then `p / q` is regular after embedding into `𝕃`. -/
lemma regularElementsSet_liftToFunctionField_div_of_dvd {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p q : F[X]} (hq : q ≠ 0) (hdiv : q ∣ p) :
    liftToFunctionField (H := H) p / liftToFunctionField (H := H) q ∈ regularElementsSet H := by
  rcases hdiv with ⟨r, rfl⟩
  have hq_lift : liftToFunctionField (H := H) q ≠ 0 := liftToFunctionField_ne_zero hq
  have heq :
      liftToFunctionField (H := H) (q * r) / liftToFunctionField (H := H) q =
        liftToFunctionField (H := H) r := by
    rw [map_mul]
    field_simp [hq_lift]
  rw [heq]
  exact regularElementsSet_liftToFunctionField H r

/-- If `W = H.leadingCoeff` divides `p`, then `p / W` is regular after embedding into `𝕃`. -/
lemma regularElementsSet_liftToFunctionField_div_leadingCoeff_of_dvd {F : Type} [Field F]
    {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] {p : F[X]}
    (hdiv : H.leadingCoeff ∣ p) :
    liftToFunctionField (H := H) p / liftToFunctionField (H := H) H.leadingCoeff ∈
      regularElementsSet H := by
  exact regularElementsSet_liftToFunctionField_div_of_dvd
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out))
    hdiv

private lemma mul_pow_mul_div_pow_eq_lower {K : Type} [Field K] {W T a : K}
    (hW : W ≠ 0) {k i : ℕ} (hi : i ≤ k) :
    W ^ k * (a * (T / W) ^ i) = a * (T ^ i * W ^ (k - i)) := by
  rw [div_pow]
  have hk : k = k - i + i := (Nat.sub_add_cancel hi).symm
  calc
    W ^ k * (a * (T ^ i / W ^ i)) = a * (T ^ i * (W ^ k / W ^ i)) := by
      ring
    _ = a * (T ^ i * W ^ (k - i)) := by
      rw [hk, pow_add]
      field_simp [hW]
      have hsub : k - i + i - i = k - i := by omega
      rw [hsub]

private lemma mul_pow_mul_div_pow_succ_eq_top {K : Type} [Field K] {W T a : K}
    (hW : W ≠ 0) (k : ℕ) :
    W ^ k * (a * (T / W) ^ (k + 1)) = (a / W) * T ^ (k + 1) := by
  rw [div_pow, pow_succ]
  field_simp [hW]
  ring

/-- Clearing denominators in `W^k · P(T/W)` as an explicit sum: if `P.natDegree ≤ k + 1`, then
`W^k * eval₂ lift (T/W) P` decomposes into a low-degree polynomial sum plus a single
`(P.coeff(k+1)/W) · T^(k+1)` term. The divisibility `W ∣ P.coeff(k+1)` is not needed here -
the formula holds in `𝕃 H` directly via field division. -/
lemma W_pow_mul_eval₂_div_eq_sum {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} {k : ℕ} (hP : P.natDegree ≤ k + 1) :
    liftToFunctionField (H := H) H.leadingCoeff ^ k *
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P =
      (∑ i ∈ Finset.range (k + 1),
          liftToFunctionField (H := H) (P.coeff i) *
            (functionFieldT (H := H) ^ i *
              liftToFunctionField (H := H) H.leadingCoeff ^ (k - i))) +
        (liftToFunctionField (H := H) (P.coeff (k + 1)) /
            liftToFunctionField (H := H) H.leadingCoeff) *
          functionFieldT (H := H) ^ (k + 1) := by
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hW_def
  set T : 𝕃 H := functionFieldT (H := H) with hT_def
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have hP_lt : P.natDegree < k + 2 := by omega
  rw [Polynomial.eval₂_eq_sum_range' liftToFunctionField hP_lt (T / W)]
  rw [Finset.mul_sum]
  rw [show k + 2 = k + 1 + 1 by omega, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi_le : i ≤ k := by
      have hi_lt := Finset.mem_range.mp hi
      omega
    exact mul_pow_mul_div_pow_eq_lower (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff i)) hW hi_le
  · exact mul_pow_mul_div_pow_succ_eq_top (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff (k + 1))) hW k

/-- The bivariate variable maps to the function-field variable `T`. -/
@[simp]
lemma liftBivariate_X {H : F[X][Y]} :
    liftBivariate (H := H) (Polynomial.X : F[X][Y]) = functionFieldT (H := H) := by
  simp [liftBivariate, functionFieldT, bivPolyHom]

/-- The function-field variable `T` is regular. -/
lemma regularElementsSet_functionFieldT (H : F[X][Y]) :
    functionFieldT (H := H) ∈ regularElementsSet H := by
  simpa using regularElementsSet_liftBivariate H (Polynomial.X : F[X][Y])

/-- A linear polynomial evaluated at `T / W` is regular when its linear coefficient is divisible by
`W = H.leadingCoeff`. -/
lemma regularElementsSet_eval₂_linear_of_coeff_one_dvd {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} (hP : P.natDegree ≤ 1) (hdiv : H.leadingCoeff ∣ P.coeff 1) :
    Polynomial.eval₂ liftToFunctionField
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P ∈
      regularElementsSet H := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hP]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  have hterm :
      liftToFunctionField (H := H) (P.coeff 1) *
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) =
        (liftToFunctionField (H := H) (P.coeff 1) /
            liftToFunctionField (H := H) H.leadingCoeff) * functionFieldT (H := H) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hterm]
  exact regularElementsSet_add
    (regularElementsSet_mul
      (regularElementsSet_liftToFunctionField_div_leadingCoeff_of_dvd hdiv)
      (regularElementsSet_functionFieldT H))
    (regularElementsSet_liftToFunctionField H (P.coeff 0))

/-- Clearing denominators in `P(T / W)`: if `P` has degree at most `k + 1` and its top
coefficient is divisible by `W = H.leadingCoeff`, then `W^k * P(T/W)` is regular. -/
lemma regularElementsSet_mul_pow_eval₂_div_of_natDegree_le_succ_of_coeff_succ_dvd
    {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} {k : ℕ} (hP : P.natDegree ≤ k + 1)
    (hdiv : H.leadingCoeff ∣ P.coeff (k + 1)) :
    liftToFunctionField (H := H) H.leadingCoeff ^ k *
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P ∈
      regularElementsSet H := by
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let T : 𝕃 H := functionFieldT (H := H)
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have hP_lt : P.natDegree < k + 2 := by omega
  change W ^ k * Polynomial.eval₂ liftToFunctionField (T / W) P ∈ regularElementsSet H
  rw [Polynomial.eval₂_eq_sum_range' liftToFunctionField hP_lt (T / W)]
  rw [Finset.mul_sum]
  rw [show k + 2 = k + 1 + 1 by omega, Finset.sum_range_succ]
  refine regularElementsSet_add ?_ ?_
  · refine regularElementsSet_sum (Finset.range (k + 1)) ?_
    intro i hi
    have hi_lt : i < k + 1 := Finset.mem_range.mp hi
    have hi_le : i ≤ k := by omega
    rw [mul_pow_mul_div_pow_eq_lower (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff i)) hW hi_le]
    exact regularElementsSet_mul
      (regularElementsSet_liftToFunctionField H (P.coeff i))
      (regularElementsSet_mul
        (by simpa [T] using regularElementsSet_pow (regularElementsSet_functionFieldT H) i)
        (by
          simpa [W] using
            regularElementsSet_pow
              (regularElementsSet_liftToFunctionField H H.leadingCoeff) (k - i)))
  · rw [mul_pow_mul_div_pow_succ_eq_top (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff (k + 1))) hW k]
    exact regularElementsSet_mul
      (by
        simpa [W] using
          regularElementsSet_liftToFunctionField_div_leadingCoeff_of_dvd (H := H) hdiv)
      (by simpa [T] using regularElementsSet_pow (regularElementsSet_functionFieldT H) (k + 1))

/-- Constant bivariate polynomials map through the coefficient embedding. -/
@[simp]
lemma liftBivariate_C {H : F[X][Y]} (p : F[X]) :
    liftBivariate (H := H) (Polynomial.C p : F[X][Y]) = liftToFunctionField (H := H) p := by
  rfl

/-- The embedding of scalars into the function field `𝕃`. -/
noncomputable def fieldTo𝕃 {H : F[X][Y]} : F →+* 𝕃 H :=
  RingHom.comp liftToFunctionField Polynomial.C

/-- View a bivariate polynomial as a power series over `𝕃 H` by lifting its coefficients. -/
noncomputable def polyToPowerSeries𝕃 (H : F[X][Y]) (P : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk <| fun n => liftToFunctionField (P.coeff n)


end

noncomputable section

namespace ClaimA2

variable {F : Type} [Field F] {R : F[X][X][X]} {H : F[X][Y]}
  [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]

/-! ### Claim A.2 hypotheses and derivative setup -/

/-- The algebraic hypotheses for Claim A.2 from Appendix A.4 of [BCIKS20], after specializing
`R` at `X = x₀`. -/
structure Hypotheses (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : Prop where
  dvd_evalX : H ∣ Bivariate.evalX (Polynomial.C x₀) R
  separable_evalX : (Bivariate.evalX (Polynomial.C x₀) R).Separable

private lemma evalX_natDegree_le {K : Type} [CommSemiring K] (x : K) (P : K[X][Y]) :
    (Bivariate.evalX x P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hcoeff : P.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hn
  simp [Bivariate.evalX_eq_map, Polynomial.coeff_map, hcoeff]

lemma evalX_ne_zero_of_Hypotheses {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    Bivariate.evalX (Polynomial.C x₀) R ≠ 0 :=
  hHyp.separable_evalX.ne_zero

lemma H_natDegree_le_R_natDegree_of_Hypotheses {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.natDegree ≤ R.natDegree :=
  (Polynomial.natDegree_le_of_dvd hHyp.dvd_evalX (evalX_ne_zero_of_Hypotheses hHyp)).trans
    (evalX_natDegree_le (Polynomial.C x₀) R)

lemma derivative_evalX_coeff (x₀ : F) (R : F[X][X][Y]) (i : ℕ) :
    (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i =
      (Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1) * ((i + 1 : ℕ) : F[X]) := by
  have hsucc_cast : (((i : ℕ) : F[X][X]) + 1) = ((i + 1 : ℕ) : F[X][X]) := by
    rw [← Nat.cast_one (R := F[X][X]), ← Nat.cast_add]
  calc
    (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i =
        ((R.derivative).coeff i).eval (Polynomial.C x₀) := by
      simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
    _ = (R.coeff (i + 1) * ((i + 1 : ℕ) : F[X][X])).eval (Polynomial.C x₀) := by
      rw [Polynomial.coeff_derivative, hsucc_cast]
    _ = (Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1) * ((i + 1 : ℕ) : F[X]) := by
      simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]

lemma natDegree_derivative_evalX_coeff_le (x₀ : F) (R : F[X][X][Y]) {D i : ℕ}
    (hD : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D) :
    ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i).natDegree ≤ D - (i + 1) := by
  rw [derivative_evalX_coeff]
  calc
    (((Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1) * ((i + 1 : ℕ) : F[X])).natDegree)
        ≤ ((Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1)).natDegree +
            (((i + 1 : ℕ) : F[X]).natDegree) := Polynomial.natDegree_mul_le
    _ = ((Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1)).natDegree := by
        rw [← Polynomial.C_eq_natCast, Polynomial.natDegree_C, Nat.add_zero]
    _ ≤ D - (i + 1) :=
        natDegree_coeff_le_of_totalDegree_le (Bivariate.evalX (Polynomial.C x₀) R) hD (i + 1)

/-- The leading coefficient `W` of `H` divides the leading coefficient of `R(x₀,Y,Z)`. -/
lemma leadingCoeff_dvd_evalX_leadingCoeff {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff := by
  rcases hHyp.dvd_evalX with ⟨q, hq⟩
  refine ⟨q.leadingCoeff, ?_⟩
  calc
    (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff = (H * q).leadingCoeff := by rw [hq]
    _ = H.leadingCoeff * q.leadingCoeff := Polynomial.leadingCoeff_mul H q

/-- The leading coefficient `W` of `H` divides the coefficient of `Y ^ R.natDegree` in
`R(x₀,Y,Z)`. If specialization lowers the `Y`-degree, that coefficient is zero. -/
lemma leadingCoeff_dvd_evalX_coeff_natDegree {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R
  have hdeg : P.natDegree ≤ R.natDegree := evalX_natDegree_le (Polynomial.C x₀) R
  by_cases hEq : P.natDegree = R.natDegree
  · simpa [P, hEq.symm] using leadingCoeff_dvd_evalX_leadingCoeff hHyp
  · have hlt : P.natDegree < R.natDegree := lt_of_le_of_ne hdeg hEq
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    exact dvd_zero H.leadingCoeff

/-- The leading coefficient `W` of `H` divides the top possible coefficient of
`∂R/∂Y(x₀,Y,Z)`. This is the coefficient that remains after multiplying `ζ` by `W^(d-2)`. -/
lemma leadingCoeff_dvd_evalX_derivative_coeff_pred {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) := by
  by_cases hR : R.natDegree = 0
  · have hderiv : R.derivative = 0 := Polynomial.derivative_of_natDegree_zero hR
    rw [hderiv]
    exact ⟨0, by simp [Bivariate.evalX_eq_map]⟩
  · have hsucc : R.natDegree - 1 + 1 = R.natDegree :=
      Nat.sub_add_cancel (Nat.pos_of_ne_zero hR)
    have hsucc_cast : (((R.natDegree - 1 : ℕ) : F[X][X]) + 1) =
        (R.natDegree : F[X][X]) := by
      rw [← Nat.cast_one (R := F[X][X])]
      rw [← Nat.cast_add, hsucc]
    have hcoeff :
        (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
          (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree *
            (R.natDegree : F[X]) := by
      calc
        (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
            ((R.derivative).coeff (R.natDegree - 1)).eval (Polynomial.C x₀) := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
        _ = (R.coeff R.natDegree * (R.natDegree : F[X][X])).eval (Polynomial.C x₀) := by
          rw [Polynomial.coeff_derivative, hsucc, hsucc_cast]
        _ = (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree *
            (R.natDegree : F[X]) := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
    rcases leadingCoeff_dvd_evalX_coeff_natDegree hHyp with ⟨q, hq⟩
    refine ⟨q * (R.natDegree : F[X]), ?_⟩
    rw [hcoeff, hq]
    ring

/-- The element `ζ` from Appendix A.4 of [BCIKS20]. -/
def ζ (R : F[X][X][Y]) (x₀ : F) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  let T : 𝕃 H := functionFieldT (H := H)
  Polynomial.eval₂ liftToFunctionField (T / W)
    (Bivariate.evalX (Polynomial.C x₀) R.derivative)

/-- If the derivative specialization is constant in the function-field variable, then `ζ` is
regular. -/
lemma ζ_regular_of_derivative_evalX_eq_C (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)] {p : F[X]}
    (hp : Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p) :
    ζ R x₀ H ∈ regularElementsSet H := by
  rw [ζ, hp]
  simp only [Polynomial.eval₂_C]
  exact regularElementsSet_liftToFunctionField H p

/-- If `R` has `Y`-degree at most one, then the specialized derivative is constant. -/
lemma derivative_evalX_eq_C_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (hR : R.natDegree ≤ 1) :
    ∃ p : F[X], Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  refine ⟨P.coeff 0, ?_⟩
  have hderiv : R.derivative.natDegree ≤ 0 := by
    calc
      R.derivative.natDegree ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      _ = 0 := by omega
  have hP : P.natDegree ≤ 0 :=
    (evalX_natDegree_le (Polynomial.C x₀) R.derivative).trans hderiv
  exact Polynomial.eq_C_of_natDegree_le_zero hP

/-- In the constant-derivative, low-`Y`-degree case, the `ξ` regularity witness is explicit. -/
lemma ξ_regular_of_derivative_evalX_eq_C_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p : F[X]} (hp : Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p)
    (hR : R.natDegree ≤ 1) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  rcases ζ_regular_of_derivative_evalX_eq_C x₀ R H hp with ⟨pre, hpre⟩
  refine ⟨pre, ?_⟩
  have hd : R.natDegree - 2 = 0 := by omega
  simpa [hd] using hpre.symm

/-- If `R` has `Y`-degree at most one, the regularity statement for `ξ` follows from the
constant-derivative case. -/
lemma ξ_regular_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hR : R.natDegree ≤ 1) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  rcases derivative_evalX_eq_C_of_natDegree_le_one x₀ R hR with ⟨p, hp⟩
  exact ξ_regular_of_derivative_evalX_eq_C_of_natDegree_le_one x₀ R H hp hR

/-- In the quadratic case, `ξ = ζ` is regular by clearing the single denominator with the
divisibility of the top derivative coefficient. -/
lemma ξ_regular_of_natDegree_eq_two
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (hR : R.natDegree = 2) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  have hP : P.natDegree ≤ 1 := by
    calc
      P.natDegree ≤ R.derivative.natDegree := evalX_natDegree_le (Polynomial.C x₀) R.derivative
      _ ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      _ = 1 := by omega
  have hdiv : H.leadingCoeff ∣ P.coeff 1 := by
    simpa [P, hR] using leadingCoeff_dvd_evalX_derivative_coeff_pred hHyp
  have hreg : ζ R x₀ H ∈ regularElementsSet H := by
    simpa [ζ, P] using regularElementsSet_eval₂_linear_of_coeff_one_dvd (H := H) hP hdiv
  rcases hreg with ⟨pre, hpre⟩
  refine ⟨pre, ?_⟩
  have hd : R.natDegree - 2 = 0 := by omega
  simpa [hd] using hpre.symm

/-- Explicit polynomial representative for the regular element `ξ = W^(d-2) · ζ` of Claim A.2.
For `2 ≤ R.natDegree`, this is the polynomial obtained by clearing the single denominator that
appears in `W^(d-2) · ζ`; the divisibility `W ∣ R'(x₀, Z)_{d-1}` is captured implicitly by
Euclidean division in `F[X]`. For `R.natDegree ≤ 1`, the derivative specialization is constant
in `Y`, so we take it as the representative. -/
noncomputable def ξ_pre (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : F[X][Y] :=
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  let d : ℕ := R.natDegree
  let W : F[X] := H.leadingCoeff
  if 2 ≤ d then
    (∑ i ∈ Finset.range (d - 1),
        Polynomial.C (P.coeff i * W ^ (d - 2 - i)) * Polynomial.X ^ i) +
      Polynomial.C (P.coeff (d - 1) / W) * Polynomial.X ^ (d - 1)
  else
    P

/-- The image of `⟦ξ_pre⟧` in the function field equals `W^(d-2) · ζ`, matching Claim A.2's
algebraic identity. -/
lemma embeddingOf𝒪Into𝕃_mk_ξ_pre (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk _ (ξ_pre x₀ R H) : 𝒪 H) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2) * ζ R x₀ H := by
  rw [embeddingOf𝒪Into𝕃_mk]
  by_cases hRle : R.natDegree ≤ 1
  · -- d ≤ 1: ξ_pre = R'(x₀, Z), constant in Y; ζ is the lift of that constant.
    rcases derivative_evalX_eq_C_of_natDegree_le_one x₀ R hRle with ⟨p, hp⟩
    have hd2 : R.natDegree - 2 = 0 := by omega
    have hbranch : ¬ 2 ≤ R.natDegree := by omega
    have hξ_pre : ξ_pre x₀ R H = Polynomial.C p := by
      simp [ξ_pre, hbranch, hp]
    rw [hξ_pre, hd2, pow_zero, one_mul, liftBivariate_C]
    change liftToFunctionField (H := H) p =
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
        (Bivariate.evalX (Polynomial.C x₀) R.derivative)
    rw [hp, Polynomial.eval₂_C]
  · have hd2 : 2 ≤ R.natDegree := by omega
    set P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative with hP_def
    set W_poly : F[X] := H.leadingCoeff with hW_poly_def
    have hkk : R.natDegree - 1 = R.natDegree - 2 + 1 := by omega
    have hP_le : P.natDegree ≤ R.natDegree - 2 + 1 := by
      have h1 : P.natDegree ≤ R.derivative.natDegree := evalX_natDegree_le _ R.derivative
      have h2 : R.derivative.natDegree ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      omega
    have hdiv : W_poly ∣ P.coeff (R.natDegree - 2 + 1) := by
      have h := leadingCoeff_dvd_evalX_derivative_coeff_pred (H := H) hHyp
      rwa [hkk] at h
    have hW_poly_ne : W_poly ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr
        (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out)
    have hW_ne : (liftToFunctionField (H := H) W_poly : 𝕃 H) ≠ 0 :=
      liftToFunctionField_leadingCoeff_ne_zero (H := H)
    have hξ_pre_eq : ξ_pre x₀ R H =
        (∑ i ∈ Finset.range (R.natDegree - 2 + 1),
            Polynomial.C (P.coeff i * W_poly ^ (R.natDegree - 2 - i)) * Polynomial.X ^ i) +
          Polynomial.C (P.coeff (R.natDegree - 2 + 1) / W_poly) *
            Polynomial.X ^ (R.natDegree - 2 + 1) := by
      simp only [ξ_pre, hd2, ↓reduceIte, ← hP_def, ← hW_poly_def, hkk]
    rw [hξ_pre_eq]
    rw [show (ζ R x₀ H : 𝕃 H) =
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) W_poly) P from rfl]
    rw [W_pow_mul_eval₂_div_eq_sum (H := H) (P := P) (k := R.natDegree - 2) hP_le]
    have hlift_div :
        liftToFunctionField (H := H) (P.coeff (R.natDegree - 2 + 1) / W_poly) =
          liftToFunctionField (H := H) (P.coeff (R.natDegree - 2 + 1)) /
            liftToFunctionField (H := H) W_poly := by
      rw [eq_div_iff hW_ne, ← map_mul, mul_comm,
          EuclideanDomain.mul_div_cancel' hW_poly_ne hdiv]
    simp only [map_add, map_sum, map_mul, map_pow, liftBivariate_C, liftBivariate_X, hlift_div]
    refine congr_arg₂ (· + ·) ?_ rfl
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

/-- The regular element `ξ = W(Z)^(d-2) * ζ` has a quotient representative in the total Lean
form of Claim A.2 of Appendix A.4 of [BCIKS20].

For `R.natDegree < 2`, the natural-number exponent truncates to zero. The paper's weight
bound is therefore stated separately with the explicit hypothesis `2 ≤ R.natDegree`. -/
lemma ξ_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H :=
  ⟨Ideal.Quotient.mk _ (ξ_pre x₀ R H),
    by simpa using embeddingOf𝒪Into𝕃_mk_ξ_pre x₀ R H hHyp⟩

/-- The regular element `ξ = W(Z)^(d-2) * ζ` used in the Lean version of Claim A.2.

The `Fact` and `Hypotheses` arguments are kept for API compatibility with downstream callers
(`α`, `γ`); they are needed for the embedding equation in `embeddingOf𝒪Into𝕃_ξ`. -/
noncomputable def ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [_φ : Fact (Irreducible H)]
    [_H_natDegree_pos : Fact (0 < H.natDegree)] (_hHyp : Hypotheses x₀ R H) : 𝒪 H :=
  Ideal.Quotient.mk _ (ξ_pre x₀ R H)

/-- The defining equation `embedding ξ = W^(d-2) · ζ`, the specialization of
`embeddingOf𝒪Into𝕃_mk_ξ_pre` to `ξ`. -/
lemma embeddingOf𝒪Into𝕃_ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2) * ζ R x₀ H :=
  embeddingOf𝒪Into𝕃_mk_ξ_pre x₀ R H hHyp

theorem leadingCoeff_natDegree_le_of_totalDegree_le {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D) :
    H.leadingCoeff.natDegree ≤ D - H.natDegree := by
  exact natDegree_coeff_le_of_totalDegree_le H hD_H H.natDegree

theorem cofactor_top_reduction_weight_le {H : F[X][Y]} (hH : 0 < H.natDegree) {Q : F[X][Y]} {d D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_HQ : Bivariate.totalDegree (H * Q) ≤ D)
    (hd : H.natDegree < d)
    (hQdeg : Q.natDegree ≤ d - H.natDegree) :
    weight_Λ
      (Polynomial.C ((d : F[X]) * Q.coeff (d - H.natDegree)) *
          Polynomial.X ^ (d - 1) %ₘ H_tilde' H) H D ≤
      (WithBot.some ((d - 1) * (D - H.natDegree + 1)) : WithBot ℕ) := by
  classical
  by_cases hQzero : Q = 0
  · subst hQzero
    simp
  · let m : ℕ := H.natDegree
    let s : ℕ := d - m
    let W : F[X] := H.coeff m
    let c : F[X] := (d : F[X]) * Q.coeff s
    let lower : F[X][Y] := ∑ i ∈ Finset.range m,
      Polynomial.C (H.coeff i * W ^ (m - 1 - i)) * Polynomial.X ^ i
    let p : F[X][Y] := Polynomial.C c * Polynomial.X ^ (d - 1)
    have hm_pos : 0 < m := by dsimp [m]; exact hH
    have hs_pos : 0 < s := by
      dsimp [s, m]
      omega
    have hdm : d - 1 = (s - 1) + m := by
      dsimp [s, m]
      omega
    have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
    have hm_le_T : m ≤ Bivariate.totalDegree H := by
      have hHin : m ∈ H.support := by
        dsimp [m]
        exact Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
      have hcontrib : (H.coeff m).natDegree + m ≤ Bivariate.totalDegree H := by
        simpa [m] using Bivariate.coeff_totalDegree_le H hHin
      omega
    have hm_le_D : m ≤ D := le_trans hm_le_T hD_H
    have hTQ : Bivariate.totalDegree Q ≤ D - Bivariate.totalDegree H := by
      have hmul : Bivariate.totalDegree (H * Q) = Bivariate.totalDegree H + Bivariate.totalDegree Q := by
        simpa using Bivariate.totalDegree_mul (F := F) hH_ne hQzero
      omega
    have hQcoeff0 : (Q.coeff s).natDegree ≤ D - Bivariate.totalDegree H := by
      exact (natDegree_coeff_le_of_totalDegree_le Q hTQ s).trans (Nat.sub_le _ _)
    have hd_natDegree : ((d : F[X]).natDegree = 0) := by
      rw [← Polynomial.C_eq_natCast, Polynomial.natDegree_C]
    have hcdeg : c.natDegree ≤ D - Bivariate.totalDegree H := by
      dsimp [c]
      calc
        ((d : F[X]) * Q.coeff s).natDegree ≤ ((d : F[X]).natDegree + (Q.coeff s).natDegree) := Polynomial.natDegree_mul_le
        _ ≤ 0 + (D - Bivariate.totalDegree H) := by
          rw [hd_natDegree]
          omega
        _ = D - Bivariate.totalDegree H := by omega
    have htilde : H_tilde' H = Polynomial.X ^ m + lower := by
      dsimp [lower, W, m]
      rw [H_tilde', if_neg (Nat.ne_of_gt hH)]
      rw [← Polynomial.coeff_natDegree (p := H)]
    have hmod : p %ₘ H_tilde' H = (-(Polynomial.C c * Polynomial.X ^ (s - 1) * lower)) %ₘ H_tilde' H := by
      apply Polynomial.modByMonic_eq_of_dvd_sub (H_tilde'_monic H hH)
      refine ⟨Polynomial.C c * Polynomial.X ^ (s - 1), ?_⟩
      rw [htilde]
      dsimp [p]
      rw [hdm, pow_add]
      ring
    have hsum_eq : Polynomial.C c * Polynomial.X ^ (s - 1) * lower =
        ∑ i ∈ Finset.range m,
          Polynomial.C (c * (H.coeff i * W ^ (m - 1 - i))) * Polynomial.X ^ ((s - 1) + i) := by
      dsimp [lower]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      let a : F[X] := H.coeff i * W ^ (m - 1 - i)
      change Polynomial.C c * Polynomial.X ^ (s - 1) * (Polynomial.C a * Polynomial.X ^ i) =
        Polynomial.C (c * a) * Polynomial.X ^ (s - 1 + i)
      calc
        Polynomial.C c * Polynomial.X ^ (s - 1) * (Polynomial.C a * Polynomial.X ^ i)
            = (Polynomial.C c * Polynomial.C a) * (Polynomial.X ^ (s - 1) * Polynomial.X ^ i) := by ring
        _ = Polynomial.C (c * a) * Polynomial.X ^ (s - 1 + i) := by
          rw [← Polynomial.C_mul, pow_add]
    have hraw : weight_Λ (-(Polynomial.C c * Polynomial.X ^ (s - 1) * lower)) H D ≤
        (WithBot.some ((d - 1) * (D - H.natDegree + 1)) : WithBot ℕ) := by
      rw [weight_Λ_neg]
      rw [hsum_eq]
      refine (weight_Λ_sum_le (Finset.range m)
        (fun i => Polynomial.C (c * (H.coeff i * W ^ (m - 1 - i))) * Polynomial.X ^ (s - 1 + i)) H D).trans ?_
      refine Finset.sup_le (fun i hi => ?_)
      have hi_lt : i < m := Finset.mem_range.mp hi
      have hHi : (H.coeff i).natDegree ≤ Bivariate.totalDegree H - i := by
        exact natDegree_coeff_le_of_totalDegree_le H (le_rfl) i
      have hWdeg : W.natDegree ≤ Bivariate.totalDegree H - m := by
        dsimp [W, m]
        exact natDegree_coeff_le_of_totalDegree_le H (le_rfl) H.natDegree
      have hWpow : (W ^ (m - 1 - i)).natDegree ≤ (m - 1 - i) * (Bivariate.totalDegree H - m) := by
        exact (Polynomial.natDegree_pow_le (p := W) (n := m - 1 - i)).trans
          (Nat.mul_le_mul_left _ hWdeg)
      have hHiW : (H.coeff i * W ^ (m - 1 - i)).natDegree ≤
          (Bivariate.totalDegree H - i) + (m - 1 - i) * (Bivariate.totalDegree H - m) := by
        calc
          (H.coeff i * W ^ (m - 1 - i)).natDegree ≤
              (H.coeff i).natDegree + (W ^ (m - 1 - i)).natDegree := Polynomial.natDegree_mul_le
          _ ≤ (Bivariate.totalDegree H - i) + (m - 1 - i) * (Bivariate.totalDegree H - m) :=
              Nat.add_le_add hHi hWpow
      have htermdeg : (c * (H.coeff i * W ^ (m - 1 - i))).natDegree ≤
          (D - Bivariate.totalDegree H) +
            ((Bivariate.totalDegree H - i) + (m - 1 - i) * (Bivariate.totalDegree H - m)) := by
        calc
          (c * (H.coeff i * W ^ (m - 1 - i))).natDegree ≤
              c.natDegree + (H.coeff i * W ^ (m - 1 - i)).natDegree := Polynomial.natDegree_mul_le
          _ ≤ (D - Bivariate.totalDegree H) +
              ((Bivariate.totalDegree H - i) + (m - 1 - i) * (Bivariate.totalDegree H - m)) :=
              Nat.add_le_add hcdeg hHiW
      have harith :
          (s - 1 + i) * (D - m + 1) +
            ((D - Bivariate.totalDegree H) + ((Bivariate.totalDegree H - i) + (m - 1 - i) * (Bivariate.totalDegree H - m))) ≤
          (d - 1) * (D - m + 1) := by
        have hT_le_D : Bivariate.totalDegree H ≤ D := hD_H
        have hi_le : i ≤ m - 1 := by omega
        have hi_le_m : i ≤ m := le_of_lt hi_lt
        have hi_le_T : i ≤ Bivariate.totalDegree H := le_trans hi_le_m hm_le_T
        have hkey :
            (s - 1 + i) * (D - m + 1) +
                ((D - Bivariate.totalDegree H) + ((Bivariate.totalDegree H - i) + (m - 1 - i) * (Bivariate.totalDegree H - m))) +
                (m - 1 - i) * (D - Bivariate.totalDegree H) =
              (d - 1) * (D - m + 1) := by
          rw [hdm]
          zify [hT_le_D, hm_le_T, hm_le_D, hi_le, hi_le_m, hi_le_T, hs_pos, hm_pos]
          ring_nf
        omega
      refine (weight_Λ_C_mul_X_pow_le H D (c * (H.coeff i * W ^ (m - 1 - i))) (s - 1 + i)).trans ?_
      rw [WithBot.coe_le_coe]
      have hM : D + 1 - Bivariate.natDegreeY H = D - m + 1 := by
        dsimp [m]
        rw [show Bivariate.natDegreeY H = H.natDegree from rfl]
        omega
      rw [hM]
      exact (Nat.add_le_add_left htermdeg ((s - 1 + i) * (D - m + 1))).trans harith
    calc
      weight_Λ (Polynomial.C ((d : F[X]) * Q.coeff (d - H.natDegree)) * Polynomial.X ^ (d - 1) %ₘ H_tilde' H) H D
          = weight_Λ (p %ₘ H_tilde' H) H D := by rfl
      _ = weight_Λ ((-(Polynomial.C c * Polynomial.X ^ (s - 1) * lower)) %ₘ H_tilde' H) H D := by rw [hmod]
      _ ≤ weight_Λ (-(Polynomial.C c * Polynomial.X ^ (s - 1) * lower)) H D :=
        weight_Λ_modByMonic_H_tilde'_le hD_H hH _
      _ ≤ (WithBot.some ((d - 1) * (D - H.natDegree + 1)) : WithBot ℕ) := hraw

theorem weight_Λ_over_𝒪_add_le {H : F[X][Y]} {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) (a b : 𝒪 H) :
    weight_Λ_over_𝒪 hH (a + b) D ≤
      max (weight_Λ_over_𝒪 hH a D) (weight_Λ_over_𝒪 hH b D) := by
  let pa := canonicalRepOf𝒪 hH a
  let pb := canonicalRepOf𝒪 hH b
  have hpa : weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) pa : 𝒪 H) D = weight_Λ pa H D := by
    exact weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH (canonicalRepOf𝒪_degree_lt hH a) D
  have hpb : weight_Λ_over_𝒪 hH (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) pb : 𝒪 H) D = weight_Λ pb H D := by
    exact weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH (canonicalRepOf𝒪_degree_lt hH b) D
  rw [← mk_canonicalRepOf𝒪 hH a, ← mk_canonicalRepOf𝒪 hH b]
  rw [hpa, hpb]
  exact le_trans (weight_Λ_over_𝒪_mk_le hD_H hH (pa + pb)) (weight_Λ_add_le pa pb H D)

noncomputable def xiPreLower (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : F[X][Y] :=
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  let d : ℕ := R.natDegree
  let W : F[X] := H.leadingCoeff
  ∑ i ∈ Finset.range (d - 1),
    Polynomial.C (P.coeff i * W ^ (d - 2 - i)) * Polynomial.X ^ i

theorem xiPreLower_coeff_natDegree_le (x₀ : F) {D i : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D) :
    (((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i *
        H.leadingCoeff ^ (R.natDegree - 2 - i)).natDegree) ≤
      (D - (i + 1)) + (R.natDegree - 2 - i) * (D - H.natDegree) := by
  have hcoeff := natDegree_derivative_evalX_coeff_le (i := i) x₀ R hD_Rx0
  have hlc := leadingCoeff_natDegree_le_of_totalDegree_le hD_H
  have hmul : (((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i * H.leadingCoeff ^ (R.natDegree - 2 - i)).natDegree) ≤
      ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i).natDegree + (H.leadingCoeff ^ (R.natDegree - 2 - i)).natDegree := Polynomial.natDegree_mul_le
  have hpow : (H.leadingCoeff ^ (R.natDegree - 2 - i)).natDegree ≤ (R.natDegree - 2 - i) * H.leadingCoeff.natDegree := Polynomial.natDegree_pow_le
  exact le_trans hmul (Nat.add_le_add hcoeff (le_trans hpow (Nat.mul_le_mul_left (R.natDegree - 2 - i) hlc)))

theorem xiPreLower_term_weight_le (x₀ : F) (hHyp : Hypotheses x₀ R H) (hRdeg : 2 ≤ R.natDegree)
    {D i : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D)
    (hi : i < R.natDegree - 1) :
    weight_Λ
      (Polynomial.C
        ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i *
          H.leadingCoeff ^ (R.natDegree - 2 - i)) *
        Polynomial.X ^ i)
      H D
      ≤ WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) := by
  refine le_trans (weight_Λ_C_mul_X_pow_le H D ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i * H.leadingCoeff ^ (R.natDegree - 2 - i)) i) ?_
  rw [WithBot.coe_le_coe]
  rw [show Bivariate.natDegreeY H = H.natDegree from rfl]
  have hcoeff := xiPreLower_coeff_natDegree_le x₀ hD_H hD_Rx0 (D := D) (i := i)
  have hdH_le_R : H.natDegree ≤ R.natDegree := H_natDegree_le_R_natDegree_of_Hypotheses hHyp
  have hHpos : 0 < H.natDegree := H_natDegree_pos.out
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hHpos
  have hH_in : H.natDegree ∈ H.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
  have hdH_le_D : H.natDegree ≤ D := by
    have : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    omega
  have hD1sub : D + 1 - H.natDegree = D - H.natDegree + 1 := by omega
  rw [hD1sub]
  set m : ℕ := D - H.natDegree
  have hcoeff_m :
      ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i *
          H.leadingCoeff ^ (R.natDegree - 2 - i)).natDegree ≤
        D - (i + 1) + (R.natDegree - 2 - i) * m := by
    simpa [m] using hcoeff
  have hi_le : i ≤ R.natDegree - 2 := by omega
  calc
    i * (m + 1) +
        ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i *
          H.leadingCoeff ^ (R.natDegree - 2 - i)).natDegree
        ≤ i * (m + 1) +
          ((D - (i + 1)) + (R.natDegree - 2 - i) * m) := by
          exact Nat.add_le_add_left hcoeff_m _
    _ ≤ (R.natDegree - 1) * (m + 1) := by
      by_cases hcase : i + 1 ≤ D
      · have hDpos : 1 ≤ D := by omega
        have hleft_eq :
            i * (m + 1) + (D - (i + 1) + (R.natDegree - 2 - i) * m) =
              (R.natDegree - 2) * m + (D - 1) := by
          zify [hcase, hRdeg, hi_le, hDpos]
          ring
        rw [hleft_eq]
        have hDminus : D - 1 ≤ m + (R.natDegree - 1) := by
          subst m
          omega
        have hright_eq :
            (R.natDegree - 2) * m + (m + (R.natDegree - 1)) =
              (R.natDegree - 1) * (m + 1) := by
          have hR1 : 1 ≤ R.natDegree := by omega
          zify [hRdeg, hR1]
          ring
        calc
          (R.natDegree - 2) * m + (D - 1)
              ≤ (R.natDegree - 2) * m + (m + (R.natDegree - 1)) := by
                exact Nat.add_le_add_left hDminus _
          _ = (R.natDegree - 1) * (m + 1) := hright_eq
      · have hDsub : D - (i + 1) = 0 := by omega
        rw [hDsub]
        rw [zero_add]
        have hleft_eq :
            i * (m + 1) + (R.natDegree - 2 - i) * m =
              (R.natDegree - 2) * m + i := by
          zify [hi_le]
          ring
        rw [hleft_eq]
        have hmul : (R.natDegree - 2) * m ≤ (R.natDegree - 1) * m := by
          exact Nat.mul_le_mul_right m (by omega)
        have hi_le_n1 : i ≤ R.natDegree - 1 := by omega
        have htarget_expand :
            (R.natDegree - 1) * (m + 1) = (R.natDegree - 1) * m + (R.natDegree - 1) := by
          ring
        rw [htarget_expand]
        exact Nat.add_le_add hmul hi_le_n1

theorem xiPreLower_weight_le (x₀ : F) (hHyp : Hypotheses x₀ R H) (hRdeg : 2 ≤ R.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D) :
    weight_Λ (xiPreLower x₀ R H) H D ≤
      WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) := by
  unfold xiPreLower
  refine le_trans (weight_Λ_sum_le (Finset.range (R.natDegree - 1)) (fun i => Polynomial.C ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i * H.leadingCoeff ^ (R.natDegree - 2 - i)) * Polynomial.X ^ i) H D) ?_
  apply Finset.sup_le
  intro i hi
  exact xiPreLower_term_weight_le x₀ hHyp hRdeg hD_H hD_Rx0 (Finset.mem_range.mp hi)

noncomputable def xiPreTop (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : F[X][Y] :=
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  let d : ℕ := R.natDegree
  let W : F[X] := H.leadingCoeff
  Polynomial.C (P.coeff (d - 1) / W) * Polynomial.X ^ (d - 1)

theorem xiPreTop_coeff_natDegree_zero_of_H_natDegree_eq_R_natDegree (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ R.natDegree) (heq : H.natDegree = R.natDegree) :
    ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) /
      H.leadingCoeff).natDegree = 0 := by
  classical
  set P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R with hP_def
  rcases hHyp.dvd_evalX with ⟨Q, hQ⟩
  have hP_ne : P ≠ 0 := by
    rw [hP_def]
    exact evalX_ne_zero_of_Hypotheses hHyp
  have hQ_ne : Q ≠ 0 := by
    intro h0
    apply hP_ne
    rw [hP_def, hQ, h0, mul_zero]
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hdegP : P.natDegree ≤ R.natDegree := by
    rw [hP_def]
    exact evalX_natDegree_le (Polynomial.C x₀) R
  have hQdeg : Q.natDegree = 0 := by
    have hmuldeg : (H * Q).natDegree = H.natDegree + Q.natDegree := by
      exact Polynomial.natDegree_mul hH_ne hQ_ne
    have hPdeg_eq : P.natDegree = (H * Q).natDegree := by
      rw [hP_def, hQ]
    omega
  let q : F[X] := Q.coeff 0
  have hQ_C : Q = Polynomial.C q := by
    exact Polynomial.eq_C_of_natDegree_le_zero (p := Q) (by omega)
  have hsepHQ : (H * Polynomial.C q).Separable := by
    rw [← hQ_C]
    rw [← hQ, ← hP_def]
    exact hHyp.separable_evalX
  have hq_unit : IsUnit q := by
    rw [Polynomial.separable_def'] at hsepHQ
    rcases hsepHQ with ⟨A, B, hAB⟩
    have hderiv : (H * Polynomial.C q).derivative = H.derivative * Polynomial.C q := by
      simp [Polynomial.derivative_mul]
    have hfactor : (A * H + B * H.derivative) * Polynomial.C q = (1 : F[X][Y]) := by
      calc
        (A * H + B * H.derivative) * Polynomial.C q
            = A * (H * Polynomial.C q) + B * (H.derivative * Polynomial.C q) := by ring
        _ = A * (H * Polynomial.C q) + B * (H * Polynomial.C q).derivative := by rw [hderiv]
        _ = 1 := hAB
    have hCunit : IsUnit (Polynomial.C q : F[X][Y]) := by
      exact isUnit_of_mul_eq_one (A * H + B * H.derivative) (by simpa [mul_comm] using hfactor)
    exact (Polynomial.isUnit_C.mp hCunit)
  have hsucc : R.natDegree - 1 + 1 = R.natDegree := by omega
  have hPtop : (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree = H.leadingCoeff * q := by
    rw [hQ, hQ_C]
    rw [← heq]
    simp [Polynomial.coeff_natDegree]
  have htop_coeff :
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
        H.leadingCoeff * (q * (R.natDegree : F[X])) := by
    rw [derivative_evalX_coeff, hsucc, hPtop]
    ring
  have hW_ne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH_ne
  have hdiv : H.leadingCoeff ∣
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) :=
    leadingCoeff_dvd_evalX_derivative_coeff_pred hHyp
  have hquot :
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) /
          H.leadingCoeff = q * (R.natDegree : F[X]) := by
    exact (EuclideanDomain.div_eq_iff_eq_mul_of_dvd
      ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1))
      H.leadingCoeff (q * (R.natDegree : F[X])) hW_ne hdiv).2 htop_coeff
  rw [hquot]
  have hqdeg0 : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hq_unit
  have hndeg0 : ((R.natDegree : F[X]).natDegree = 0) := by
    rw [← Polynomial.C_eq_natCast, Polynomial.natDegree_C]
  have hle : (q * (R.natDegree : F[X])).natDegree ≤ 0 := by
    calc
      (q * (R.natDegree : F[X])).natDegree ≤ q.natDegree + ((R.natDegree : F[X]).natDegree) :=
        Polynomial.natDegree_mul_le
      _ = 0 := by rw [hqdeg0, hndeg0, Nat.zero_add]
  omega

theorem xiPreTop_modByMonic_weight_le (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ R.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D)
    (hlt : H.natDegree < R.natDegree) :
    weight_Λ (xiPreTop x₀ R H %ₘ H_tilde' H) H D ≤
      (WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) : WithBot ℕ) := by
  classical
  rcases hHyp.dvd_evalX with ⟨Q, hQ⟩
  have hPne : Bivariate.evalX (Polynomial.C x₀) R ≠ 0 := evalX_ne_zero_of_Hypotheses hHyp
  have hHne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hWne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hHne
  have hQne : Q ≠ 0 := by
    intro hQ0
    apply hPne
    rw [hQ, hQ0, mul_zero]
  have hQdeg : Q.natDegree ≤ R.natDegree - H.natDegree := by
    have hproddeg : (H * Q).natDegree = H.natDegree + Q.natDegree := by
      rw [Polynomial.natDegree_mul hHne hQne]
    have hPdeg_eval : (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ R.natDegree := evalX_natDegree_le (Polynomial.C x₀) R
    rw [hQ] at hPdeg_eval
    omega
  have hD_HQ : Bivariate.totalDegree (H * Q) ≤ D := by
    simpa [← hQ] using hD_Rx0
  have hxi : xiPreTop x₀ R H = Polynomial.C ((R.natDegree : F[X]) * Q.coeff (R.natDegree - H.natDegree)) * Polynomial.X ^ (R.natDegree - 1) := by
    change Polynomial.C (((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) / H.leadingCoeff)) * Polynomial.X ^ (R.natDegree - 1) = Polynomial.C ((R.natDegree : F[X]) * Q.coeff (R.natDegree - H.natDegree)) * Polynomial.X ^ (R.natDegree - 1)
    congr 1
    have hdpos : 0 < R.natDegree := by omega
    have hsucc : R.natDegree - 1 + 1 = R.natDegree := Nat.sub_add_cancel hdpos
    have hder := derivative_evalX_coeff x₀ R (R.natDegree - 1)
    rw [hsucc] at hder
    have hcoeffP : (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree = H.leadingCoeff * Q.coeff (R.natDegree - H.natDegree) := by
      have hmle : H.natDegree ≤ R.natDegree := by omega
      have hmulcoeff := Polynomial.coeff_mul_add_eq_of_natDegree_le (f := H) (g := Q) (df := H.natDegree) (dg := R.natDegree - H.natDegree) (le_rfl) hQdeg
      have hsum : H.natDegree + (R.natDegree - H.natDegree) = R.natDegree := Nat.add_sub_cancel' hmle
      rw [hQ]
      simpa [hsum, Polynomial.coeff_natDegree] using hmulcoeff
    rw [hder, hcoeffP]
    rw [mul_assoc]
    have hdiv : H.leadingCoeff ∣ H.leadingCoeff * (Q.coeff (R.natDegree - H.natDegree) * (R.natDegree : F[X])) := dvd_mul_right _ _
    have hcancel := (EuclideanDomain.div_eq_iff_eq_mul_of_dvd (H.leadingCoeff * (Q.coeff (R.natDegree - H.natDegree) * (R.natDegree : F[X])) ) H.leadingCoeff (Q.coeff (R.natDegree - H.natDegree) * (R.natDegree : F[X])) hWne hdiv).2 (by ring)
    rw [hcancel]
    ring_nf
  simpa [hxi] using (cofactor_top_reduction_weight_le (H := H) hH (Q := Q) (d := R.natDegree) (D := D) hD_H hD_HQ hlt hQdeg)

theorem xiPreTop_modByMonic_coeff_natDegree_le (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ R.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D)
    (hlt : H.natDegree < R.natDegree) (n : ℕ) :
    ((xiPreTop x₀ R H %ₘ H_tilde' H).coeff n).natDegree ≤
      (R.natDegree - 1 - n) * (D - H.natDegree + 1) := by
  classical
  let f : F[X][Y] := xiPreTop x₀ R H %ₘ H_tilde' H
  let m : ℕ := D - H.natDegree + 1
  have hwt : weight_Λ f H D ≤ (WithBot.some ((R.natDegree - 1) * m) : WithBot ℕ) := by
    dsimp [f, m]
    exact xiPreTop_modByMonic_weight_le x₀ hH hHyp hRdeg hD_H hD_Rx0 hlt
  have hHne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hHin : H.natDegree ∈ H.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hHne)
  have hHdeg_le_D : H.natDegree ≤ D := by
    have htd : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hHin
    omega
  by_cases hcoeff : f.coeff n = 0
  · dsimp [f] at hcoeff ⊢
    simp only [hcoeff, Polynomial.natDegree_zero, zero_le]
  · have hnmem : n ∈ f.support := by
      rw [Polynomial.mem_support_iff]
      exact hcoeff
    have hineq := (weight_Λ_le_iff.mp hwt) n hnmem
    have hbY : Bivariate.natDegreeY H = H.natDegree := rfl
    have hm_eq : D + 1 - Bivariate.natDegreeY H = m := by
      dsimp [m]
      rw [hbY]
      omega
    have hineq_m : n * m + (f.coeff n).natDegree ≤ (R.natDegree - 1) * m := by
      simpa only [hm_eq] using hineq
    have hineq_m' : (f.coeff n).natDegree + n * m ≤ (R.natDegree - 1) * m := by
      simpa only [Nat.add_comm] using hineq_m
    have hsub : (f.coeff n).natDegree ≤ (R.natDegree - 1) * m - n * m :=
      Nat.le_sub_of_add_le hineq_m'
    have hbound : (f.coeff n).natDegree ≤ (R.natDegree - 1 - n) * m := by
      rw [Nat.sub_mul]
      exact hsub
    exact hbound

theorem xiPreTop_topCoeff_mul_natDegree_le (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ R.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D) :
    (H.leadingCoeff *
      ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) /
        H.leadingCoeff)).natDegree ≤ D - R.natDegree := by
  let P := Bivariate.evalX (Polynomial.C x₀) R.derivative
  let W := H.leadingCoeff
  have hWne : W ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hH)
  have hdiv : W ∣ P.coeff (R.natDegree - 1) := by
    simpa [P, W] using leadingCoeff_dvd_evalX_derivative_coeff_pred hHyp
  have hmul : W * (P.coeff (R.natDegree - 1) / W) = P.coeff (R.natDegree - 1) := by
    exact EuclideanDomain.mul_div_cancel' hWne hdiv
  rw [show H.leadingCoeff * ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) / H.leadingCoeff) = P.coeff (R.natDegree - 1) by simpa [P, W] using hmul]
  have hdeg := natDegree_derivative_evalX_coeff_le x₀ R hD_Rx0 (i := R.natDegree - 1)
  have hRpos : 1 ≤ R.natDegree := by omega
  have hpred : R.natDegree - 1 + 1 = R.natDegree := Nat.sub_add_cancel hRpos
  rw [hpred] at hdeg
  simpa [P] using hdeg

theorem xiPreTop_weight_over_𝒪_le_of_H_natDegree_lt_R_natDegree (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ R.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D)
    (hlt : H.natDegree < R.natDegree) :
    weight_Λ_over_𝒪 hH
      (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (xiPreTop x₀ R H) : 𝒪 H) D
      ≤ WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) := by
  rw [weight_Λ_over_𝒪_mk]
  rw [weight_Λ_le_iff]
  intro n hn
  have hcoeff_bound :=
    xiPreTop_modByMonic_coeff_natDegree_le x₀ hH hHyp hRdeg hD_H hD_Rx0 hlt n
  have hbY : Bivariate.natDegreeY H = H.natDegree := rfl
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hH_in : H.natDegree ∈ H.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
  have hHd_le_D : H.natDegree ≤ D := by
    have htd : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    omega
  have hq_ne_one : H_tilde' H ≠ (1 : F[X][Y]) := by
    intro hq1
    have hnat : (H_tilde' H).natDegree = (1 : F[X][Y]).natDegree := by
      rw [hq1]
    rw [natDegree_H_tilde' hH] at hnat
    simp at hnat
    omega
  have hrem_nat_lt : (xiPreTop x₀ R H %ₘ H_tilde' H).natDegree < H.natDegree := by
    have hltrem :=
      Polynomial.natDegree_modByMonic_lt (xiPreTop x₀ R H) (H_tilde'_monic H hH) hq_ne_one
    rwa [natDegree_H_tilde' hH] at hltrem
  have hn_le_rem : n ≤ (xiPreTop x₀ R H %ₘ H_tilde' H).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)
  have hn_lt_H : n < H.natDegree := lt_of_le_of_lt hn_le_rem hrem_nat_lt
  have hn_le_Rminus1 : n ≤ R.natDegree - 1 := by
    omega
  rw [hbY]
  rw [show D + 1 - H.natDegree = D - H.natDegree + 1 by omega]
  calc
    n * (D - H.natDegree + 1) + ((xiPreTop x₀ R H %ₘ H_tilde' H).coeff n).natDegree
        ≤ n * (D - H.natDegree + 1) + (R.natDegree - 1 - n) * (D - H.natDegree + 1) := by
          exact Nat.add_le_add_left hcoeff_bound _
    _ = (n + (R.natDegree - 1 - n)) * (D - H.natDegree + 1) := by
          rw [Nat.add_mul]
    _ = (R.natDegree - 1) * (D - H.natDegree + 1) := by
          have hsum : n + (R.natDegree - 1 - n) = R.natDegree - 1 := by omega
          rw [hsum]

theorem xiPreTop_weight_over_𝒪_le (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ R.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D) :
    weight_Λ_over_𝒪 hH
      (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (xiPreTop x₀ R H) : 𝒪 H) D
      ≤ WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) := by
  classical
  have hHleR : H.natDegree ≤ R.natDegree := H_natDegree_le_R_natDegree_of_Hypotheses hHyp
  rcases lt_or_eq_of_le hHleR with hlt | heq
  · exact xiPreTop_weight_over_𝒪_le_of_H_natDegree_lt_R_natDegree x₀ hH hHyp hRdeg hD_H hD_Rx0 hlt
  · have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
    have hH_in : H.natDegree ∈ H.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
    have hHleD : H.natDegree ≤ D := by
      have hcoeff_total := Bivariate.coeff_totalDegree_le H hH_in
      omega
    have hRleD : R.natDegree ≤ D := by omega
    have hsub : D + 1 - R.natDegree = D - R.natDegree + 1 := by omega
    unfold xiPreTop
    let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
    let d : ℕ := R.natDegree
    let W : F[X] := H.leadingCoeff
    have hcoeff0 : (P.coeff (d - 1) / W).natDegree = 0 := by
      dsimp [P, d, W]
      exact xiPreTop_coeff_natDegree_zero_of_H_natDegree_eq_R_natDegree x₀ hH hHyp hRdeg heq
    refine le_trans (weight_Λ_over_𝒪_mk_le hD_H hH _) ?_
    refine le_trans (weight_Λ_C_mul_X_pow_le H D (P.coeff (d - 1) / W) (d - 1)) ?_
    rw [WithBot.coe_le_coe]
    dsimp [P, d, W]
    rw [hcoeff0]
    rw [Bivariate.natDegreeY]
    rw [heq]
    rw [hsub]
    omega

theorem xiPre_eq_lower_add_top (x₀ : F) (hRdeg : 2 ≤ R.natDegree) :
    ξ_pre x₀ R H = xiPreLower x₀ R H + xiPreTop x₀ R H := by
  simp only [ξ_pre, xiPreLower, xiPreTop, hRdeg, if_pos]


/-- The bound of the weight `Λ` of the elements `ξ` as stated in Claim A.2 of Appendix A.4
of [BCIKS20].

The explicit hypothesis `2 ≤ R.natDegree` is needed because the paper uses `W^(d-2)`, while
Lean's natural-number exponent would otherwise totalize the low-degree cases by truncation. -/
lemma ξ_weight_le (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    {D : ℕ} (hD_H : D ≥ Bivariate.totalDegree H)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)) :
    weight_Λ_over_𝒪 hH (ξ x₀ R H hHyp) D ≤
    WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  have hRdeg' : 2 ≤ R.natDegree := by
    simpa [Bivariate.natDegreeY] using hRdeg
  have hD_H' : Bivariate.totalDegree H ≤ D := hD_H
  have hD_Rx0' : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D := hD_Rx0
  unfold ξ
  rw [xiPre_eq_lower_add_top x₀ hRdeg']
  refine (weight_Λ_over_𝒪_add_le hD_H' hH
    (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (xiPreLower x₀ R H) : 𝒪 H)
    (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (xiPreTop x₀ R H) : 𝒪 H)).trans ?_
  apply max_le
  · exact (weight_Λ_over_𝒪_mk_le hD_H' hH (xiPreLower x₀ R H)).trans
      (by simpa [Bivariate.natDegreeY] using xiPreLower_weight_le x₀ hHyp hRdeg' hD_H' hD_Rx0')
  · simpa [Bivariate.natDegreeY] using
      (xiPreTop_weight_over_𝒪_le x₀ hH hHyp hRdeg' hD_H' hD_Rx0')

/-- The exponent of `ξ` in the denominator of the `t`-th Hensel coefficient.

The paper separates `t = 0`, where no `ξ` factor appears, from `t ≥ 1`, where the exponent is
`2*t - 1`. -/
def henselDenominatorExponent (t : ℕ) : ℕ :=
  if t = 0 then 0 else 2 * t - 1

@[simp]
lemma henselDenominatorExponent_zero : henselDenominatorExponent 0 = 0 := by
  simp [henselDenominatorExponent]

@[simp]
lemma henselDenominatorExponent_succ (t : ℕ) :
    henselDenominatorExponent (t + 1) = 2 * (t + 1) - 1 := by
  simp [henselDenominatorExponent]

/-- A total degree for the trivariate polynomial `R`, represented as a polynomial in `Y` with
bivariate coefficients in the `Z` and `X` variables. -/
def trivariateTotalDegree (R : F[X][X][Y]) : ℕ :=
  R.support.sup (fun i => Bivariate.totalDegree (R.coeff i) + i)

/-- Each coefficient of `R` is bounded by `trivariateTotalDegree R`. -/
lemma coeff_totalDegree_add_index_le_trivariateTotalDegree (R : F[X][X][Y]) {i : ℕ}
    (hi : i ∈ R.support) :
    Bivariate.totalDegree (R.coeff i) + i ≤ trivariateTotalDegree R := by
  classical
  unfold trivariateTotalDegree
  exact Finset.le_sup (f := fun i => Bivariate.totalDegree (R.coeff i) + i) hi

/-- A canonical degree bound large enough for both `H` and all coefficients of `R`. -/
def defaultDegreeBound (R : F[X][X][Y]) (H : F[X][Y]) : ℕ :=
  max (Bivariate.totalDegree H) (trivariateTotalDegree R)

lemma defaultDegreeBound_ge_H (R : F[X][X][Y]) (H : F[X][Y]) :
    Bivariate.totalDegree H ≤ defaultDegreeBound R H :=
  le_max_left _ _

lemma defaultDegreeBound_ge_R_coeff (R : F[X][X][Y]) (H : F[X][Y]) {i : ℕ}
    (hi : i ∈ R.support) :
    Bivariate.totalDegree (R.coeff i) + i ≤ defaultDegreeBound R H :=
  (coeff_totalDegree_add_index_le_trivariateTotalDegree R hi).trans (le_max_right _ _)

/-- Coefficients in `F[Z][X]` evaluated as power series over the function field: `Z` is sent to
the function-field coefficient embedding, and the `X` variable is sent to `x₀ + S`, where `S` is
the power-series variable. This realizes the local coordinate `S = X - x₀` of [BCIKS20] A.4, so
that a root condition becomes an identity in `𝕃 H⟦S⟧ = L[[X - x₀]]`. -/
noncomputable def liftCoeffToPowerSeries (x₀ : F) (H : F[X][Y]) :
    F[X][X] →+* PowerSeries (𝕃 H) :=
  Polynomial.eval₂RingHom (RingHom.comp PowerSeries.C (liftToFunctionField (H := H)))
    (PowerSeries.C (fieldTo𝕃 (H := H) x₀) + PowerSeries.X)

/-- Evaluation of the trivariate polynomial `R(X,Y,Z)` at a power series `Γ` for the `Y`
variable, with the `X` variable interpreted as `x₀ + S` (`S` the power-series variable, i.e. the
local coordinate `X - x₀`) and `Z` interpreted in the function field of `H`. -/
noncomputable def evalRAtPowerSeries (x₀ : F) (H : F[X][Y]) (R : F[X][X][Y])
    (Γ : PowerSeries (𝕃 H)) : PowerSeries (𝕃 H) :=
  Polynomial.eval₂ (liftCoeffToPowerSeries x₀ H) Γ R

/-- The coefficient sequence obtained from a candidate sequence of regular numerators. -/
noncomputable def alphaOfNumerators (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (βseq t) /
    (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H hHyp)) ^
      henselDenominatorExponent t)

/-- The local power series `γ = ∑ αₜ Sᵗ` induced by a candidate sequence of regular numerators,
where `S = X - x₀` is the local coordinate of [BCIKS20] A.4. The `x₀`-shift is carried by
`evalRAtPowerSeries` (`X ↦ x₀ + S`), not by `γ`, matching the paper's `γ ∈ L[[X - x₀]]`. -/
noncomputable def gammaOfNumerators (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) :
    PowerSeries (𝕃 H) :=
  PowerSeries.mk (alphaOfNumerators x₀ R H hHyp βseq)

/-- A numerator sequence has the semantic content required by Claim A.2: it gives the Hensel
lift starting at `T / W`, and the induced power series is a root of `R(x₀ + S, ·, Z)`. -/
def IsHenselNumeratorSequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) : Prop :=
  alphaOfNumerators x₀ R H hHyp βseq 0 =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
    evalRAtPowerSeries x₀ H R (gammaOfNumerators x₀ R H hHyp βseq) = 0

theorem evalX_totalDegree_le_of_coeff_bound (x₀ : F) (R : F[X][X][Y]) {D : ℕ}
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D) :
    Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D := by
  classical
  unfold Bivariate.totalDegree
  refine Finset.sup_le ?_
  intro i hi
  have hcoeff_eval_ne : (Bivariate.evalX (Polynomial.C x₀) R).coeff i ≠ 0 :=
    Polynomial.mem_support_iff.mp hi
  have hcoeff_eq : (Bivariate.evalX (Polynomial.C x₀) R).coeff i =
      (R.coeff i).eval (Polynomial.C x₀) := by
    simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
  have hRcoeff_ne : R.coeff i ≠ 0 := by
    intro h0
    apply hcoeff_eval_ne
    rw [hcoeff_eq, h0]
    simp
  have hiR : i ∈ R.support := Polynomial.mem_support_iff.mpr hRcoeff_ne
  have heval_deg : ((Bivariate.evalX (Polynomial.C x₀) R).coeff i).natDegree ≤
      Bivariate.totalDegree (R.coeff i) := by
    rw [hcoeff_eq]
    have hP : (Polynomial.C x₀ : F[X]).natDegree ≤ 1 - 1 := by
      simp [Polynomial.natDegree_C]
    have hle := Bivariate.degree_eval_le_weightedDegree (Q := R.coeff i)
      (P := Polynomial.C x₀) (k := 1) hP
    have hw_le_total : Bivariate.natWeightedDegree (R.coeff i) 1 (1 - 1) ≤
        Bivariate.totalDegree (R.coeff i) := by
      unfold Bivariate.natWeightedDegree Bivariate.totalDegree
      simp only [Nat.sub_self, one_mul, zero_mul, add_zero]
      refine Finset.sup_le ?_
      intro j hj
      have hsup : ((R.coeff i).coeff j).natDegree + j ≤
          (R.coeff i).support.sup (fun m => ((R.coeff i).coeff m).natDegree + m) :=
        Finset.le_sup (s := (R.coeff i).support)
          (f := fun m => ((R.coeff i).coeff m).natDegree + m) hj
      exact le_trans (Nat.le_add_right ((R.coeff i).coeff j).natDegree j) hsup
    exact hle.trans hw_le_total
  have hD := hD_R i hiR
  omega

/-- The local power series `γ = ∑ αₜ Sᵗ ∈ 𝕃 H⟦S⟧`, where `S = X - x₀` is the local coordinate
of [BCIKS20] Appendix A.4. The `x₀`-shift lives in `evalRAtPowerSeries` (`X ↦ x₀ + S`), not in
`γ` itself, matching the paper's `γ ∈ L[[X - x₀]]`. -/
noncomputable def gammaFromAlpha (H : F[X][Y]) (αseq : ℕ → 𝕃 H) :
    PowerSeries (𝕃 H) :=
  PowerSeries.mk αseq

def HasNumeratorShape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H) : Prop :=
  ∀ t : ℕ, alphaOfNumerators x₀ R H hHyp βseq t = αseq t

theorem beta_zero_eq_X_of_shape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    βseq 0 =
      (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) : 𝒪 H) := by
  classical
  apply embeddingOf𝒪Into𝕃_injective hH
  have h0 := hshape 0
  unfold alphaOfNumerators at h0
  simp only [henselDenominatorExponent_zero, pow_zero, mul_one, zero_add, pow_one] at h0
  rw [hα0] at h0
  have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  field_simp [hW] at h0
  rw [embeddingOf𝒪Into𝕃_mk, liftBivariate_X]
  exact h0

theorem coeff_mul_eq_zero_of_orders {A : Type} [CommRing A] {m : ℕ}
    (u v : PowerSeries A) (a b : ℕ)
    (hab : m < a + b) (hu : ∀ i < a, PowerSeries.coeff i u = 0)
    (hv : ∀ i < b, PowerSeries.coeff i v = 0) :
    PowerSeries.coeff m (u * v) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hsum : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
  rcases lt_or_ge p.1 a with h1 | h1
  · rw [hu p.1 h1, zero_mul]
  · have : p.2 < b := by omega
    rw [hv p.2 this, mul_zero]

theorem coeff_mul_of_low_order {A : Type} [CommRing A] (n : ℕ) (P δ : PowerSeries A)
    (hδ : ∀ i < n, PowerSeries.coeff i δ = 0) :
    PowerSeries.coeff n (P * δ) = PowerSeries.constantCoeff P * PowerSeries.coeff n δ := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single (0, n)]
  · simp [PowerSeries.coeff_zero_eq_constantCoeff]
  · intro b hb hbne
    have hmem : b.1 + b.2 = n := Finset.mem_antidiagonal.mp hb
    have hb2 : b.2 < n := by
      rcases Nat.eq_zero_or_pos b.1 with h | h
      · exfalso; apply hbne; ext
        · simp [h]
        · simp; omega
      · omega
    rw [hδ b.2 hb2, mul_zero]
  · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

theorem remainder_low_order {A B : Type} [CommRing A] [CommRing B] (n : ℕ)
    (φ : A →+* PowerSeries B)
    (Γ δ : PowerSeries B) (hδ : ∀ i < n, PowerSeries.coeff i δ = 0) (p : A[X]) :
    ∀ i < 2 * n, PowerSeries.coeff i
      (Polynomial.eval₂ φ (Γ + δ) p - Polynomial.eval₂ φ Γ p
        - Polynomial.eval₂ φ Γ (Polynomial.derivative p) * δ) = 0 := by
  induction p using Polynomial.induction_on with
  | C a =>
      intro i hi
      simp [Polynomial.derivative_C]
  | add p q hp hq =>
      intro i hi
      have e1 := hp i hi
      have e2 := hq i hi
      simp only [Polynomial.eval₂_add, add_mul, map_sub, map_add] at *
      linear_combination e1 + e2
  | monomial m a hp =>
      intro i hi
      set q : A[X] := Polynomial.C a * Polynomial.X ^ m with hq_def
      have hmulX : Polynomial.C a * Polynomial.X ^ (m+1) = q * Polynomial.X := by
        rw [hq_def]; ring
      rw [hmulX]
      have hderiv : Polynomial.derivative (q * Polynomial.X)
          = Polynomial.derivative q * Polynomial.X + q := by
        rw [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one]
      rw [hderiv]
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_add]
      set u := Polynomial.eval₂ φ Γ q with hu_def
      set up := Polynomial.eval₂ φ (Γ + δ) q with hup_def
      set d := Polynomial.eval₂ φ Γ (Polynomial.derivative q) with hd_def
      have hrewrite : up * (Γ + δ) - u * Γ - (d * Γ + u) * δ
          = d * (δ * δ) + (up - u - d * δ) * (Γ + δ) := by ring
      rw [hrewrite, map_add]
      have h1 : PowerSeries.coeff i (d * (δ * δ)) = 0 := by
        apply coeff_mul_eq_zero_of_orders d (δ * δ) 0 (2*n) (by omega)
        · intro j hj; omega
        · intro j hj
          exact coeff_mul_eq_zero_of_orders δ δ n n (by omega) hδ hδ
      have h2 : PowerSeries.coeff i ((up - u - d * δ) * (Γ + δ)) = 0 := by
        apply coeff_mul_eq_zero_of_orders (up - u - d * δ) (Γ + δ) (2*n) 0 (by omega)
        · intro j hj; exact hp j hj
        · intro j hj; omega
      rw [h1, h2, add_zero]



theorem constantCoeff_liftCoeffToPowerSeries (x₀ : F) (p : F[X][X]) :
    PowerSeries.constantCoeff (liftCoeffToPowerSeries x₀ H p) =
      liftToFunctionField (H := H) (p.eval (Polynomial.C x₀)) := by
  unfold liftCoeffToPowerSeries
  rw [coe_eval₂RingHom, Polynomial.hom_eval₂]
  have hconst : RingHom.comp (PowerSeries.constantCoeff (R := 𝕃 H))
      (RingHom.comp PowerSeries.C (liftToFunctionField (H := H)))
      = liftToFunctionField (H := H) := by
    refine RingHom.ext fun z => ?_
    simp
  rw [hconst]
  have hs : PowerSeries.constantCoeff (R := 𝕃 H)
      (PowerSeries.C (fieldTo𝕃 (H := H) x₀) + PowerSeries.X) = fieldTo𝕃 (H := H) x₀ := by
    simp
  rw [hs]
  have : fieldTo𝕃 (H := H) x₀ = liftToFunctionField (H := H) (Polynomial.C x₀) := rfl
  rw [this, Polynomial.eval₂_hom]

theorem constantCoeff_eval₂_liftCoeff (x₀ : F) (q : F[X][X][Y]) (Γ : PowerSeries (𝕃 H)) :
    PowerSeries.constantCoeff (Polynomial.eval₂ (liftCoeffToPowerSeries x₀ H) Γ q) =
      Polynomial.eval₂ (liftToFunctionField (H := H))
        (PowerSeries.constantCoeff Γ) (Bivariate.evalX (Polynomial.C x₀) q) := by
  rw [Polynomial.hom_eval₂]
  rw [Bivariate.evalX_eq_map, Polynomial.eval₂_map]
  congr 1
  refine RingHom.ext fun p => ?_
  show PowerSeries.constantCoeff (liftCoeffToPowerSeries x₀ H p) = _
  rw [constantCoeff_liftCoeffToPowerSeries]
  rfl

-- constantCoeff of derivative eval = ζ when constantCoeff Γ = T/W
theorem constantCoeff_eval₂_derivative_eq_zeta (x₀ : F) (R : F[X][X][Y])
    (Γ : PowerSeries (𝕃 H))
    (hΓ0 : PowerSeries.constantCoeff Γ =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) :
    PowerSeries.constantCoeff
        (Polynomial.eval₂ (liftCoeffToPowerSeries x₀ H) Γ R.derivative)
      = ζ R x₀ H := by
  rw [constantCoeff_eval₂_liftCoeff, hΓ0]
  rfl



theorem coeff_evalR_split (x₀ : F) (R : F[X][X][Y]) (n : ℕ) (hn : 1 ≤ n)
    (Γ δ : PowerSeries (𝕃 H)) (hδ : ∀ i < n, PowerSeries.coeff i δ = 0)
    (hΓ0 : PowerSeries.constantCoeff Γ =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) :
    PowerSeries.coeff n (evalRAtPowerSeries x₀ H R (Γ + δ)) =
      PowerSeries.coeff n (evalRAtPowerSeries x₀ H R Γ)
        + ζ R x₀ H * PowerSeries.coeff n δ := by
  unfold evalRAtPowerSeries
  have hrem := remainder_low_order n (liftCoeffToPowerSeries x₀ H) Γ δ hδ R n (by omega)
  rw [map_sub, map_sub, sub_eq_zero, sub_eq_iff_eq_add] at hrem
  rw [hrem, coeff_mul_of_low_order n _ δ hδ,
    constantCoeff_eval₂_derivative_eq_zeta x₀ R Γ hΓ0, add_comm]

-- base case n=0
theorem coeff_zero_evalR (x₀ : F) (R : F[X][X][Y]) (Γ : PowerSeries (𝕃 H)) :
    PowerSeries.coeff 0 (evalRAtPowerSeries x₀ H R Γ) =
      Polynomial.eval₂ (liftToFunctionField (H := H)) (PowerSeries.constantCoeff Γ)
        (Bivariate.evalX (Polynomial.C x₀) R) := by
  unfold evalRAtPowerSeries
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_eval₂_liftCoeff]



theorem coeff_evalR_stable (x₀ : F) (R : F[X][X][Y]) (n m : ℕ) (hm : m < n)
    (Γ δ : PowerSeries (𝕃 H)) (hδ : ∀ i < n, PowerSeries.coeff i δ = 0) :
    PowerSeries.coeff m (evalRAtPowerSeries x₀ H R (Γ + δ)) =
      PowerSeries.coeff m (evalRAtPowerSeries x₀ H R Γ) := by
  unfold evalRAtPowerSeries
  have hrem := remainder_low_order n (liftCoeffToPowerSeries x₀ H) Γ δ hδ R m (by omega)
  rw [map_sub, map_sub, sub_eq_zero, sub_eq_iff_eq_add] at hrem
  rw [hrem]
  have hz : PowerSeries.coeff m
      (Polynomial.eval₂ (liftCoeffToPowerSeries x₀ H) Γ (derivative R) * δ) = 0 := by
    apply coeff_mul_eq_zero_of_orders _ δ 0 n (by omega)
    · intro j hj; omega
    · exact hδ
  rw [hz, zero_add]


-- The recursive construction.
noncomputable def bSeq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] : ℕ → (ℕ → 𝕃 H)
  | 0 => fun i => if i = 0 then
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff else 0
  | (N+1) => Function.update (bSeq x₀ R H N) (N+1)
      (- PowerSeries.coeff (N+1)
          (evalRAtPowerSeries x₀ H R (PowerSeries.mk (bSeq x₀ R H N))) / ζ R x₀ H)

noncomputable def alphaSeq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] : ℕ → 𝕃 H :=
  fun n => bSeq x₀ R H n n

-- bSeq N agrees with bSeq (N+1) below N+1
theorem bSeq_succ_def (x₀ : F) (R : F[X][X][Y]) (N : ℕ) :
    bSeq x₀ R H (N+1) = Function.update (bSeq x₀ R H N) (N+1)
      (- PowerSeries.coeff (N+1)
          (evalRAtPowerSeries x₀ H R (PowerSeries.mk (bSeq x₀ R H N))) / ζ R x₀ H) := by
  rfl

theorem bSeq_succ_eq_below (x₀ : F) (R : F[X][X][Y]) (N i : ℕ) (hi : i < N + 1) :
    bSeq x₀ R H (N+1) i = bSeq x₀ R H N i := by
  rw [bSeq_succ_def, Function.update_apply, if_neg (by omega)]

-- value 0 is T/W for all N
theorem bSeq_zero (x₀ : F) (R : F[X][X][Y]) (N : ℕ) :
    bSeq x₀ R H N 0 =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff := by
  induction N with
  | zero => simp [bSeq]
  | succ N ih => rw [bSeq_succ_eq_below x₀ R N 0 (by omega), ih]



theorem bSeq_stable (x₀ : F) (R : F[X][X][Y]) (N i : ℕ) (hi : i ≤ N) :
    bSeq x₀ R H N i = alphaSeq x₀ R H i := by
  induction N with
  | zero =>
      interval_cases i
      rfl
  | succ N ih =>
      rcases Nat.lt_or_ge i (N+1) with h | h
      · rw [bSeq_succ_eq_below x₀ R N i h]
        exact ih (by omega)
      · have : i = N + 1 := by omega
        subst this
        rfl

-- mk (bSeq N) agrees with mk (alphaSeq) at indices ≤ N
theorem mk_bSeq_coeff_eq (x₀ : F) (R : F[X][X][Y]) (N i : ℕ) (hi : i ≤ N) :
    PowerSeries.coeff i (PowerSeries.mk (bSeq x₀ R H N)) =
      PowerSeries.coeff i (PowerSeries.mk (alphaSeq x₀ R H)) := by
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, bSeq_stable x₀ R N i hi]



theorem bSeq_eq_zero_of_gt (x₀ : F) (R : F[X][X][Y]) (N j : ℕ) (hj : N < j) :
    bSeq x₀ R H N j = 0 := by
  induction N generalizing j with
  | zero =>
      have : j ≠ 0 := by omega
      simp [bSeq, this]
  | succ N ih =>
      rw [bSeq_succ_def, Function.update_apply, if_neg (by omega)]
      exact ih j (by omega)

-- δ helper: mk (bSeq (N+1)) = mk (bSeq N) + δ with δ low order N+1
theorem coeff_delta_below (x₀ : F) (R : F[X][X][Y]) (N i : ℕ) (hi : i < N + 1) :
    PowerSeries.coeff i
      (PowerSeries.mk (bSeq x₀ R H (N+1)) - PowerSeries.mk (bSeq x₀ R H N)) = 0 := by
  rw [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk, bSeq_succ_eq_below x₀ R N i hi,
    sub_self]

theorem root_bSeq (x₀ : F) (R : F[X][X][Y])
    (hinit : Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) R) = 0)
    (hzeta : ζ R x₀ H ≠ 0) :
    ∀ N, ∀ m ≤ N, PowerSeries.coeff m
      (evalRAtPowerSeries x₀ H R (PowerSeries.mk (bSeq x₀ R H N))) = 0 := by
  intro N
  induction N with
  | zero =>
      intro m hm
      interval_cases m
      rw [coeff_zero_evalR]
      have hcc : PowerSeries.constantCoeff (PowerSeries.mk (bSeq x₀ R H 0)) =
          functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, bSeq_zero]
      rw [hcc, hinit]
  | succ N ih =>
      intro m hm
      set Γ := PowerSeries.mk (bSeq x₀ R H N) with hΓ
      set δ := PowerSeries.mk (bSeq x₀ R H (N+1)) - PowerSeries.mk (bSeq x₀ R H N) with hδ_def
      have hsum : PowerSeries.mk (bSeq x₀ R H (N+1)) = Γ + δ := by rw [hδ_def]; ring
      have hδlow : ∀ i < N + 1, PowerSeries.coeff i δ = 0 := by
        intro i hi; rw [hδ_def]; exact coeff_delta_below x₀ R N i hi
      have hΓ0 : PowerSeries.constantCoeff Γ =
          functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff := by
        rw [hΓ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, bSeq_zero]
      rw [hsum]
      rcases Nat.lt_or_ge m (N+1) with hlt | hge
      · rw [coeff_evalR_stable x₀ R (N+1) m hlt Γ δ hδlow]
        exact ih m (by omega)
      · have hmeq : m = N + 1 := by omega
        subst hmeq
        rw [coeff_evalR_split x₀ R (N+1) (by omega) Γ δ hδlow hΓ0]
        -- coeff (N+1) δ = bSeq (N+1)(N+1) - bSeq N (N+1)
        have hδval : PowerSeries.coeff (N+1) δ =
            bSeq x₀ R H (N+1) (N+1) - bSeq x₀ R H N (N+1) := by
          rw [hδ_def, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
        have hbN1 : bSeq x₀ R H N (N+1) = 0 := bSeq_eq_zero_of_gt x₀ R N (N+1) (by omega)
        have hval : bSeq x₀ R H (N+1) (N+1) =
            - PowerSeries.coeff (N+1) (evalRAtPowerSeries x₀ H R Γ) / ζ R x₀ H := by
          rw [bSeq_succ_def, Function.update_self, hΓ]
        rw [hδval, hbN1, sub_zero, hval]
        field_simp
        ring

theorem formalHenselAlphaSequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hinit : Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) R) = 0)
    (hzeta : ζ R x₀ H ≠ 0) :
    ∃ αseq : ℕ → 𝕃 H,
      αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
      evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0 := by
  -- Formal-Hensel / Newton iteration over the field `𝕃 H`, in the local coordinate
  -- `S = X - x₀` (so `evalRAtPowerSeries` evaluates `R` at `X ↦ x₀ + S`).
  -- Construct `αseq` coefficient-by-coefficient with `α₀ = T/W` (`hinit` is the base).
  -- Key linearity lemma: `coeff (n) (evalRAtPowerSeries x₀ H R (mk α)) = ζ * α n + c n`
  -- where `c n` depends only on `α i, i < n` (the partition expansion of A.4, in which
  -- `αₙ` first appears at degree `n` with coefficient `A₀,λ⁽ⁿ⁾ = ζ`). Since `hzeta` makes
  -- `ζ` a unit, solve `α n = -c n / ζ`, so every coefficient of `evalR` vanishes; conclude
  -- with `PowerSeries.ext`. (`𝕃 H⟦S⟧` is also Henselian, but `R` need not be monic in `Y`.)
  refine ⟨alphaSeq x₀ R H, ?_, ?_⟩
  · show bSeq x₀ R H 0 0 = _
    simp [bSeq]
  · unfold gammaFromAlpha
    ext m
    rw [map_zero]
    set α := PowerSeries.mk (alphaSeq x₀ R H) with hα
    set Γ := PowerSeries.mk (bSeq x₀ R H m) with hΓ
    set δ := α - Γ with hδ_def
    have hsum : α = Γ + δ := by rw [hδ_def]; ring
    have hδlow : ∀ i < m + 1, PowerSeries.coeff i δ = 0 := by
      intro i hi
      rw [hδ_def, map_sub, hα, hΓ, mk_bSeq_coeff_eq x₀ R m i (by omega), sub_self]
    have hstable := coeff_evalR_stable x₀ R (m+1) m (by omega) Γ δ hδlow
    rw [hsum, hstable]
    exact root_bSeq x₀ R hinit hzeta m m (le_refl m)

theorem gammaOfNumerators_eq_gammaFromAlpha (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    gammaOfNumerators x₀ R H hHyp βseq = gammaFromAlpha H αseq := by
  unfold HasNumeratorShape at hshape
  unfold gammaOfNumerators gammaFromAlpha
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  exact hshape n

noncomputable def henselCoeffResidual (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (αseq : ℕ → 𝕃 H) (t : ℕ) : 𝕃 H :=
  PowerSeries.coeff (t + 1) (evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq)) -
    ζ R x₀ H * αseq (t + 1)

theorem hensel_numerator_sequence_of_alpha_shape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    IsHenselNumeratorSequence x₀ R H hHyp βseq := by
  unfold IsHenselNumeratorSequence
  constructor
  · rw [hshape 0]
    exact hα0
  · rw [gammaOfNumerators_eq_gammaFromAlpha x₀ R H hHyp αseq βseq hshape]
    exact hroot

theorem mk_H_tilde_eq_W_pow_mul_eval2 (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)] :
    (Ideal.Quotient.mk (Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F)))) (H_tilde H) : 𝕃 H) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (H.natDegree - 1) *
        Polynomial.eval₂ (liftToFunctionField (H := H))
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) H := by
  unfold liftToFunctionField functionFieldT coeffAsRatFunc
  unfold H_tilde
  simp only [Polynomial.coeff_natDegree, ToRatFunc.bivPolyHom, Polynomial.coe_mapRingHom,
    Polynomial.map_C, RingHom.comp_apply]
  let Wp : Polynomial (RatFunc F) := Polynomial.C (univPolyHom (F := F) H.leadingCoeff)
  let I : Ideal (Polynomial (RatFunc F)) := Ideal.span ({Wp ^ (H.natDegree - 1) * Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / Wp) H} : Set (Polynomial (RatFunc F)))
  let q : Polynomial (RatFunc F) →+* 𝕃 H := Ideal.Quotient.mk I
  have hW_ne : univPolyHom (F := F) H.leadingCoeff ≠ 0 := by
    intro h
    exact (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt _H_natDegree_pos.out))
      (univPolyHom_injective (F := F) (by simpa using h))
  have hdiv : q (Polynomial.X / Wp) = q Polynomial.X / q Wp := by
    dsimp [Wp]
    rw [Polynomial.div_C]
    rw [map_mul]
    rw [div_eq_mul_inv]
    congr 1
    have hmul : q (Polynomial.C (univPolyHom (F := F) H.leadingCoeff)) *
        q (Polynomial.C ((univPolyHom (F := F) H.leadingCoeff)⁻¹)) = 1 := by
      rw [← map_mul, ← Polynomial.C_mul]
      rw [mul_inv_cancel₀ hW_ne]
      exact map_one q
    exact (inv_eq_of_mul_eq_one_right hmul).symm
  change q (Wp ^ (H.natDegree - 1) * Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F))) (Polynomial.X / Wp) H) = q Wp ^ (H.natDegree - 1) * Polynomial.eval₂ (q.comp ((Polynomial.mapRingHom (univPolyHom (F := F))).comp Polynomial.C)) (q Polynomial.X / q Wp) H
  rw [map_mul, map_pow]
  rw [← hdiv]
  rw [Polynomial.hom_eval₂]
  have hhom : q.comp (RingHom.comp Polynomial.C (univPolyHom (F := F)) : F[X] →+* Polynomial (RatFunc F)) =
      q.comp ((Polynomial.mapRingHom (univPolyHom (F := F))).comp Polynomial.C) := by
    ext p <;> simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
  rw [hhom]

theorem H_eval2_T_div_W_eq_zero (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)] :
    Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) H = 0 := by
  have hzero : (Ideal.Quotient.mk (Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F)))) (H_tilde H) : 𝕃 H) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  rw [mk_H_tilde_eq_W_pow_mul_eval2] at hzero
  have hW : liftToFunctionField (H := H) H.leadingCoeff ^ (H.natDegree - 1) ≠ 0 := by
    exact pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  exact (mul_eq_zero.mp hzero).resolve_left hW

theorem initial_root_at_x0 (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) R) = 0 := by
  classical
  rcases hHyp.dvd_evalX with ⟨Q, hQ⟩
  rw [hQ, Polynomial.eval₂_mul]
  rw [H_eval2_T_div_W_eq_zero H, zero_mul]

theorem zeta_ne_zero_of_Hypotheses (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    ζ R x₀ H ≠ 0 := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R
  let t : 𝕃 H := functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff
  have hroot : Polynomial.eval₂ (liftToFunctionField (H := H)) t P = 0 := by
    simpa [P, t] using initial_root_at_x0 x₀ R H hHyp
  have hderiv_evalX : Bivariate.evalX (Polynomial.C x₀) R.derivative = P.derivative := by
    ext i
    simp [P, derivative_evalX_coeff, Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one]
  have hne : Polynomial.eval₂ (liftToFunctionField (H := H)) t P.derivative ≠ 0 := by
    exact hHyp.separable_evalX.eval₂_derivative_ne_zero (liftToFunctionField (H := H)) hroot
  simpa [ζ, P, t, hderiv_evalX] using hne

theorem exists_hensel_alpha_sequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    ∃ αseq : ℕ → 𝕃 H,
      αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
      evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0 := by
  exact formalHenselAlphaSequence x₀ R H (initial_root_at_x0 x₀ R H hHyp) (zeta_ne_zero_of_Hypotheses x₀ R H hHyp)

/-- Predicate: all coefficients of a power series over `𝕃 H` are regular (lie in the image of
`𝒪 H`). This abstracts the "regular power series" used throughout the Hensel clearing argument. -/
def AllCoeffRegular (H : F[X][Y]) (φ : PowerSeries (𝕃 H)) : Prop :=
  ∀ n, PowerSeries.coeff n φ ∈ regularElementsSet H

theorem AllCoeffRegular.add {H : F[X][Y]} {φ ψ : PowerSeries (𝕃 H)}
    (hφ : AllCoeffRegular H φ) (hψ : AllCoeffRegular H ψ) :
    AllCoeffRegular H (φ + ψ) := by
  intro n; rw [map_add]; exact regularElementsSet_add (hφ n) (hψ n)

theorem AllCoeffRegular.mul {H : F[X][Y]} {φ ψ : PowerSeries (𝕃 H)}
    (hφ : AllCoeffRegular H φ) (hψ : AllCoeffRegular H ψ) :
    AllCoeffRegular H (φ * ψ) := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply regularElementsSet_sum
  intro p _
  exact regularElementsSet_mul (hφ p.1) (hψ p.2)

theorem AllCoeffRegular.pow {H : F[X][Y]} {φ : PowerSeries (𝕃 H)}
    (hφ : AllCoeffRegular H φ) (m : ℕ) :
    AllCoeffRegular H (φ ^ m) := by
  induction m with
  | zero =>
      intro n; rw [pow_zero, PowerSeries.coeff_one]; split
      · exact regularElementsSet_one H
      · exact regularElementsSet_zero H
  | succ m ih => rw [pow_succ]; exact ih.mul hφ

theorem AllCoeffRegular.const {H : F[X][Y]} {c : 𝕃 H} (hc : c ∈ regularElementsSet H) :
    AllCoeffRegular H (PowerSeries.C c) := by
  intro n; rw [PowerSeries.coeff_C]; split
  · exact hc
  · exact regularElementsSet_zero H

theorem AllCoeffRegular.X {H : F[X][Y]} : AllCoeffRegular H (PowerSeries.X) := by
  intro n; rw [PowerSeries.coeff_X]; split
  · exact regularElementsSet_one H
  · exact regularElementsSet_zero H

theorem AllCoeffRegular.zero {H : F[X][Y]} :
    AllCoeffRegular H (0 : PowerSeries (𝕃 H)) := by
  intro n; rw [map_zero]; exact regularElementsSet_zero H

/-- The image of a field constant `x₀ : F` in `𝕃 H` is a regular element. -/
theorem fieldTo𝕃_regular (x₀ : F) (H : F[X][Y]) :
    fieldTo𝕃 (H := H) x₀ ∈ regularElementsSet H := by
  show RingHom.comp liftToFunctionField Polynomial.C x₀ ∈ regularElementsSet H
  rw [RingHom.comp_apply]
  exact regularElementsSet_liftToFunctionField H _

/-- Every coefficient of `liftCoeffToPowerSeries x₀ H p` is regular: the construction only uses
`liftToFunctionField`-images of `F[X]`-coefficients, the regular constant `x₀`, and the
power-series variable, all of which preserve regularity. -/
theorem coeff_liftCoeff_regular (x₀ : F) (H : F[X][Y]) (p : F[X][X]) :
    AllCoeffRegular H (liftCoeffToPowerSeries x₀ H p) := by
  classical
  have heq : liftCoeffToPowerSeries x₀ H p =
      Polynomial.eval₂ (RingHom.comp PowerSeries.C (liftToFunctionField (H := H)))
        (PowerSeries.C (fieldTo𝕃 (H := H) x₀) + PowerSeries.X) p := rfl
  rw [heq, Polynomial.eval₂_eq_sum_range]
  apply Finset.sum_induction _ (AllCoeffRegular H) (fun _ _ => AllCoeffRegular.add)
    AllCoeffRegular.zero
  intro m _
  apply AllCoeffRegular.mul
  · rw [RingHom.comp_apply]
    exact AllCoeffRegular.const (regularElementsSet_liftToFunctionField H _)
  · exact AllCoeffRegular.pow
      ((AllCoeffRegular.const (fieldTo𝕃_regular x₀ H)).add AllCoeffRegular.X) m

/-- **Residual simplification** (paper A.4): replacing `αseq` by its truncation `αtrunc i =
if i ≤ t then αseq i else 0` cancels the linear term `ζ · αseq (t+1)` exactly. Hence the Hensel
residual at step `t` equals the `(t+1)`-st coefficient of `R` evaluated at the *truncated*
power series. This uses only the splitting lemma `coeff_evalR_split`; `hroot` is not needed. -/
theorem henselCoeffResidual_eq_trunc (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (t : ℕ) :
    henselCoeffResidual x₀ R H αseq t =
      PowerSeries.coeff (t + 1)
        (evalRAtPowerSeries x₀ H R
          (PowerSeries.mk (fun i => if i ≤ t then αseq i else 0))) := by
  classical
  unfold henselCoeffResidual gammaFromAlpha
  set αtrunc : ℕ → 𝕃 H := fun i => if i ≤ t then αseq i else 0 with hαtrunc
  set δ : PowerSeries (𝕃 H) := PowerSeries.mk αseq - PowerSeries.mk αtrunc with hδ_def
  have hsum : PowerSeries.mk αseq = PowerSeries.mk αtrunc + δ := by rw [hδ_def]; ring
  have hδlow : ∀ i < t + 1, PowerSeries.coeff i δ = 0 := by
    intro i hi
    rw [hδ_def, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk, hαtrunc]
    simp only []
    rw [if_pos (by omega)]; ring
  have hδtop : PowerSeries.coeff (t + 1) δ = αseq (t + 1) := by
    rw [hδ_def, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk, hαtrunc]
    simp only []
    rw [if_neg (by omega)]; ring
  have hΓ0 : PowerSeries.constantCoeff (PowerSeries.mk αtrunc) =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hαtrunc]
    simp only []
    rw [if_pos (by omega), hα0]
  rw [hsum, coeff_evalR_split x₀ R (t + 1) (by omega) (PowerSeries.mk αtrunc) δ hδlow hΓ0,
    hδtop]
  ring

/-- **Per-degree clearing lemma** (paper A.4 core combinatorial bound).

For the truncated power series `g = mk αtrunc` whose nonzero coefficients (`i ≤ t`) have the
Hensel shape `αtrunc i = embeddingOf𝒪Into𝕃 (βprev ⟨i⟩) / (W^{i+1} · eta^{e_i})` with `βprev`
regular and `e_i = henselDenominatorExponent i`, each degree-`j` summand of the expansion of
`coeff (t+1) (eval₂ liftCoeff g R)`, after multiplication by the global clearing denominator
`Ddiv = W^{t+2} · eta^{E-1} · W^{d-2}`, is a regular element.

This is the combinatorial heart of [BCIKS20] Appendix A.4 (pp. 52–53). The denominator of a
partition term with `∑ iₗ = b ≤ t+1` over `j` parts is `W^{b+j} · eta^{∑ e_{iₗ}}`; the
exponent bounds `∑ e_{iₗ} ≤ E-1 = 2t` and (for `b ≤ t`) `b+j ≤ t+d` make the leftover `W`/`eta`
powers nonnegative. The single boundary case `a = 0, b = t+1, j = R.natDegree` has a one-`W`
deficit covered by the leading-coefficient divisibility `leadingCoeff_dvd_evalX_coeff_natDegree`
(the coefficient `coeff 0 (liftCoeff (R.coeff d))` is `liftToFunctionField` of the top
coefficient of `R(x₀,·)`, which is divisible by `W`). The leftover `eta = W^{d-2}·ζ` factors
and `embeddingOf𝒪Into𝕃_ξ` close the regularity. -/
theorem henselClearedTerm_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (t : ℕ) (βprev : Fin (t + 1) → 𝒪 H)
    (αtrunc : ℕ → 𝕃 H)
    (hshape : ∀ i : ℕ, αtrunc i =
      if h : i ≤ t then
        embeddingOf𝒪Into𝕃 H (βprev ⟨i, by omega⟩) /
          (liftToFunctionField (H := H) H.leadingCoeff ^ (i + 1) *
            (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent i)
      else 0)
    (j : ℕ) (hj : j ∈ Finset.range (R.natDegree + 1)) :
    PowerSeries.coeff (t + 1)
        (liftCoeffToPowerSeries x₀ H (R.coeff j) * (PowerSeries.mk αtrunc) ^ j) *
      (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
        (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ (henselDenominatorExponent (t + 1) - 1) *
        liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2)) ∈
      regularElementsSet H := by
  classical
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hWdef
  set eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp) with hetadef
  have hWne : W ≠ 0 := liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hetane : eta ≠ 0 := by
    rw [hetadef, embeddingOf𝒪Into𝕃_ξ]
    exact mul_ne_zero (pow_ne_zero _ hWne) (zeta_ne_zero_of_Hypotheses x₀ R H hHyp)
  have hjle : j ≤ R.natDegree := by
    rw [Finset.mem_range] at hj; omega
  -- regularity of cleared numerators (clearing the denominator of each `αtrunc i`, `i ≤ t`)
  have hnumReg : ∀ i, i ≤ t →
      αtrunc i * (W ^ (i + 1) * eta ^ henselDenominatorExponent i) ∈ regularElementsSet H := by
    intro i hi
    rw [hshape i, dif_pos hi, hWdef, hetadef,
      div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hWne) (pow_ne_zero _ hetane))]
    exact ⟨βprev ⟨i, by omega⟩, rfl⟩
  -- `αtrunc` vanishes above the truncation point
  have hαzero : ∀ i, t < i → αtrunc i = 0 := by
    intro i hi; rw [hshape i, dif_neg (by omega)]
  -- Step: distribute `coeff_mul` and `coeff_pow`, reduce to a single composition `l`.
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply regularElementsSet_sum
  intro p _hp
  rw [PowerSeries.coeff_pow]
  simp only [PowerSeries.coeff_mk]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply regularElementsSet_sum
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  have hbsum : (∑ i ∈ Finset.range j, l i) = p.2 := hl.1
  have hcoeffReg : PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j))
      ∈ regularElementsSet H := coeff_liftCoeff_regular x₀ H (R.coeff j) p.1
  have hab : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp _hp
  -- Case A: some part exceeds `t`  ⇒  the product has a zero factor.
  by_cases hbig : ∃ i ∈ Finset.range j, t < l i
  · obtain ⟨i₀, hi₀, hi₀t⟩ := hbig
    have hz : (∏ i ∈ Finset.range j, αtrunc (l i)) = 0 :=
      Finset.prod_eq_zero hi₀ (hαzero _ hi₀t)
    rw [hz]
    simpa using regularElementsSet_zero H
  · -- Case B: all parts `≤ t`.
    push_neg at hbig
    have hle : ∀ i ∈ Finset.range j, l i ≤ t := hbig
    -- product-clearing: `(∏ αtrunc) · W^{∑(lᵢ+1)} · eta^{∑e} ∈ regular`
    have hprodReg : (∏ i ∈ Finset.range j, αtrunc (l i)) *
        (W ^ (∑ i ∈ Finset.range j, (l i + 1)) *
          eta ^ (∑ i ∈ Finset.range j, henselDenominatorExponent (l i)))
        ∈ regularElementsSet H := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact regularElementsSet_prod _ fun i hi => hnumReg (l i) (hle i hi)
    -- the eta exponent bound `∑ e ≤ E - 1 = 2t`
    have hPe : (∑ i ∈ Finset.range j, henselDenominatorExponent (l i)) ≤
        henselDenominatorExponent (t + 1) - 1 := by
      set Pe := (∑ i ∈ Finset.range j, henselDenominatorExponent (l i)) with hPedef
      set S1 := (∑ i ∈ Finset.range j, (if l i = 0 then 0 else 1)) with hS1def
      have h2b : 2 * p.2 = Pe + S1 := by
        rw [hPedef, hS1def, ← hbsum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by
          unfold henselDenominatorExponent; split <;> omega
      have hbS1 : p.2 ≤ t * S1 := by
        rw [← hbsum, hS1def, Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        split
        · next h => rw [h]; simp
        · next h => rw [Nat.mul_one]; exact hle i hi
      have hE1 : henselDenominatorExponent (t + 1) - 1 = 2 * t := by
        rw [henselDenominatorExponent_succ]; omega
      rw [hE1]
      rcases Nat.lt_or_ge p.2 (t + 1) with hbt | hbt
      · omega
      · have hS1ge : 2 ≤ S1 := by
          by_contra h
          push_neg at h
          interval_cases S1 <;> omega
        omega
    -- `Pw = ∑(lᵢ + 1) = p.2 + j`
    have hPweq : (∑ i ∈ Finset.range j, (l i + 1)) = p.2 + j := by
      rw [Finset.sum_add_distrib, hbsum]; simp
    set Pw := (∑ i ∈ Finset.range j, (l i + 1)) with hPwdef
    set Pe := (∑ i ∈ Finset.range j, henselDenominatorExponent (l i)) with hPedef
    set E1 := henselDenominatorExponent (t + 1) - 1 with hE1def
    -- helper: given a `W`-budget `wb ≥ Pw` and a regular `cf`, finish.
    have finish_with : ∀ (cf : 𝕃 H) (wb : ℕ),
        cf ∈ regularElementsSet H → Pw ≤ wb →
        cf * ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
          (W ^ (wb - Pw) * eta ^ (E1 - Pe)) ∈ regularElementsSet H := by
      intro cf wb hcf _hwb
      refine regularElementsSet_mul (regularElementsSet_mul hcf hprodReg) ?_
      exact regularElementsSet_mul
        (by rw [hWdef]; exact regularElementsSet_pow (regularElementsSet_liftToFunctionField H _) _)
        (by rw [hetadef]; exact regularElementsSet_pow ⟨_, rfl⟩ _)
    -- boundary detection
    by_cases hbdry : p.2 = t + 1 ∧ j = R.natDegree ∧ 2 ≤ R.natDegree
    · -- boundary: `p.1 = 0`, `j = d`, `d ≥ 2`; one extra `W` comes from the leading-coeff
      -- divisibility `W ∣ coeff 0 (liftCoeff (R.coeff d))`.
      obtain ⟨hb, hjeq, hdge⟩ := hbdry
      have ha0 : p.1 = 0 := by omega
      -- coeff 0 (liftCoeff (R.coeff d)) = W * q, q regular
      have hWdvd : ∃ q : 𝕃 H, q ∈ regularElementsSet H ∧
          PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) = W * q := by
        rw [ha0, hjeq, PowerSeries.coeff_zero_eq_constantCoeff_apply,
          constantCoeff_liftCoeffToPowerSeries]
        have hcoeff : (R.coeff R.natDegree).eval (Polynomial.C x₀) =
            (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
        rw [hcoeff]
        obtain ⟨c, hc⟩ := leadingCoeff_dvd_evalX_coeff_natDegree hHyp
        rw [hc, map_mul]
        exact ⟨liftToFunctionField (H := H) c, regularElementsSet_liftToFunctionField H c, by
          rw [hWdef]⟩
      obtain ⟨q, hqReg, hqeq⟩ := hWdvd
      -- W-budget: total available `W` power is `(t+2) + (d-2) + 1` (the `+1` from `q`'s `W`).
      have hbudget : Pw ≤ (t + 1 + 1) + (R.natDegree - 2) + 1 := by
        rw [hPweq]; omega
      -- rewrite Ddiv with the extra `W` from `coeffReg = W * q`
      rw [hqeq]
      have hreassoc :
          (W * q) * (∏ i ∈ Finset.range j, αtrunc (l i)) *
              (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
          q * ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
            (W ^ (((t + 1 + 1) + (R.natDegree - 2) + 1) - Pw) * eta ^ (E1 - Pe)) := by
        have hwsplit : ((t + 1 + 1) + (R.natDegree - 2) + 1) =
            Pw + (((t + 1 + 1) + (R.natDegree - 2) + 1) - Pw) := by omega
        have hesplit : E1 = Pe + (E1 - Pe) := by omega
        rw [show (W * q) * (∏ i ∈ Finset.range j, αtrunc (l i)) *
              (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
            q * ((∏ i ∈ Finset.range j, αtrunc (l i)) *
              (W ^ ((t + 1 + 1) + (R.natDegree - 2) + 1) * eta ^ E1)) by ring]
        conv_lhs => rw [hwsplit, hesplit, pow_add, pow_add]
        ring
      rw [hreassoc]
      exact finish_with q _ hqReg hbudget
    · -- non-boundary: the `W`-budget `(t+2)+(d-2)` already covers `Pw = p.2 + j`.
      have hbudget : Pw ≤ (t + 1 + 1) + (R.natDegree - 2) := by
        rw [hPweq]
        rw [Finset.mem_range] at hj
        -- `¬(p.2 = t+1 ∧ j = d ∧ 2 ≤ d)`; with `p.2 ≤ t+1`, `j ≤ d`
        rcases Nat.lt_or_ge R.natDegree 2 with hd | hd
        · omega
        · -- d ≥ 2:  the negated boundary forces `p.2 ≤ t` or `j ≤ d - 1`
          rcases not_and_or.mp hbdry with h1 | h2
          · -- p.2 ≠ t+1, so p.2 ≤ t
            omega
          · rcases not_and_or.mp h2 with h3 | h4
            · -- j ≠ R.natDegree, so j ≤ d - 1
              omega
            · exact absurd hd h4
      -- rewrite Ddiv directly
      have hreassoc :
          PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
          PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) *
            ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
            (W ^ (((t + 1 + 1) + (R.natDegree - 2)) - Pw) * eta ^ (E1 - Pe)) := by
        have hwsplit : ((t + 1 + 1) + (R.natDegree - 2)) =
            Pw + (((t + 1 + 1) + (R.natDegree - 2)) - Pw) := by omega
        have hesplit : E1 = Pe + (E1 - Pe) := by omega
        rw [show PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
            PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) *
              ((∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ ((t + 1 + 1) + (R.natDegree - 2)) * eta ^ E1)) by ring]
        conv_lhs => rw [hwsplit, hesplit, pow_add, pow_add]
        ring
      rw [hreassoc]
      exact finish_with _ _ hcoeffReg hbudget

theorem henselCoeffResidual_regular_after_clearing (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hzeta : ζ R x₀ H ≠ 0)
    (t : ℕ) (βprev : Fin (t + 1) → 𝒪 H)
    (hprev : ∀ i : Fin (t + 1),
      embeddingOf𝒪Into𝕃 H (βprev i) /
        (liftToFunctionField (H := H) H.leadingCoeff ^ (i.val + 1) *
          (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent i.val) =
        αseq i.val) :
    let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
    let eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)
    let E : ℕ := henselDenominatorExponent (t + 1)
    let Ddiv : 𝕃 H := W ^ (t + 1 + 1) * eta ^ (E - 1) * W ^ (R.natDegree - 2)
    henselCoeffResidual x₀ R H αseq t * Ddiv ∈ regularElementsSet H := by
  -- Residual-regularity (paper A.4). Step 1 (`henselCoeffResidual_eq_trunc`): the residual is
  -- the `(t+1)`-st coefficient of `R` evaluated at the truncated series `mk αtrunc` (the linear
  -- term `ζ · α(t+1)` cancels exactly). Step 2: expand `eval₂ liftCoeff (mk αtrunc) R` as a
  -- finite sum over `j`, distribute `Ddiv`, and apply the per-degree clearing lemma
  -- `henselClearedTerm_regular` to each summand.
  classical
  intro W eta E Ddiv
  set αtrunc : ℕ → 𝕃 H := fun i => if i ≤ t then αseq i else 0 with hαtrunc
  rw [henselCoeffResidual_eq_trunc x₀ R H αseq hα0 t]
  -- shape of `αtrunc` from `hprev`
  have hshape : ∀ i : ℕ, αtrunc i =
      if h : i ≤ t then
        embeddingOf𝒪Into𝕃 H (βprev ⟨i, by omega⟩) /
          (liftToFunctionField (H := H) H.leadingCoeff ^ (i + 1) *
            (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent i)
      else 0 := by
    intro i
    by_cases h : i ≤ t
    · have hval : αtrunc i = αseq i := by rw [hαtrunc]; simp only [if_pos h]
      rw [hval, dif_pos h]
      have := hprev ⟨i, by omega⟩
      simpa using this.symm
    · have hval : αtrunc i = 0 := by rw [hαtrunc]; simp only [if_neg h]
      rw [hval, dif_neg h]
  show PowerSeries.coeff (t + 1)
      (evalRAtPowerSeries x₀ H R (PowerSeries.mk αtrunc)) * Ddiv ∈ regularElementsSet H
  unfold evalRAtPowerSeries
  rw [Polynomial.eval₂_eq_sum_range, map_sum, Finset.sum_mul]
  apply regularElementsSet_sum
  intro j hj
  exact henselClearedTerm_regular x₀ R H hHyp t βprev αtrunc hshape j hj

end ClaimA2

section
variable {F : Type} [CommRing F] [IsDomain F]

omit [IsDomain F] in
/-- `Λ` is subadditive under multiplication of bivariate polynomials (bound form). -/
lemma weight_Λ_mul_le' {f g H : F[X][Y]} {D bf bg : ℕ}
    (hf : weight_Λ f H D ≤ (WithBot.some bf : WithBot ℕ))
    (hg : weight_Λ g H D ≤ (WithBot.some bg : WithBot ℕ)) :
    weight_Λ (f * g) H D ≤ (WithBot.some (bf + bg) : WithBot ℕ) := by
  classical
  rw [weight_Λ_le_iff]
  rw [weight_Λ_le_iff] at hf hg
  intro n hn
  set m := D + 1 - Bivariate.natDegreeY H with hm
  have hcoeff_ne : (f * g).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hexists : ∃ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hcoeff_ne (by rw [Polynomial.coeff_mul]; exact Finset.sum_eq_zero h)
  obtain ⟨x0, hx0mem, hx0ne⟩ := hexists
  have hx0sum : x0.1 + x0.2 = n := Finset.mem_antidiagonal.mp hx0mem
  have hfb0 := hf x0.1 (Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul hx0ne))
  have hgb0 := hg x0.2 (Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul hx0ne))
  have hnm_le : n * m ≤ bf + bg := by
    have : n * m = x0.1 * m + x0.2 * m := by rw [← hx0sum, Nat.add_mul]
    omega
  have hdeg : ((f * g).coeff n).natDegree ≤ bf + bg - n * m := by
    rw [Polynomial.coeff_mul]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro x hx
    have hxsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
    by_cases hxz : f.coeff x.1 * g.coeff x.2 = 0
    · simp [hxz]
    · have hfb := hf x.1 (Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul hxz))
      have hgb := hg x.2 (Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul hxz))
      have hprod : (f.coeff x.1 * g.coeff x.2).natDegree ≤
          (f.coeff x.1).natDegree + (g.coeff x.2).natDegree := Polynomial.natDegree_mul_le
      have hnm : n * m = x.1 * m + x.2 * m := by rw [← hxsum, Nat.add_mul]
      omega
  omega

end

namespace ClaimA2
variable {F : Type} [Field F] {R : F[X][X][X]} {H : F[X][Y]}
  [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]

/-- The `𝒪`-weight is invariant under negation. -/
lemma weight_Λ_over_𝒪_neg {hH : 0 < H.natDegree} (a : 𝒪 H) (D : ℕ) :
    weight_Λ_over_𝒪 hH (-a) D = weight_Λ_over_𝒪 hH a D := by
  classical
  have hrep : (-a) = (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
      (-(canonicalRepOf𝒪 hH a)) : 𝒪 H) := by
    rw [map_neg, mk_canonicalRepOf𝒪]
  have hdeg : (-(canonicalRepOf𝒪 hH a)).degree < (H_tilde' H).degree := by
    rw [Polynomial.degree_neg]; exact canonicalRepOf𝒪_degree_lt hH a
  rw [hrep, weight_Λ_over_𝒪_mk_eq_self_of_degree_lt hH hdeg, weight_Λ_neg]
  rfl

/-- `𝒪`-weight is subadditive under multiplication (bound form). -/
lemma weight_Λ_over_𝒪_mul_le' {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) {a b : 𝒪 H} {ba bb : ℕ}
    (ha : weight_Λ_over_𝒪 hH a D ≤ (WithBot.some ba : WithBot ℕ))
    (hb : weight_Λ_over_𝒪 hH b D ≤ (WithBot.some bb : WithBot ℕ)) :
    weight_Λ_over_𝒪 hH (a * b) D ≤ (WithBot.some (ba + bb) : WithBot ℕ) := by
  classical
  have hab : a * b = (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
      (canonicalRepOf𝒪 hH a * canonicalRepOf𝒪 hH b) : 𝒪 H) := by
    rw [map_mul, mk_canonicalRepOf𝒪, mk_canonicalRepOf𝒪]
  rw [hab]
  exact (weight_Λ_over_𝒪_mk_le hD hH _).trans (weight_Λ_mul_le' ha hb)

/-- `RegularWeightLe hH a D B`: the element `a : 𝕃 H` is regular (in the image of `𝒪 H`) with a
witness whose `Λ`-weight is at most `B`. Bundles regularity together with a weight certificate so
that the Hensel-clearing expansion can be carried out with `Λ`-bookkeeping. -/
def RegularWeightLe {H : F[X][Y]} (hH : 0 < H.natDegree) (a : 𝕃 H) (D B : ℕ) : Prop :=
  ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 H b ∧
    weight_Λ_over_𝒪 hH b D ≤ (WithBot.some B : WithBot ℕ)

lemma RegularWeightLe.mono {hH : 0 < H.natDegree} {a : 𝕃 H} {D B B' : ℕ}
    (h : RegularWeightLe hH a D B) (hBB : B ≤ B') : RegularWeightLe hH a D B' := by
  obtain ⟨b, hb, hw⟩ := h
  exact ⟨b, hb, hw.trans (by exact_mod_cast hBB)⟩

lemma RegularWeightLe.mul {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree}
    {a b : 𝕃 H} {Ba Bb : ℕ}
    (ha : RegularWeightLe hH a D Ba) (hb : RegularWeightLe hH b D Bb) :
    RegularWeightLe hH (a * b) D (Ba + Bb) := by
  obtain ⟨a', ha', hwa⟩ := ha
  obtain ⟨b', hb', hwb⟩ := hb
  exact ⟨a' * b', by rw [ha', hb', map_mul], weight_Λ_over_𝒪_mul_le' hD hH hwa hwb⟩

lemma RegularWeightLe.add {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree}
    {a b : 𝕃 H} {B : ℕ}
    (ha : RegularWeightLe hH a D B) (hb : RegularWeightLe hH b D B) :
    RegularWeightLe hH (a + b) D B := by
  obtain ⟨a', ha', hwa⟩ := ha
  obtain ⟨b', hb', hwb⟩ := hb
  exact ⟨a' + b', by rw [ha', hb', map_add],
    (weight_Λ_over_𝒪_add_le hD hH a' b').trans (max_le hwa hwb)⟩

lemma RegularWeightLe.neg {hH : 0 < H.natDegree} {a : 𝕃 H} {D B : ℕ}
    (ha : RegularWeightLe hH a D B) : RegularWeightLe hH (-a) D B := by
  obtain ⟨a', ha', hwa⟩ := ha
  exact ⟨-a', by rw [ha', map_neg], by rwa [weight_Λ_over_𝒪_neg]⟩

lemma RegularWeightLe.pow {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree}
    {a : 𝕃 H} {Ba : ℕ} (ha : RegularWeightLe hH a D Ba) (k : ℕ) :
    RegularWeightLe hH (a ^ k) D (k * Ba) := by
  induction k with
  | zero =>
      simp only [pow_zero, Nat.zero_mul]
      refine ⟨1, by rw [map_one], ?_⟩
      rw [show (1 : 𝒪 H) = (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (1 : F[X][Y]) : 𝒪 H) by simp]
      refine (weight_Λ_over_𝒪_mk_le hD hH _).trans ?_
      rw [show (1 : F[X][Y]) = Polynomial.C 1 by simp]
      exact (weight_Λ_C_le H D 1).trans (by simp)
  | succ k ih =>
      rw [pow_succ]
      refine (RegularWeightLe.mul hD ih ha).mono ?_
      ring_nf; omega

lemma RegularWeightLe.sum {ι : Type} (s : Finset ι) (f : ι → 𝕃 H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree} {B : ℕ}
    (hf : ∀ i ∈ s, RegularWeightLe hH (f i) D B) :
    RegularWeightLe hH (∑ i ∈ s, f i) D B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, by rw [map_zero, Finset.sum_empty], ?_⟩
      rw [weight_Λ_over_𝒪_zero]; exact bot_le
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact RegularWeightLe.add hD (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma RegularWeightLe.prod {ι : Type} (s : Finset ι) (f : ι → 𝕃 H) (B : ι → ℕ)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree}
    (hf : ∀ i ∈ s, RegularWeightLe hH (f i) D (B i)) :
    RegularWeightLe hH (∏ i ∈ s, f i) D (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      refine ⟨1, by rw [map_one], ?_⟩
      rw [show (1 : 𝒪 H) = (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (1 : F[X][Y]) : 𝒪 H) by simp]
      refine (weight_Λ_over_𝒪_mk_le hD hH _).trans ?_
      rw [show (1 : F[X][Y]) = Polynomial.C 1 by simp]
      exact (weight_Λ_C_le H D 1).trans (by simp)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact RegularWeightLe.mul hD (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Coefficient embeddings are regular with `Λ`-weight at most their `X`-degree. -/
lemma RWL_lift {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (c : F[X]) : RegularWeightLe hH (liftToFunctionField (H := H) c) D c.natDegree := by
  refine ⟨(Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C c) : 𝒪 H), ?_, ?_⟩
  · rw [embeddingOf𝒪Into𝕃_mk]; rfl
  · exact (weight_Λ_over_𝒪_mk_le hD hH _).trans (weight_Λ_C_le H D c)

/-- The leading coefficient lift `W` is regular with `Λ`-weight at most `D`. -/
lemma RWL_W {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    RegularWeightLe hH (liftToFunctionField (H := H) H.leadingCoeff) D D := by
  refine (RWL_lift hD hH H.leadingCoeff).mono ?_
  by_cases hHz : H = 0
  · simp [hHz]
  · have hH_in : H.natDegree ∈ H.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hHz)
    have h1 : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    rw [Polynomial.leadingCoeff]; omega

/-- The power-series variable's coefficients are regular with weight `0`. -/
lemma RWL_X {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) (n : ℕ) :
    RegularWeightLe hH (PowerSeries.coeff n (PowerSeries.X : PowerSeries (𝕃 H))) D 0 := by
  rw [PowerSeries.coeff_X]
  split
  · rw [show (1 : 𝕃 H) = liftToFunctionField (H := H) 1 by simp]
    exact (RWL_lift hD hH 1).mono (by simp)
  · rw [show (0 : 𝕃 H) = liftToFunctionField (H := H) 0 by simp]
    exact (RWL_lift hD hH 0).mono (by simp)

/-- The field constant embedding has weight `0`. -/
lemma RWL_fieldTo {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (x₀ : F) : RegularWeightLe hH (fieldTo𝕃 (H := H) x₀) D 0 := by
  rw [show fieldTo𝕃 (H := H) x₀ = liftToFunctionField (H := H) (Polynomial.C x₀) from rfl]
  exact (RWL_lift hD hH _).mono (by simp [Polynomial.natDegree_C])

/-- Coefficients of the local-coordinate binomial `(x₀ + S)^s` are weight-`0` regular. -/
lemma RWL_binom_coeff {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (x₀ : F) (s : ℕ) : ∀ n,
    RegularWeightLe hH (PowerSeries.coeff n
      ((PowerSeries.C (fieldTo𝕃 (H := H) x₀) + PowerSeries.X) ^ s)) D 0 := by
  induction s with
  | zero =>
      intro n
      rw [pow_zero, PowerSeries.coeff_one]
      split
      · rw [show (1 : 𝕃 H) = liftToFunctionField (H := H) 1 by simp]
        exact (RWL_lift hD hH 1).mono (by simp)
      · rw [show (0 : 𝕃 H) = liftToFunctionField (H := H) 0 by simp]
        exact (RWL_lift hD hH 0).mono (by simp)
  | succ s ih =>
      intro n
      rw [pow_succ, PowerSeries.coeff_mul]
      refine RegularWeightLe.sum _ _ hD ?_
      intro pr _
      have h2 : RegularWeightLe hH
          (PowerSeries.coeff pr.2 (PowerSeries.C (fieldTo𝕃 (H := H) x₀) + PowerSeries.X)) D 0 := by
        rw [map_add]
        refine RegularWeightLe.add hD ?_ (RWL_X hD hH pr.2)
        rw [PowerSeries.coeff_C]
        split
        · exact RWL_fieldTo hD hH x₀
        · rw [show (0 : 𝕃 H) = liftToFunctionField (H := H) 0 by simp]
          exact (RWL_lift hD hH 0).mono (by simp)
      exact (RegularWeightLe.mul hD (ih pr.1) h2).mono (by simp)

/-- Each coefficient of `liftCoeffToPowerSeries x₀ H p` is regular with weight at most the
total degree of `p`. -/
lemma RWL_coeff_liftCoeff {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (x₀ : F) (p : F[X][X]) (n : ℕ) :
    RegularWeightLe hH (PowerSeries.coeff n (liftCoeffToPowerSeries x₀ H p)) D
      (Bivariate.totalDegree p) := by
  classical
  unfold liftCoeffToPowerSeries
  rw [coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range, map_sum]
  refine RegularWeightLe.sum _ _ hD ?_
  intro s _
  rw [RingHom.comp_apply, PowerSeries.coeff_C_mul]
  refine (RegularWeightLe.mul hD (RWL_lift hD hH (p.coeff s))
    (RWL_binom_coeff hD hH x₀ s n)).mono ?_
  rw [Nat.add_zero]
  rcases Bivariate.coeff_totalDegree_le' p s with h | h0
  · omega
  · rw [h0]; simp

/-- Sharp `Λ`-weight bound on the leading-coefficient lift `W`: `Λ(W) ≤ D - dH`.
This is the per-`W`-factor budget used in the sharp telescoping of [BCIKS20] A.4 (pp. 52–53);
the looser `Λ(W) ≤ D` of `RWL_W` is not enough for the constant term to telescope. -/
lemma RWL_W_sharp {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) :
    RegularWeightLe hH (liftToFunctionField (H := H) H.leadingCoeff) D
      (D - H.natDegree) := by
  refine (RWL_lift hD hH H.leadingCoeff).mono ?_
  by_cases hHz : H = 0
  · simp [hHz]
  · have hH_in : H.natDegree ∈ H.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hHz)
    have h1 : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    rw [Polynomial.leadingCoeff]; omega

/-- The sharp per-step `Λ`-weight budget of [BCIKS20] A.4 (the bound on `Λ(βₜ)`):
`sharp t = 1 + (t+1)·(D - dH) + eₜ·((dY-1)·(D - dH + 1))`, where `dH = natDegreeY H`,
`dY = natDegreeY R`, and `eₜ = henselDenominatorExponent t`.  The `1` is the constant from the
leading-coefficient divisibility, `(t+1)·(D-dH)` is the `W`-power contribution, and the last term
is the `ξ`-power contribution.  This bound telescopes linearly in `t`, unlike the loose
multiplicative `(2t+1)·dY·D`. -/
def numeratorShapeSharp (R : F[X][X][Y]) (H : F[X][Y]) (D t : ℕ) : ℕ :=
  1 + (t + 1) * (D - Bivariate.natDegreeY H) +
    henselDenominatorExponent t *
      ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))

/-- The sharp bound weakens to the loose paper bound consumed by the final assembly:
`sharp t ≤ (2t+1)·dY·D`.  Pure arithmetic, using `dH ≥ 1`, `dH ≤ dY`, `dH ≤ D`, and
`eₜ ≤ 2t`. -/
lemma numeratorShapeSharp_le_loose (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D) (t : ℕ) :
    numeratorShapeSharp R H D t ≤ (2 * t + 1) * Bivariate.natDegreeY R * D := by
  -- Translate the degree facts into the bare numeric hypotheses needed by the arithmetic.
  have hdH_dY : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R :=
    H_natDegree_le_R_natDegree_of_Hypotheses hHyp
  have hdH_pos : 1 ≤ Bivariate.natDegreeY H := hH
  have hdH_D : Bivariate.natDegreeY H ≤ D := by
    have hH_in : H.natDegree ∈ H.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr
        (by rintro rfl; simp at hH))
    have h1 : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    rw [show Bivariate.natDegreeY H = H.natDegree from rfl]; omega
  have het : henselDenominatorExponent t ≤ 2 * t := by
    unfold henselDenominatorExponent; split <;> omega
  unfold numeratorShapeSharp
  set D' := D
  set dH := Bivariate.natDegreeY H with hdHdef
  set dY := Bivariate.natDegreeY R with hdYdef
  set et := henselDenominatorExponent t with hetdef
  clear_value D' dH dY et
  obtain ⟨a, rfl⟩ : ∃ a, D' = dH + a := ⟨D' - dH, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, dY = dH + b := ⟨dY - dH, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, dH = c + 1 := ⟨dH - 1, by omega⟩
  simp only [Nat.add_sub_cancel_left] at *
  rw [show c + 1 + b - 1 = c + b by omega]
  have hA : et * ((c + b) * (a + 1)) ≤ 2 * t * ((c + b) * (a + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have hRHS : (2 * t + 1) * ((c + b) + 1) * (a + 1) ≤
      (2 * t + 1) * (c + 1 + b) * (c + 1 + a) := by
    apply Nat.mul_le_mul
    · rw [show c + 1 + b = (c + b) + 1 by ring]
    · omega
  nlinarith [hA, hRHS]

theorem numerator_shape_weight_succ_le_strong (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq)
    (t : ℕ)
    (ihAll : ∀ s ≤ t,
      weight_Λ_over_𝒪 hH (βseq s) D ≤
        (WithBot.some ((2 * s + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ)) :
    weight_Λ_over_𝒪 hH (βseq (t + 1)) D ≤
      (WithBot.some ((2 * (t + 1) + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  -- Strong successor step for the weight induction (paper A.4 bound on `Λ(βₜ)`).
  --
  -- INFRASTRUCTURE (all proven above, axiom-clean and reusable):
  --   * `weight_Λ_mul_le'` / `weight_Λ_over_𝒪_mul_le'` — `Λ` is subadditive under (bivariate
  --     and `𝒪`-) multiplication;
  --   * `weight_Λ_over_𝒪_neg`;
  --   * the `RegularWeightLe` predicate bundling regularity with a `Λ`-weight certificate, with
  --     closure lemmas `.mono`, `.mul`, `.add`, `.neg`, `.pow`, `.sum`, `.prod`;
  --   * base certificates `RWL_lift`, `RWL_W` (`Λ(W) ≤ D`), `RWL_X`, `RWL_fieldTo`,
  --     `RWL_binom_coeff`, and `RWL_coeff_liftCoeff` (`Λ(coeffₙ (liftCoeff p)) ≤ totalDegree p`).
  -- With `embeddingOf𝒪Into𝕃_injective`, `regular_numerator_shape_succ`'s computation, and
  -- `henselCoeffResidual_eq_trunc`, one has
  --   `embeddingOf𝒪Into𝕃 H (βseq (t+1)) = -(henselCoeffResidual … t * Ddiv)`,
  -- and the cleared element expands (cf. `henselClearedTerm_regular`) into a finite `RegularWeightLe`
  -- combination over `j ∈ range (d+1)` and compositions `l` of `t+1`, each summand of the form
  --   `coeffₚ₁(liftCoeff (R.coeff j)) · ∏ₘ embeddingOf𝒪Into𝕃 (βseq (lₘ)) · W^{wb} · η^{eb}`.
  --
  -- REMAINING GAP (genuinely hard, not closeable with the supplied hypotheses as stated):
  -- Bounding each summand term-by-term by the closure API uses `ihAll` for each factor
  -- `embeddingOf𝒪Into𝕃 (βseq lₘ)`, giving weight `≤ (2 lₘ+1)·dY·D`. Subadditivity over the `j`
  -- factors then yields `∑ₘ (2 lₘ+1)·dY·D = (2·p.2 + j)·dY·D` for the product alone, plus the `η`
  -- contribution `eb·Λ(ξ) ≈ (2t)·dY·D`. For `t ≥ 1` this already exceeds the target
  -- `(2(t+1)+1)·dY·D`: e.g. `t=1, dY=4`, one term with two parts `lₘ=1` gives
  -- `(2·2+4)·dY·D = 8·dY·D > 5·dY·D`. The paper's *sharp* bound `Λ(βₜ) ≤ 1 + (t+1)Λ(W) + eₜΛ(ξ)`
  -- is linear in `t` only because the `β`-contributions telescope through the `W`/`η`-exponents
  -- rather than appearing as an independent product of the loose `(2s+1)dY D` per-`β` bounds.
  -- Closing this faithfully requires reproducing that sharp accounting (tracking the separate
  -- `X`-degree and `Y`-degree contributions of the cleared element through the `%ₘ H_tilde'`
  -- reduction), which the loose multiplicative `ihAll` route cannot supply. This is the one
  -- remaining, precisely-characterized gap; everything else around it is proven above.
  sorry

theorem numerator_shape_weight_bound (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    ∀ t : ℕ,
      weight_Λ_over_𝒪 hH (βseq t) D ≤
        (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  intro t
  exact Nat.strong_induction_on t (fun t ih => by
    cases t with
    | zero =>
        have hβ0 := beta_zero_eq_X_of_shape x₀ R H hHyp hH hD_H hD_R αseq βseq hα0 hroot hshape
        rw [hβ0]
        refine (weight_Λ_over_𝒪_mk_le (H := H) (D := D) hD_H hH (Polynomial.X : F[X][Y])).trans ?_
        have hX : weight_Λ (Polynomial.X : F[X][Y]) H D ≤
            (WithBot.some (D + 1 - Bivariate.natDegreeY H) : WithBot ℕ) := by
          simpa only [pow_one, one_mul] using (weight_Λ_X_pow_le (H := H) (D := D) (k := 1))
        refine hX.trans ?_
        rw [WithBot.coe_le_coe]
        rw [show 2 * 0 + 1 = 1 by norm_num, one_mul]
        have hYpos : 0 < Bivariate.natDegreeY H := by
          exact hH
        have hH_le_R : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R := by
          exact H_natDegree_le_R_natDegree_of_Hypotheses hHyp
        have hR_pos : 0 < Bivariate.natDegreeY R := lt_of_lt_of_le hYpos hH_le_R
        have hDsub : D + 1 - Bivariate.natDegreeY H ≤ D := by
          omega
        exact le_trans hDsub (Nat.le_mul_of_pos_left D hR_pos)
    | succ t =>
        have hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) := by
          exact evalX_totalDegree_le_of_coeff_bound x₀ R hD_R
        exact numerator_shape_weight_succ_le_strong x₀ R H hHyp hH hD_H hD_R hD_Rx0 αseq βseq hα0 hroot hshape t (by
          intro s hs
          exact ih s (Nat.lt_succ_of_le hs)))

theorem regular_numerator_shape_succ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hzeta : ζ R x₀ H ≠ 0)
    (t : ℕ) (βprev : Fin (t + 1) → 𝒪 H)
    (hprev : ∀ i : Fin (t + 1),
      embeddingOf𝒪Into𝕃 H (βprev i) /
        (liftToFunctionField (H := H) H.leadingCoeff ^ (i.val + 1) *
          (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent i.val) =
        αseq i.val) :
    ∃ βnext : 𝒪 H,
      embeddingOf𝒪Into𝕃 H βnext /
        (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
          (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent (t + 1)) =
        αseq (t + 1) := by
  classical
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)
  let E : ℕ := henselDenominatorExponent (t + 1)
  let D : 𝕃 H := W ^ (t + 1 + 1) * eta ^ E
  let Ddiv : 𝕃 H := W ^ (t + 1 + 1) * eta ^ (E - 1) * W ^ (R.natDegree - 2)
  let S : 𝕃 H :=
    PowerSeries.coeff (t + 1) (evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq)) -
      ζ R x₀ H * αseq (t + 1)
  have hSreg : S * Ddiv ∈ regularElementsSet H := by
    exact henselCoeffResidual_regular_after_clearing x₀ R H hHyp αseq hα0 hroot hzeta t βprev hprev
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have heta : eta ≠ 0 := by
    have hξeq := embeddingOf𝒪Into𝕃_ξ x₀ R H hHyp
    simpa [eta, W, hξeq] using mul_ne_zero (pow_ne_zero (R.natDegree - 2) hW) hzeta
  have hD : D ≠ 0 := by
    simp only [D]
    exact mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ heta)
  have hcoeff : PowerSeries.coeff (t + 1) (evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq)) = 0 := by
    simpa using congrArg (fun p : PowerSeries (𝕃 H) => PowerSeries.coeff (t + 1) p) hroot
  have hS : S = - ζ R x₀ H * αseq (t + 1) := by
    simp only [S, hcoeff, zero_sub]
    ring
  have hEpos : 0 < E := by
    dsimp [E]
    rw [henselDenominatorExponent_succ]
    omega
  have hE : E = (E - 1) + 1 := by omega
  have hpeta : eta ^ E = eta ^ (E - 1) * eta := by
    conv_lhs => rw [hE, pow_succ]
  have hD_eq : D = ζ R x₀ H * Ddiv := by
    have heta_eq : eta = W ^ (R.natDegree - 2) * ζ R x₀ H := by
      simpa [eta, W] using embeddingOf𝒪Into𝕃_ξ x₀ R H hHyp
    calc
      D = W ^ (t + 1 + 1) * eta ^ E := rfl
      _ = W ^ (t + 1 + 1) * (eta ^ (E - 1) * eta) := by
        rw [hpeta]
      _ = W ^ (t + 1 + 1) * (eta ^ (E - 1) * (W ^ (R.natDegree - 2) * ζ R x₀ H)) := by
        exact congrArg (fun x => W ^ (t + 1 + 1) * (eta ^ (E - 1) * x)) heta_eq
      _ = ζ R x₀ H * (W ^ (t + 1 + 1) * eta ^ (E - 1) * W ^ (R.natDegree - 2)) := by
        ring
      _ = ζ R x₀ H * Ddiv := rfl
  have hprod_eq : αseq (t + 1) * D = -(S * Ddiv) := by
    rw [hD_eq, hS]
    ring
  have hregProd : αseq (t + 1) * D ∈ regularElementsSet H := by
    rw [hprod_eq]
    exact regularElementsSet_neg hSreg
  rcases hregProd with ⟨βnext, hβnext⟩
  refine ⟨βnext, ?_⟩
  have hβnext' : (embeddingOf𝒪Into𝕃 H) βnext = αseq (t + 1) * D := hβnext.symm
  rw [hβnext']
  change (αseq (t + 1) * D) / D = αseq (t + 1)
  exact mul_div_cancel_right₀ (αseq (t + 1)) hD

theorem exists_regular_numerator_shape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0) :
    ∃ βseq : ℕ → 𝒪 H,
      HasNumeratorShape x₀ R H hHyp αseq βseq := by
  classical
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let Xi : 𝕃 H := embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)
  let shapeAt : ℕ → 𝒪 H → Prop := fun t β =>
    embeddingOf𝒪Into𝕃 H β / (W ^ (t + 1) * Xi ^ henselDenominatorExponent t) = αseq t
  have hprefix : ∀ n : ℕ, ∃ βpref : Fin (n + 1) → 𝒪 H, ∀ i : Fin (n + 1), shapeAt i.val (βpref i) := by
    intro n
    induction n with
    | zero =>
        let β0 : 𝒪 H := (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) : 𝒪 H)
        refine ⟨fun _ => β0, ?_⟩
        intro i
        have hi : i.val = 0 := by omega
        rw [hi]
        unfold shapeAt
        rw [hα0]
        simp [β0, W, Xi, div_eq_mul_inv]
    | succ n ih =>
        rcases ih with ⟨βpref, hβpref⟩
        have hnext : ∃ βnext : 𝒪 H, shapeAt (n + 1) βnext := by
          unfold shapeAt
          exact regular_numerator_shape_succ x₀ R H hHyp αseq hα0 hroot
            (zeta_ne_zero_of_Hypotheses x₀ R H hHyp) n βpref (by
              intro i
              exact hβpref i)
        rcases hnext with ⟨βnext, hβnext⟩
        refine ⟨fun i => if hlt : i.val < n + 1 then βpref ⟨i.val, hlt⟩ else βnext, ?_⟩
        intro i
        by_cases hlt : i.val < n + 1
        · simp [hlt]
          exact hβpref ⟨i.val, hlt⟩
        · have hval : i.val = n + 1 := by
            have hi_lt : i.val < n + 1 + 1 := i.isLt
            omega
          simp [hlt, hval]
          exact hβnext
  let βseq : ℕ → 𝒪 H := fun t => (Classical.choose (hprefix t)) ⟨t, Nat.lt_succ_self t⟩
  refine ⟨βseq, ?_⟩
  intro t
  unfold HasNumeratorShape at *
  unfold alphaOfNumerators
  change shapeAt t (βseq t)
  unfold βseq
  exact (Classical.choose_spec (hprefix t)) ⟨t, Nat.lt_succ_self t⟩

/-- There is a sequence of regular numerators `β_t` with the Hensel-lift semantics and the
weight bound stated in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
lemma exists_hensel_numerator_sequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D) :
    ∃ βseq : ℕ → 𝒪 H,
      IsHenselNumeratorSequence x₀ R H hHyp βseq ∧
      ∀ t : ℕ,
        weight_Λ_over_𝒪 hH (βseq t) D ≤
          (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  rcases exists_hensel_alpha_sequence x₀ R H hHyp with ⟨αseq, hα0, hroot⟩
  rcases exists_regular_numerator_shape x₀ R H hHyp αseq hα0 hroot with ⟨βseq, hshape⟩
  refine ⟨βseq, ?_, ?_⟩
  · exact hensel_numerator_sequence_of_alpha_shape x₀ R H hHyp αseq βseq hα0 hroot hshape
  · exact numerator_shape_weight_bound x₀ R H hHyp hH hD_H hD_R αseq βseq hα0 hroot hshape

/-- The chosen regular numerator sequence supplied by `exists_hensel_numerator_sequence`. -/
noncomputable def βSeq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) : ℕ → 𝒪 H :=
  if hH : 0 < H.natDegree then
    (exists_hensel_numerator_sequence x₀ R H hHyp hH
      (defaultDegreeBound_ge_H R H) (fun _ hi => defaultDegreeBound_ge_R_coeff R H hi)).choose
  else
    fun _ => 0

/-- The specification satisfied by the chosen numerator sequence. -/
lemma βSeq_spec (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) :
    IsHenselNumeratorSequence x₀ R H hHyp (βSeq x₀ R H hHyp) ∧
      ∀ t : ℕ,
        weight_Λ_over_𝒪 hH ((βSeq x₀ R H hHyp) t) (defaultDegreeBound R H) ≤
          (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * defaultDegreeBound R H) :
            WithBot ℕ) := by
  unfold βSeq
  rw [dif_pos hH]
  exact (exists_hensel_numerator_sequence x₀ R H hHyp hH
    (defaultDegreeBound_ge_H R H) (fun _ hi => defaultDegreeBound_ge_R_coeff R H hi)).choose_spec

/-- The regular element `β_t` giving the numerator of the `t`-th chosen Hensel coefficient. -/
noncomputable def β (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝒪 H :=
  βSeq x₀ R H hHyp t

/-- The chosen Hensel-lift coefficients induced by the regular numerator sequence. -/
def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  alphaOfNumerators x₀ R H hHyp (βSeq x₀ R H hHyp) t

/-- Variant of `α` taking explicit irreducibility and positive-degree hypotheses. -/
def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp t

/-- The chosen power series `γ = ∑ α_t (X - x₀)^t`, induced by the selected regular numerator
sequence from `exists_hensel_numerator_sequence`. -/
def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    PowerSeries (𝕃 H) :=
  gammaOfNumerators x₀ R H hHyp (βSeq x₀ R H hHyp)

/-- Variant of `γ` taking explicit irreducibility and positive-degree hypotheses. -/
def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) : PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp

end ClaimA2
end
end BCIKS20AppendixA
