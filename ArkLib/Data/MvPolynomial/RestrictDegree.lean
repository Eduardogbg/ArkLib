/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.MvPolynomial.Degrees
import ArkLib.Data.MvPolynomial.RestrictDegreeVar

/-!
# Operations preserving `MvPolynomial.restrictDegree`

This file collects lemmas about how the basic `MvPolynomial` operations interact with
`MvPolynomial.restrictDegree`, plus a "fix first `v` variables" helper.

The contents were originally housed in `Binius.BinaryBasefold.Prelude`. They are fully
generic (no binary-tower or characteristic dependencies) and have been promoted here so
that the structured (witness-mode) sumcheck — see
`ArkLib.ProofSystem.Sumcheck.Structured` — and any future ring-switching protocol can
import them without depending on `Binius.BinaryBasefold.*`.
-/

namespace MvPolynomial

open Finset

variable {L : Type*} [CommSemiring L] (ℓ : ℕ)

/-- The original index of a variable that survives after fixing the first `v` variables. -/
def fixFirstVariablesOfMQP_survivingIndex (v : Fin (ℓ + 1)) : Fin (ℓ - v) → Fin ℓ :=
  fun i => ⟨v + i, by
    have hi := i.2
    have hv := v.2
    omega⟩

/-- Fixes the **first** `v` variables of a `ℓ`-variate multivariate polynomial, leaving variables
`v, ..., ℓ-1` as `Fin (ℓ-v)`. Used by the structured sumcheck via
`fixFirstVariablesOfMQP_degreeLE` / the prismalinear analog
`fixFirstVariablesOfMQP_degreeVarLE`. -/
noncomputable def fixFirstVariablesOfMQP (v : Fin (ℓ + 1))
  (H : MvPolynomial (Fin ℓ) L) (challenges : Fin v → L) : MvPolynomial (Fin (ℓ - v)) L :=
  have h_l_eq : ℓ = v + (ℓ - v) := (Nat.add_sub_of_le v.is_le).symm
  -- Step 1 : Rename L[X Fin ℓ] to L[X (Fin (ℓ - v) ⊕ Fin v)], with the surviving suffix
  -- variables on `Sum.inl` and the fixed prefix variables on `Sum.inr`.
  let finEquiv := (finSumFinEquiv (m := v) (n := ℓ - v)).symm.trans (Equiv.sumComm _ _)
  let H_sum : L[X (Fin (ℓ - v) ⊕ Fin v)] := by
    apply MvPolynomial.rename (f := (finCongr h_l_eq).trans finEquiv) H
  -- Step 2 : Convert to (L[X Fin v])[X Fin (ℓ - v)] via sumAlgEquiv
  let H_forward : L[X Fin v][X Fin (ℓ - v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  -- Step 3 : Evaluate the poly at the point challenges to get a final L[X Fin (ℓ - v)]
  let eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  MvPolynomial.map (f := eval_map) (σ := Fin (ℓ - v)) H_forward

/-- Fixing the first `0` variables (with the empty challenge vector) is the identity. -/
theorem fixFirstVariablesOfMQP_zero_eq (H : MvPolynomial (Fin ℓ) L) :
    fixFirstVariablesOfMQP ℓ (0 : Fin (ℓ + 1)) H (challenges := Fin.elim0) = H := by
  induction H using MvPolynomial.induction_on with
  | C a =>
      unfold fixFirstVariablesOfMQP
      simp only [MvPolynomial.rename_C, MvPolynomial.sumAlgEquiv_apply, MvPolynomial.sumToIter_C,
        MvPolynomial.map_C, MvPolynomial.eval_C]
      rfl
  | add p q hp hq =>
      have hadd : ∀ x y : MvPolynomial (Fin ℓ) L,
          fixFirstVariablesOfMQP ℓ (0 : Fin (ℓ + 1)) (x + y) (challenges := Fin.elim0) =
            fixFirstVariablesOfMQP ℓ (0 : Fin (ℓ + 1)) x (challenges := Fin.elim0) +
              fixFirstVariablesOfMQP ℓ (0 : Fin (ℓ + 1)) y (challenges := Fin.elim0) := by
        intro x y; unfold fixFirstVariablesOfMQP; simp only [map_add]
      rw [hadd, hp, hq]
      rfl
  | mul_X p j hp =>
      have hmul : ∀ (x : MvPolynomial (Fin ℓ) L) (i : Fin ℓ),
          fixFirstVariablesOfMQP ℓ (0 : Fin (ℓ + 1)) (x * X i) (challenges := Fin.elim0) =
            fixFirstVariablesOfMQP ℓ (0 : Fin (ℓ + 1)) x (challenges := Fin.elim0) *
              fixFirstVariablesOfMQP ℓ (0 : Fin (ℓ + 1)) (X i) (challenges := Fin.elim0) := by
        intro x i; unfold fixFirstVariablesOfMQP; simp only [map_mul]
      rw [hmul, hp]
      congr 1
      -- image of `X j`: rename ↦ sumAlgEquiv ↦ map(eval elim0) sends `X j ↦ X j`
      unfold fixFirstVariablesOfMQP
      dsimp only
      rw [MvPolynomial.rename_X]
      have hj : (((finCongr (show ℓ = ((0 : Fin (ℓ + 1)) : ℕ) + (ℓ - ((0 : Fin (ℓ + 1)) : ℕ)) by
              simp)).trans
            (finSumFinEquiv.symm.trans (Equiv.sumComm _ _))) j) = Sum.inl (Fin.cast (by simp) j) := by
        simp [Equiv.sumComm, finCongr, finSumFinEquiv, Fin.addCases]; rfl
      rw [hj, MvPolynomial.sumAlgEquiv_apply, MvPolynomial.sumToIter_Xl, MvPolynomial.map_X]
      congr 1

/-- The per-variable / prismalinear degree-survival lemma: if a polynomial respects a per-variable
degree bound `b : Fin ℓ → ℕ`, then fixing the first `v` variables to scalars produces a polynomial
whose surviving `Fin (ℓ-v)` variables respect `b` restricted to their original suffix indices.
Needed for SWIRL-style sumchecks where the multiplier has degree `|D|-1` in the skip coord and
`≤ 1` in the remaining Boolean coords. The uniform `fixFirstVariablesOfMQP_degreeLE` below is the
constant-`b` corollary. -/
theorem fixFirstVariablesOfMQP_degreeVarLE
    {b : Fin ℓ → ℕ} (v : Fin (ℓ + 1)) {challenges : Fin v → L}
    {poly : MvPolynomial (Fin ℓ) L}
    (hp : poly ∈ restrictDegreeVar (Fin ℓ) L b) :
    fixFirstVariablesOfMQP ℓ v poly challenges ∈
      restrictDegreeVar (Fin (ℓ - v)) L (b ∘ fixFirstVariablesOfMQP_survivingIndex ℓ v) := by
  rw [MvPolynomial.mem_restrictDegreeVar]
  unfold fixFirstVariablesOfMQP
  dsimp only
  intro term h_term_in_support i
  have h_l_eq : ℓ = v + (ℓ - v) := (Nat.add_sub_of_le v.is_le).symm
  set finEquiv := (finSumFinEquiv (m := v) (n := ℓ - v)).symm.trans (Equiv.sumComm _ _)
  set e : Fin ℓ ≃ Fin (ℓ - v) ⊕ Fin v := (finCongr h_l_eq).trans finEquiv with he
  set H_sum := MvPolynomial.rename (f := e) poly
  set H_grouped : L[X Fin ↑v][X Fin (ℓ - ↑v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  set eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  have h_Hgrouped_degreeVarLE :
      H_grouped ∈ restrictDegreeVar (Fin (ℓ - v)) (L[X Fin ↑v]) ((b ∘ e.symm) ∘ Sum.inl) :=
    sumAlgEquiv_mem_restrictDegreeVar H_sum
      (rename_equiv_mem_restrictDegreeVar e poly hp)
  have h_term_in_Hgrouped_support : term ∈ H_grouped.support :=
    MvPolynomial.support_map_subset _ _ h_term_in_support
  have h_bound : term i ≤ (b ∘ e.symm) (Sum.inl i) :=
    (MvPolynomial.mem_restrictDegreeVar H_grouped).mp h_Hgrouped_degreeVarLE
      term h_term_in_Hgrouped_support i
  -- Bound-equality: (b ∘ e.symm) (Sum.inl i) is the original suffix variable `v + i`.
  have h_eq : e.symm (Sum.inl i) = fixFirstVariablesOfMQP_survivingIndex ℓ v i := by
    apply Fin.ext
    simp [he, finEquiv, fixFirstVariablesOfMQP_survivingIndex]
  change term i ≤ b (fixFirstVariablesOfMQP_survivingIndex ℓ v i)
  rw [← h_eq]
  exact h_bound

/-- Uniform corollary of `fixFirstVariablesOfMQP_degreeVarLE`: the constant per-variable case
`b = fun _ => deg`, where `restrictDegreeVar` collapses to `restrictDegree` definitionally via
`restrictDegreeVar_const`. Used by the structured sumcheck to bound the round polynomial. -/
theorem fixFirstVariablesOfMQP_degreeLE {deg : ℕ} (v : Fin (ℓ + 1)) {challenges : Fin v → L}
    {poly : L[X Fin ℓ]} (hp : poly ∈ L⦃≤ deg⦄[X Fin ℓ]) :
    fixFirstVariablesOfMQP ℓ v poly challenges ∈ L⦃≤ deg⦄[X Fin (ℓ - v)] :=
  fixFirstVariablesOfMQP_degreeVarLE ℓ (b := fun _ => deg) v hp

/-- For a multilinear `t` (each variable has `degreeOf ≤ 1`), substituting `t` into a univariate
`Q : L[X]` via `Polynomial.aeval` yields a multivariate polynomial whose degree in each variable is
bounded by `Q.natDegree`. Used by the structured sumcheck to bound the degree of `Q(witness)` in
the round polynomial `H = P · Q(t)`. -/
theorem degreeOf_aeval_le {L : Type*} [CommSemiring L] {σ : Type*} (i : σ)
    (Q : Polynomial L) (t : MvPolynomial σ L) (ht : degreeOf i t ≤ 1) :
    degreeOf i (Polynomial.aeval t Q) ≤ Q.natDegree := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum]
  refine le_trans (degreeOf_sum_le i Q.support _) ?_
  refine Finset.sup_le fun e he => ?_
  calc degreeOf i (algebraMap L (MvPolynomial σ L) (Q.coeff e) * t ^ e)
      ≤ degreeOf i (algebraMap L (MvPolynomial σ L) (Q.coeff e)) + degreeOf i (t ^ e) :=
        degreeOf_mul_le i _ _
    _ = degreeOf i (t ^ e) := by rw [MvPolynomial.algebraMap_eq, degreeOf_C, zero_add]
    _ ≤ e * degreeOf i t := degreeOf_pow_le i t e
    _ ≤ e * 1 := by gcongr
    _ = e := mul_one e
    _ ≤ Q.natDegree := Polynomial.le_natDegree_of_mem_supp e he

end MvPolynomial
