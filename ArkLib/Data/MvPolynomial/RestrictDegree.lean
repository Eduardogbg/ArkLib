/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.MvPolynomial.Degrees

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

private lemma sumToIter_monomial_aux {R : Type*} [CommSemiring R]
    {S₁ S₂ : Type*}
    (m : (S₁ ⊕ S₂) →₀ ℕ) (c : R) :
    MvPolynomial.sumToIter R S₁ S₂ (MvPolynomial.monomial m c) =
      MvPolynomial.monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
        (MvPolynomial.monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) c) := by
  simp +decide only [MvPolynomial.sumToIter, MvPolynomial.eval₂Hom_monomial]
  simp +decide [Finsupp.prod, Finsupp.comapDomain]
  convert congr_arg₂ (· * ·) rfl ?_ using 1
  rotate_left
  exact ∏ x ∈ m.support,
    Sum.rec (fun a => MvPolynomial.X a)
      (fun b => MvPolynomial.C (MvPolynomial.X b)) x ^ m x
  · rfl
  · simp +decide [MvPolynomial.monomial_eq, Finset.prod_ite]
    simp +decide [mul_assoc, Finsupp.prod]
    rw [← Finset.prod_filter_mul_prod_filter_not m.support (fun x => x.isRight)]
    congr! 2
    · exact Finset.prod_bij (fun x hx => Sum.inr x) (by aesop) (by aesop)
        (by aesop) (by aesop)
    · exact Finset.prod_bij (fun x hx => Sum.inl x) (by aesop) (by aesop)
        (by aesop) (by aesop)

private lemma sumAlgEquiv_mem_restrictDegree {R : Type*} [CommSemiring R]
    {S₁ S₂ : Type*}
    (p : MvPolynomial (S₁ ⊕ S₂) R) (n : ℕ)
    (hp : p ∈ MvPolynomial.restrictDegree (S₁ ⊕ S₂) R n) :
    (MvPolynomial.sumAlgEquiv R S₁ S₂) p ∈
      MvPolynomial.restrictDegree S₁ (MvPolynomial S₂ R) n := by
  intro s hs
  obtain ⟨m, hm⟩ : ∃ m : (S₁ ⊕ S₂) →₀ ℕ,
      m ∈ p.support ∧ s = m.comapDomain Sum.inl Sum.inl_injective.injOn := by
    have h_sum : (MvPolynomial.sumAlgEquiv R S₁ S₂) p =
        ∑ m ∈ p.support,
          (MvPolynomial.monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn))
            (MvPolynomial.monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn)
              (p.coeff m)) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      exact Finset.sum_congr rfl fun _ _ => sumToIter_monomial_aux _ _
    contrapose! hs
    simp +decide [h_sum]
    erw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    erw [AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.lsingle_apply]; aesop
  aesop

private lemma rename_equiv_mem_restrictDegree {R : Type*} [CommSemiring R]
    {σ τ : Type*}
    (e : σ ≃ τ) (p : MvPolynomial σ R) (n : ℕ)
    (hp : p ∈ MvPolynomial.restrictDegree σ R n) :
    (MvPolynomial.rename e p) ∈ MvPolynomial.restrictDegree τ R n := by
  intro m hm
  obtain ⟨n', hn', hm_eq⟩ : ∃ n' ∈ p.support, m = n'.mapDomain e := by
    simp +zetaDelta at *
    rw [MvPolynomial.rename_eq] at hm
    contrapose! hm
    rw [Finsupp.mapDomain]
    rw [Finsupp.sum, Finsupp.finset_sum_apply]
    exact Finset.sum_eq_zero fun x hx =>
      Finsupp.single_eq_of_ne (hm x (by aesop))
  aesop

variable {L : Type*} [CommRing L] (ℓ : ℕ)

/-- Fixes the first `v` variables of a `ℓ`-variate multivariate polynomial.
`t` -> `H_i` derivation
-/
noncomputable def fixFirstVariablesOfMQP (v : Fin (ℓ + 1))
  (H : MvPolynomial (Fin ℓ) L) (challenges : Fin v → L) : MvPolynomial (Fin (ℓ - v)) L :=
  have h_l_eq : ℓ = (ℓ - v) + v := by rw [Nat.add_comm]; exact (Nat.add_sub_of_le v.is_le).symm
  -- Step 1 : Rename L[X Fin ℓ] to L[X (Fin (ℓ - v) ⊕ Fin v)]
  let finEquiv := finSumFinEquiv (m := ℓ - v) (n := v).symm
  let H_sum : L[X (Fin (ℓ - v) ⊕ Fin v)] := by
    apply MvPolynomial.rename (f := (finCongr h_l_eq).trans finEquiv) H
  -- Step 2 : Convert to (L[X Fin v])[X Fin (ℓ - v)] via sumAlgEquiv
  let H_forward : L[X Fin v][X Fin (ℓ - v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  -- Step 3 : Evaluate the poly at the point challenges to get a final L[X Fin (ℓ - v)]
  let eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  MvPolynomial.map (f := eval_map) (σ := Fin (ℓ - v)) H_forward

/-- Auxiliary lemma for proving that the polynomial sent by the honest prover is of degree at most
`deg` -/
theorem fixFirstVariablesOfMQP_degreeLE {deg : ℕ} (v : Fin (ℓ + 1)) {challenges : Fin v → L}
    {poly : L[X Fin ℓ]} (hp : poly ∈ L⦃≤ deg⦄[X Fin ℓ]) :
    fixFirstVariablesOfMQP ℓ v poly challenges ∈ L⦃≤ deg⦄[X Fin (ℓ - v)] := by
  -- The goal is to prove the totalDegree of the result is ≤ deg.
  rw [MvPolynomial.mem_restrictDegree]
  unfold fixFirstVariablesOfMQP
  dsimp only
  intro term h_term_in_support i
  -- ⊢ term i ≤ deg
  have h_l_eq : ℓ = (ℓ - v) + v := (Nat.sub_add_cancel v.is_le).symm
  set finEquiv := finSumFinEquiv (m := ℓ - v) (n := v).symm
  set H_sum := MvPolynomial.rename (f := (finCongr h_l_eq).trans finEquiv) poly
  set H_grouped : L[X Fin ↑v][X Fin (ℓ - ↑v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  set eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  have h_Hgrouped_degreeLE : H_grouped ∈ (L[X Fin ↑v])⦃≤ deg⦄[X Fin (ℓ - ↑v)] := by
    exact sumAlgEquiv_mem_restrictDegree H_sum deg
      (rename_equiv_mem_restrictDegree
        ((finCongr h_l_eq).trans finEquiv) poly deg hp)
  have h_mem_support_max_deg_LE := MvPolynomial.mem_restrictDegree (R := L[X Fin ↑v]) (n := deg)
    (σ := Fin (ℓ - ↑v)) (p := H_grouped).mp (h_Hgrouped_degreeLE)
  have h_term_in_Hgrouped_support : term ∈ H_grouped.support := by
    have h_support_map_subset : ((MvPolynomial.map eval_map) H_grouped).support
      ⊆ H_grouped.support := by apply MvPolynomial.support_map_subset
    exact (h_support_map_subset) h_term_in_support
  -- h_Hgrouped_degreeLE
  let res : term i ≤ deg := h_mem_support_max_deg_LE term h_term_in_Hgrouped_support i
  exact res

end MvPolynomial
