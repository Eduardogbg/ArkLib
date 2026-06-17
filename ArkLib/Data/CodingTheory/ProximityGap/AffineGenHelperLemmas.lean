/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import ArkLib.Data.CodingTheory.ProximityGap.MCAGenerator
import Mathlib
import ArkLib.Data.Probability.Notation
import ArkLib.Data.Probability.Instances


/-!
# Support lemmas for `AffineLine_MCA_AffineSpaceMCA` (Lemma 7.1 of [BCGM25])
This file develops the combinatorial / linear-algebraic ingredients of the proof that MCA for the
affine line generator implies MCA for the affine space generator.
## References
* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BCGM25]. Full paper : https://eprint.iacr.org/2025/2051}
-/

open scoped BigOperators
open CoreDefinitions LinearCode

namespace AffineMCA

variable {ι : Type} [Fintype ι]
          {F : Type} [Field F]


/-- The affine-space combination of codewords `U` at seed `x`:
`U 0 + ∑ i, x i • U (i+1)`, i.e. `vecMul (1, x) U`. -/
def affineComb {s : ℕ} (U : Fin (s + 1) → (ι → F)) (x : Fin s → F) : ι → F :=
  Matrix.vecMul (Fin.cons 1 x) U


/-- The linear combination `∑ i, l i • U (i+1)` of the "direction" codewords. -/
def linComb {s : ℕ} (U : Fin (s + 1) → (ι → F)) (l : Fin s → F) : ι → F :=
  fun k => ∑ i, l i * U i.succ k

omit [Fintype ι] in
lemma affineComb_apply {s : ℕ} (U : Fin (s + 1) → (ι → F)) (x : Fin s → F) (k : ι) :
    affineComb U x k = U 0 k + ∑ i, x i * U i.succ k := by
  unfold affineComb
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ]


/-
The affine line combination `vecMul (1, t) W = W 0 + t • W 1`.
-/
omit [Fintype ι] in
lemma line_vecMul (W : Fin 2 → (ι → F)) (t : F) :
    Matrix.vecMul (AffineLineGenerator F t) W = W 0 + t • W 1 := by
  ext k
  exact (by
  simp only [Matrix.vecMul, AffineLineGenerator, Matrix.cons_dotProduct, Matrix.head_val', one_mul,
    Matrix.tail_val', Matrix.dotProduct_of_isEmpty, add_zero, Fin.isValue, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rfl)


/-
Restriction is additive.
-/
lemma projectedWord_add (a b : ι → F) (T : Finset ι) :
    projectedWord (a + b) T = projectedWord a T + projectedWord b T := rfl

/-
The affine combination along the line `x ↦ v + t • lam` in seed space.
-/
omit [Fintype ι] in
lemma affineComb_line {s : ℕ} (U : Fin (s + 1) → (ι → F)) (v lam : Fin s → F) (t : F) :
    affineComb U (v + t • lam) = affineComb U v + t • (linComb U lam) := by
  simp only [affineComb, funext_iff, Pi.add_apply, Pi.smul_apply, linComb, smul_eq_mul,
            Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, one_mul, Fin.cons_succ,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc, Finset.sum_add_distrib,
            Finset.mul_sum _ _ _, add_assoc, implies_true]
/-
**Step 1 of Lemma 7.1.**  If the affine combination restricted to `T` lies in the code, and
some `U j` restricted to `T` does *not* lie in the code, then some *direction* codeword `U (i+1)`
restricted to `T` does not lie in the code.
-/
lemma exists_succ_not_mem {s : ℕ} (LC : LinearCode ι F) (T : Finset ι)
    (U : Fin (s + 1) → (ι → F)) (x : Fin s → F)
    (hv : projectedWord (affineComb U x) T ∈ projectedCode_submod LC T)
    (hj : ∃ j : Fin (s + 1), projectedWord (U j) T ∉ projectedCode_submod LC T) :
    ∃ i : Fin s, projectedWord (U i.succ) T ∉ projectedCode_submod LC T := by
  contrapose! hj;
  intro j;
  induction j using Fin.inductionOn
  · have h_aff : affineComb U x = U 0 + linComb U x := by
      ext k; simp [affineComb_apply, linComb]
    have hj' : ∀ i : Fin s, projectedWord (U i.succ) T ∈ projectedCode LC.carrier T := hj
    have h_linComb : projectedWord (linComb U x) T ∈ projectedCode_submod LC T := by
      change projectedWord (fun k => ∑ i, x i * U i.succ k) T ∈ projectedCode LC.carrier T
      exact LinearCode.projectedCode_linearCombination LC T (fun i => U i.succ) x hj'
    have h_split : projectedWord (affineComb U x) T =
        projectedWord (U 0) T + projectedWord (linComb U x) T := by
      rw [h_aff, projectedWord_add]
    have hmem := Submodule.sub_mem _ (h_split ▸ hv) h_linComb
    rwa [add_sub_cancel_right] at hmem
  · exact hj _

open Classical in
/-
**Kernel count (Step 2 of Lemma 7.1).**  If some direction codeword `w i` does not project into
the code on `T`, then the set of coefficient vectors `l` whose combination `∑ i, l i • w i` projects
into the code has cardinality at most `|F|^(s-1)`.
-/
lemma proj_lincomb_ker_card_le [Fintype F] {s : ℕ}
    (LC : LinearCode ι F) (T : Finset ι) (w : Fin s → (ι → F))
    (hne : ∃ i, projectedWord (w i) T ∉ projectedCode_submod LC T) :
    (Finset.univ.filter (fun l : Fin s → F =>
        projectedWord (fun k => ∑ i, l i * w i k) T ∈ projectedCode_submod LC T)).card
      ≤ (Fintype.card F) ^ (s - 1) := by
  -- By definition of $g$, we know that its kernel has dimension at most $s-1$.
  have hker : (Module.finrank F (LinearMap.ker (show (Fin s → F) →ₗ[F] (T → F) ⧸ LC.projectedCode_submod T from (Submodule.mkQ (LC.projectedCode_submod T)) ∘ₗ (LinearMap.funLeft F F (Subtype.val : T → ι)) ∘ₗ (Fintype.linearCombination F w)))) ≤ s - 1 := by
                                                  obtain ⟨ i, hi ⟩ := hne;
                                                  have h_range : LinearMap.range (show (Fin s → F) →ₗ[F] (T → F) ⧸ LC.projectedCode_submod T from (Submodule.mkQ (LC.projectedCode_submod T)) ∘ₗ (LinearMap.funLeft F F (Subtype.val : T → ι)) ∘ₗ (Fintype.linearCombination F w)) ≠ ⊥ := by
                                                                                    simp_all +decide [ Submodule.eq_bot_iff ];
                                                                                    use Pi.single i 1; simp_all +decide [ Fintype.linearCombination_apply ] ;
                                                                                    convert hi using 1;
                                                  have := LinearMap.finrank_range_add_finrank_ker ( show ( Fin s → F ) →ₗ[F] ( T → F ) ⧸ LC.projectedCode_submod T from ( Submodule.mkQ ( LC.projectedCode_submod T ) ) ∘ₗ ( LinearMap.funLeft F F ( Subtype.val : T → ι ) ) ∘ₗ ( Fintype.linearCombination F w ) );
                                                  simp_all +decide;
                                                  exact Nat.le_sub_one_of_lt ( lt_of_lt_of_le ( Nat.lt_add_of_pos_left ( Nat.pos_of_ne_zero ( by aesop ) ) ) this.le );
  -- Since the kernel is a subspace of the s-dimensional space `Fin s → F`, its cardinality is $q^{\text{dim}(\text{ker}(g))}$.
  have hcard : Fintype.card (LinearMap.ker (show (Fin s → F) →ₗ[F] (T → F) ⧸ LC.projectedCode_submod T from (Submodule.mkQ (LC.projectedCode_submod T)) ∘ₗ (LinearMap.funLeft F F (Subtype.val : T → ι)) ∘ₗ (Fintype.linearCombination F w))) ≤ (Fintype.card F) ^ (s - 1) := by
                                              have hcard : Fintype.card (LinearMap.ker (show (Fin s → F) →ₗ[F] (T → F) ⧸ LC.projectedCode_submod T from (Submodule.mkQ (LC.projectedCode_submod T)) ∘ₗ (LinearMap.funLeft F F (Subtype.val : T → ι)) ∘ₗ (Fintype.linearCombination F w))) = (Fintype.card F) ^ (Module.finrank F (LinearMap.ker (show (Fin s → F) →ₗ[F] (T → F) ⧸ LC.projectedCode_submod T from (Submodule.mkQ (LC.projectedCode_submod T)) ∘ₗ (LinearMap.funLeft F F (Subtype.val : T → ι)) ∘ₗ (Fintype.linearCombination F w)))) := by
                                                                                                                                                                                                                                                                                                                                                  have := @Module.card_eq_pow_finrank F;
                                                                                                                                                                                                                                                                                                                                                  convert this;
                                              exact hcard.symm ▸ pow_le_pow_right₀ ( Fintype.card_pos ) hker;
  convert hcard using 1 ; simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] ;
  rw [Fintype.card_subtype]
  congr
  ext
  simp only [projectedWord, Fintype.linearCombination_apply, map_sum, map_smul]
  congr! 1
  ext
  simp [Finset.sum_apply, LinearMap.funLeft_apply]
/-
**Averaging over coefficient vectors (Step 3 of Lemma 7.1).**  A pigeonhole: if a sum of
nonnegative integer counts over all `|F|^s` coefficient vectors is bounded by `|F|^(s-1) * m`, then
some coefficient vector achieves a count whose `|F|`-fold is at most `m`.
-/
omit [Field F] in
lemma exists_avg_le [Fintype F] {s : ℕ} (hs : 1 ≤ s) [Nonempty F]
    (f : (Fin s → F) → ℕ) (m : ℕ)
    (hsum : ∑ l, f l ≤ (Fintype.card F) ^ (s - 1) * m) :
    ∃ l, (Fintype.card F : ℝ) * f l ≤ m := by
  by_contra h_contra
  push Not at h_contra
  norm_cast at *
  have := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) fun l _ => h_contra l
  simp_all only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
    Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum _ _ _]
  cases s <;> simp_all [pow_succ', mul_assoc]
  nlinarith

open Classical in
/-
**Averaging over base points (Step 5 of Lemma 7.1).**
For a fixed direction `d`, some base
point `v` makes the line `t ↦ v + t • d` hit the set `B'` with (normalized) frequency at least the
density of `B'`.
-/
lemma exists_dir_line_ge [Fintype F] [Nonempty F] {s : ℕ}
    (d : Fin s → F) (B' : Finset (Fin s → F)) :
    ∃ v : Fin s → F,
      ((B'.card : ℝ) / (Fintype.card F) ^ s) ≤
        ((Finset.univ.filter (fun t : F => v + t • d ∈ B')).card : ℝ) / (Fintype.card F) := by
  -- By averaged, we mean summing over $v$ and then dividing by $|F|^s$.
  set q := Fintype.card F
  have h_sum : ∑ v : Fin s → F, (Finset.univ.filter (fun t : F => v + t • d ∈ B')).card = q * B'.card := by
    have h_sum : ∑ v : Fin s → F, (Finset.univ.filter (fun t : F => v + t • d ∈ B')).card = ∑ t : F, ∑ v : Fin s → F, (if v + t • d ∈ B' then 1 else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    -- For each fixed $t$, the inner sum counts the number of $v$ such that $v + t • d ∈ B'$.
    have h_inner : ∀ t : F, ∑ v : Fin s → F, (if v + t • d ∈ B' then 1 else 0) = B'.card := by
      intro t
      have h_inner : Finset.card (Finset.filter (fun v => v + t • d ∈ B') Finset.univ) = Finset.card B' := by
        rw [ ← Finset.card_image_of_injective _ ( show Function.Injective ( fun v : Fin s → F => v + t • d ) from fun v w h => by simpa using h ) ] ; congr ; ext ; aesop;
      aesop;
    aesop;
  contrapose! h_sum;
  have := Finset.sum_lt_sum_of_nonempty ( Finset.univ_nonempty ) fun v _ => h_sum v; simp_all +decide ;
  rw [ mul_div_cancel₀ ] at this <;> simp_all +decide [ ← Finset.sum_div _ _ _ ] ;
  rw [ div_lt_iff₀ ] at this <;> norm_cast at * <;> nlinarith [ show q > 0 from Fintype.card_pos ] ;


open Classical in
/-
**Core combinatorial content of Lemma 7.1.**  There is a choice of two line-codewords `W` so
that `(1 - 1/|F|)` times the density of affine-space bad seeds is at most the density of affine-line
bad seeds for `W`.
-/
lemma exists_line_bound [Fintype F] {s : ℕ} (hs : 1 ≤ s)
    (LC : LinearCode ι F) (U : Fin (s + 1) → (ι → F)) (γ : unitInterval) :
    ∃ W : Fin 2 → (ι → F),
      (1 - 1 / (Fintype.card F : ℝ)) *
        (((Finset.univ.filter (fun x : Fin s → F =>
            IsMCA (AffineSpaceGenerator F s) LC x U γ)).card : ℝ) / (Fintype.card F) ^ s)
      ≤ ((Finset.univ.filter (fun t : F =>
            IsMCA (AffineLineGenerator F) LC t W γ)).card : ℝ) / (Fintype.card F) := by
  -- Witness function. For each `x` choose `T x : Finset ι` such that `isB x` implies:
  -- `(T x).card ≥ card ι * (1-γ)`, `projectedWord (affineComb U x) (T x) ∈ projectedCode_submod
  -- LC (T x)` (rewriting the `vecMul` form via `affineComb_eq_vecMul`), and `∃ j, projectedWord
  -- (U j) (T x) ∉ projectedCode_submod LC (T x)`.
  set isB := fun x => IsMCA (AffineSpaceGenerator F s) LC x U γ
  set Bset := Finset.univ.filter isB
  set m := Bset.card
  obtain ⟨T, hT⟩ :
    ∃ T : (Fin s → F) → (Finset ι), ∀ x, isB x → (T x).card ≥ (Fintype.card ι) * (1 - (γ : ℝ)) ∧
      projectedWord (affineComb U x) (T x) ∈ projectedCode_submod LC (T x) ∧
      ∃ j, projectedWord (U j) (T x) ∉ projectedCode_submod LC (T x) := by
    have hT : ∀ x, isB x → ∃ T : Finset ι, (T.card : ℝ) ≥ (Fintype.card ι) * (1 - (γ : ℝ)) ∧
          projectedWord (affineComb U x) T ∈ projectedCode_submod LC T ∧ ∃ j,
                          projectedWord (U j) T ∉ projectedCode_submod LC T := by
      exact fun x hx => by obtain ⟨T, hT₁, hT₂, j, hj⟩ := hx; exact ⟨T, hT₁, hT₂, j, hj⟩
    choose! T hT using hT
    use T
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin s → F, (Bset.filter (fun x => projectedWord (linComb U lam) (T x)
                       ∈ projectedCode_submod LC (T x))).card ≤ m / (Fintype.card F : ℝ) := by
    have h_sum : ∑ lam : Fin s → F, (Bset.filter (fun x => projectedWord (linComb U lam) (T x) ∈
                  projectedCode_submod LC (T x))).card ≤ m * (Fintype.card F) ^ (s - 1) := by
      have h_sum : ∀ x ∈ Bset, ∑ lam : Fin s → F, (if projectedWord (linComb U lam) (T x) ∈
                  projectedCode_submod LC (T x) then 1 else 0) ≤ (Fintype.card F) ^ (s - 1) := by
        intro x hx
        have h_ker : ∃ i : Fin s, projectedWord (U i.succ) (T x) ∉ projectedCode_submod LC (T x) :=
          by
          exact exists_succ_not_mem LC (T x) U x (hT x (Finset.mem_filter.mp hx |>.2) |>.2.1)
                (hT x (Finset.mem_filter.mp hx |>.2) |>.2.2)
        have := proj_lincomb_ker_card_le LC (T x) (fun i => U i.succ) h_ker; aesop
      convert Finset.sum_le_sum h_sum using 1
      · rw [Finset.sum_comm, Finset.sum_congr rfl]
        aesop
      · simp +zetaDelta
    have := exists_avg_le hs (fun lam => (Bset.filter (fun x => projectedWord (linComb U lam) (T x)
          ∈ LC.projectedCode_submod (T x) ) |> Finset.card)) m ?_
    · exact this.imp fun x hx => by rwa [le_div_iff₀' (Nat.cast_pos.mpr <| Fintype.card_pos)]
    · linarith
  obtain ⟨v, hv⟩ : ∃ v : Fin s → F, ((Bset.filter (fun x => ¬projectedWord (linComb U lam) (T x) ∈
          projectedCode_submod LC (T x))).card : ℝ) / (Fintype.card F) ^ s ≤
          ((Finset.univ.filter (fun t : F => v + t • lam ∈ Bset ∧
           ¬projectedWord (linComb U lam) (T (v + t • lam)) ∈
           projectedCode_submod LC (T (v + t • lam)))).card : ℝ) / (Fintype.card F) := by
    have := exists_dir_line_ge lam (Bset.filter fun x => ¬projectedWord (linComb U lam) (T x) ∈
            LC.projectedCode_submod (T x)); aesop
  refine ⟨![affineComb U v, linComb U lam], le_trans ?_ (hv.trans ?_ )⟩
  · convert mul_le_mul_of_nonneg_right
        (show (1 - 1 / (Fintype.card F : ℝ)) * m ≤ (
          Finset.filter (fun x => ¬projectedWord (linComb U lam ) ( T x ) ∈
          LC.projectedCode_submod (T x)) Bset |> Finset.card : ℝ) from ?_)
          (by positivity : 0 ≤ (Fintype.card F : ℝ) ⁻¹ ^ s) using 1
    · ring
    · ring
    · rw [one_sub_div, div_mul_eq_mul_div, div_le_iff₀] <;> norm_cast <;> norm_num
      · rw [Int.subNatNat_eq_coe]
        push_cast
        rw [le_div_iff₀ (Nat.cast_pos.mpr <| Fintype.card_pos)] at hlam
        norm_cast at *
        rw [Int.subNatNat_eq_coe]
        push_cast
        nlinarith [show Fintype.card F > 1 from Fintype.one_lt_card,
          show Finset.card (Finset.filter
              (fun x => projectedWord (linComb U lam) (T x) ∈
                projectedCode_submod LC (T x)) Bset)
            + Finset.card (Finset.filter
              (fun x => ¬projectedWord (linComb U lam) (T x) ∈
                projectedCode_submod LC (T x)) Bset) = m
            from by rw [Finset.card_filter_add_card_filter_not]]
  · gcongr
    intro h
    use T (v + ‹_› • lam)
    simp_all only [ge_iff_le, Finset.mem_univ, line_vecMul, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.exists_fin_two, not_false_eq_true, or_true,
      and_true]
    exact ⟨hT _ (Finset.mem_filter.mp h.1 |>.2 ) |>.1,
        by simpa only [affineComb_line] using hT _ (Finset.mem_filter.mp h.1 |>.2 ) |>.2.1⟩

end AffineMCA
