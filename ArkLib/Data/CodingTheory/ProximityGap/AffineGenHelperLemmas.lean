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

variable {ι : Type}
         {F : Type} [Field F]


/-- The affine-space combination of codewords `U` at seed `x`:
`U 0 + ∑ i, x i • U (i+1)`, i.e. `vecMul (1, x) U`. -/
abbrev affineComb {s : ℕ} (U : Fin (s + 1) → (ι → F)) (x : Fin s → F) : ι → F :=
  Matrix.vecMul (Fin.cons 1 x) U

/-- The linear combination `∑ i, l i • U (i+1)` of the "direction" codewords. -/
abbrev linComb {s : ℕ} (U : Fin (s + 1) → (ι → F)) (l : Fin s → F) : ι → F :=
  fun k => ∑ i, l i * U i.succ k

/-
The affine line combination `vecMul (1, t) W = W 0 + t • W 1`.
-/
lemma line_vecMul (W : Fin 2 → (ι → F)) (t : F) :
    Matrix.vecMul (AffineLineGenerator F t) W = W 0 + t • W 1 := by
  ext k
  simp [AffineLineGenerator, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-
The affine combination along the line `x ↦ v + t • lam` in seed space.
-/
lemma affineComb_line {s : ℕ} (U : Fin (s + 1) → (ι → F)) (v lam : Fin s → F) (t : F) :
    affineComb U (v + t • lam) = affineComb U v + t • (linComb U lam) := by
  have hsplit : (Fin.cons 1 (v + t • lam) : Fin (s + 1) → F) =
      Fin.cons 1 v + t • (Fin.cons (0 : F) lam : Fin (s + 1) → F) := by
    ext i
    refine Fin.cases ?_ ?_ i <;> simp
  have hlin : Matrix.vecMul (Fin.cons (0 : F) lam : Fin (s + 1) → F) U = linComb U lam := by
    ext k
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, linComb]
  change Matrix.vecMul (Fin.cons 1 (v + t • lam) : Fin (s + 1) → F) U = _
  rw [hsplit, Matrix.add_vecMul, Matrix.smul_vecMul, hlin]

/-
**Step 1 of Lemma 7.1.**  If the affine combination restricted to `T` lies in the code, and
some `U j` restricted to `T` does *not* lie in the code, then some *direction* codeword `U (i+1)`
restricted to `T` does not lie in the code.
-/
lemma exists_succ_not_mem [Fintype ι] {s : ℕ} (LC : LinearCode ι F) (T : Finset ι)
    (U : Fin (s + 1) → (ι → F)) (x : Fin s → F)
    (hv : projectedWord (affineComb U x) T ∈ projectedCode_submod LC T)
    (hj : ∃ j : Fin (s + 1), projectedWord (U j) T ∉ projectedCode_submod LC T) :
    ∃ i : Fin s, projectedWord (U i.succ) T ∉ projectedCode_submod LC T := by
  contrapose! hj
  intro j
  induction j using Fin.inductionOn
  · have h_aff : affineComb U x = U 0 + linComb U x := by
      ext k; simp [affineComb, linComb, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    have hj' : ∀ i : Fin s, projectedWord (U i.succ) T ∈ projectedCode LC.carrier T := hj
    have h_linComb : projectedWord (linComb U x) T ∈ projectedCode_submod LC T := by
      change projectedWord (fun k => ∑ i, x i * U i.succ k) T ∈ projectedCode LC.carrier T
      exact LinearCode.projectedCode_linearCombination LC T (fun i => U i.succ) x hj'
    have h_split : projectedWord (affineComb U x) T =
        projectedWord (U 0) T + projectedWord (linComb U x) T := by
      rw [h_aff]
      rfl
    have hmem := Submodule.sub_mem _ (h_split ▸ hv) h_linComb
    rwa [add_sub_cancel_right] at hmem
  · exact hj _

-- /-- The "bad seeds" for the affine-space generator: those `x` for which the MCA condition holds,
-- i.e. for which the affine-space generator output at `x` *fails* to have correlated agreement.
-- This is the formalization of the paper's bad-seed set `B`. The `Finset`-valued version used in
-- the cardinality counting argument is `Bset`/`isB` in `exists_line_bound` below. -/
-- def MCABadSeed [Fintype F] [Fintype ι] {s : ℕ} (LC : LinearCode ι F) (U : Fin (s + 1) → (ι → F))
--     (γ : unitInterval) : Type :=
--   {x : Fin s → F // IsMCA (AffineSpaceGenerator F s) LC x U γ}

-- /-- For a bad seed `B`, a choice of the witnessing `Finset ι` from the existential in `IsMCA`. -/
-- noncomputable def MCABadSeed.witnessFinset [Fintype F] [Fintype ι] {s : ℕ} {LC : LinearCode ι F}
--     {U : Fin (s + 1) → (ι → F)} {γ : unitInterval} (B : MCABadSeed LC U γ) : Finset ι :=
--   Classical.choose B.2

/-- The quotient of the projected word space `T → F` by the projected code on `T`, used in the
kernel/rank-nullity argument of Step 2. -/
abbrev projectedQuotient [Fintype ι] (LC : LinearCode ι F) (T : Finset ι) : Type :=
  (T → F) ⧸ LC.projectedCode_submod T

open Classical in
/-
**Kernel count (Step 2 of Lemma 7.1).**
If some direction codeword `w i` does not project into the code on `T`, then the set of coefficient
vectors `l` whose combination `∑ i, l i • w i` projects into the code has cardinality at most
`|F| ^ (s-1)`. -/
lemma proj_lincomb_ker_card_le [Fintype F] [Fintype ι] {s : ℕ}
    (LC : LinearCode ι F) (T : Finset ι) (w : Fin s → (ι → F))
    (hne : ∃ i, projectedWord (w i) T ∉ projectedCode_submod LC T) :
    (Finset.univ.filter (fun l : Fin s → F =>
        projectedWord (fun k => ∑ i, l i * w i k) T ∈ projectedCode_submod LC T)).card
      ≤ (Fintype.card F) ^ (s - 1) := by
  -- `g` is the composite linear map `(Fin s → F) → (T → F) ⧸ projectedCode_submod LC T` sending
  -- `l ↦ (∑ i, l i • w i)|[T] mod projectedCode_submod LC T`; its kernel is exactly the set of
  -- `l` whose combination projects into the code on `T`.
  set g : (Fin s → F) →ₗ[F] projectedQuotient LC T :=
    Submodule.mkQ (LC.projectedCode_submod T) ∘ₗ
      LinearMap.funLeft F F (Subtype.val : T → ι) ∘ₗ Fintype.linearCombination F w with hg_def
  -- By definition of $g$, we know that its kernel has dimension at most $s-1$.
  have hker : Module.finrank F (LinearMap.ker g) ≤ s - 1 := by
    obtain ⟨i, hi⟩ := hne
    have h_range : LinearMap.range g ≠ ⊥ := by
      simp_all only [ne_eq, Submodule.eq_bot_iff, LinearMap.mem_range, LinearMap.coe_comp,
        Function.comp_apply, Submodule.mkQ_apply, forall_exists_index, forall_apply_eq_imp_iff,
        Submodule.Quotient.mk_eq_zero, not_forall]
      exact ⟨Pi.single i 1, by simpa [Fintype.linearCombination_apply] using hi⟩
    have hrank_null := LinearMap.finrank_range_add_finrank_ker g
    simp_all only [ne_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, ge_iff_le]
    exact Nat.le_sub_one_of_lt
      (lt_of_lt_of_le (Nat.lt_add_of_pos_left (Nat.pos_of_ne_zero (by aesop))) hrank_null.le)
  -- Since the kernel is a subspace of the s-dimensional space `Fin s → F`, its cardinality is
  -- $q^{\text{dim}(\text{ker}(g))}$.
  have hcard : Fintype.card (LinearMap.ker g) ≤ (Fintype.card F) ^ (s - 1) := by
    rw [Module.card_eq_pow_finrank (K := F)]
    exact pow_le_pow_right₀ (Fintype.card_pos) hker
  convert hcard using 1
  simp only [LinearMap.mem_ker, hg_def, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
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
lemma exists_avg_le [Fintype F] {s : ℕ} (hs : 1 ≤ s) (f : (Fin s → F) → ℕ) (m : ℕ)
    (hsum : ∑ l, f l ≤ (Fintype.card F) ^ (s - 1) * m) :
    ∃ l, (Fintype.card F : ℝ) * f l ≤ m := by
  by_contra h_contra
  push Not at h_contra
  norm_cast at *
  have hsum_lt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) fun l _ => h_contra l
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
  -- For each fixed $t$, the map $v ↦ v + t • d$ is injective, so the filtered card on the left
  -- equals $|B'|$.
  have h_card_eq : ∀ t : F, Finset.card (Finset.filter (fun v => v + t • d ∈ B') Finset.univ) =
      Finset.card B' := by
    intro t
    have hinj : Function.Injective (fun v : Fin s → F => v + t • d) := fun v w h => by simpa using h
    rw [← Finset.card_image_of_injective _ hinj]
    congr; ext; aesop
  -- For each fixed $t$, the inner sum counts the number of $v$ such that $v + t • d ∈ B'$.
  have h_inner : ∀ t : F, ∑ v : Fin s → F, (if v + t • d ∈ B' then 1 else 0) = B'.card := by
    intro t; have := h_card_eq t; aesop
  have h_swap : ∑ v : Fin s → F, (Finset.univ.filter (fun t : F => v + t • d ∈ B')).card =
      ∑ t : F, ∑ v : Fin s → F, (if v + t • d ∈ B' then 1 else 0) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl]; aesop
  have h_sum :
      ∑ v : Fin s → F, (Finset.univ.filter (fun t : F => v + t • d ∈ B')).card = q * B'.card := by
    rw [h_swap]
    simp only [h_inner, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rfl
  contrapose! h_sum
  have hsum_lt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) fun v _ => h_sum v
  simp_all only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, ne_eq]
  rw [mul_div_cancel₀] at hsum_lt <;> simp_all only [← Finset.sum_div _ _ _, ne_eq,
    pow_eq_zero_iff', Nat.cast_eq_zero, Fintype.card_ne_zero, false_and, not_false_eq_true]
  rw [div_lt_iff₀] at hsum_lt <;> norm_cast at * <;> nlinarith [show q > 0 from Fintype.card_pos]


open Classical in
/-
**Core combinatorial content of Lemma 7.1.**
There is a choice of two line-codewords `W` so that `(1 - 1/|F|)` times the density of affine-space
bad seeds is at most the density of affine-line bad seeds for `W`.
-/
lemma exists_line_bound [Fintype F] [Fintype ι] {s : ℕ} (hs : 1 ≤ s)
    (LC : LinearCode ι F) (U : Fin (s + 1) → (ι → F)) (γ : unitInterval) :
    ∃ W : Fin 2 → (ι → F),
      (1 - 1 / (Fintype.card F : ℝ)) *
        (((Finset.univ.filter (fun x : Fin s → F =>
            IsMCA (AffineSpaceGenerator F s) LC x U γ)).card : ℝ) / (Fintype.card F) ^ s)
      ≤ ((Finset.univ.filter (fun t : F =>
            IsMCA (AffineLineGenerator F) LC t W γ)).card : ℝ) / (Fintype.card F) := by
  -- Witness function. For each `x` choose `T x : Finset ι` such that `isB x` implies:
  -- `(T x).card ≥ card ι * (1-γ)`, `projectedWord (affineComb U x) (T x) ∈ projectedCode_submod
  -- LC (T x)`, and `∃ j, projectedWord (U j) (T x) ∉ projectedCode_submod LC (T x)`.
  -- `isB`/`Bset` are the `Finset`-valued counterpart of `MCABadSeed LC U γ`: `isB` is the
  -- membership predicate for the bad-seed subtype, and `Bset` its `Finset.filter` realization,
  -- used here for cardinality counting rather than `Fintype.card` on the subtype.
  set isB := fun x => IsMCA (AffineSpaceGenerator F s) LC x U γ
  set Bset := Finset.univ.filter isB
  set m := Bset.card
  obtain ⟨T, hT⟩ :
    ∃ T : (Fin s → F) → (Finset ι), ∀ x, isB x → (T x).card ≥ (Fintype.card ι) * (1 - (γ : ℝ)) ∧
      projectedWord (affineComb U x) (T x) ∈ projectedCode_submod LC (T x) ∧
      ∃ j, projectedWord (U j) (T x) ∉ projectedCode_submod LC (T x) := by
    choose! T hT using fun x (hx : isB x) => hx
    use T
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin s → F, (Bset.filter (fun x => projectedWord (linComb U lam) (T x)
                       ∈ projectedCode_submod LC (T x))).card ≤ m / (Fintype.card F : ℝ) := by
    -- For each bad seed `x`, the kernel bound (Step 2) caps the number of `lam` whose combination
    -- projects into the code on `T x` by `|F| ^ (s - 1)`.
    have h_per_seed_le : ∀ x ∈ Bset, ∑ lam : Fin s → F, (if projectedWord (linComb U lam) (T x) ∈
                projectedCode_submod LC (T x) then 1 else 0) ≤ (Fintype.card F) ^ (s - 1) := by
      intro x hx
      have h_ker : ∃ i : Fin s, projectedWord (U i.succ) (T x) ∉ projectedCode_submod LC (T x) :=
        exists_succ_not_mem LC (T x) U x (hT x (Finset.mem_filter.mp hx |>.2) |>.2.1)
              (hT x (Finset.mem_filter.mp hx |>.2) |>.2.2)
      have h_proj_bound := proj_lincomb_ker_card_le LC (T x) (fun i => U i.succ) h_ker
      aesop
    -- Summing the per-seed bound over all bad seeds gives a bound on the total count.
    have h_sum : ∑ lam : Fin s → F, (Bset.filter (fun x => projectedWord (linComb U lam) (T x) ∈
                  projectedCode_submod LC (T x))).card ≤ m * (Fintype.card F) ^ (s - 1) := by
      convert Finset.sum_le_sum h_per_seed_le using 1
      · rw [Finset.sum_comm, Finset.sum_congr rfl]
        aesop
      · simp +zetaDelta
    -- By averaging, some `lam` achieves at most the average count.
    have havg := exists_avg_le hs (fun lam => (Bset.filter (fun x => projectedWord (linComb U lam)
          (T x) ∈ LC.projectedCode_submod (T x) ) |> Finset.card)) m ?_
    · exact havg.imp fun x hx => by rwa [le_div_iff₀' (Nat.cast_pos.mpr <| Fintype.card_pos)]
    · linarith
  obtain ⟨v, hv⟩ : ∃ v : Fin s → F, ((Bset.filter (fun x => ¬projectedWord (linComb U lam) (T x) ∈
          projectedCode_submod LC (T x))).card : ℝ) / (Fintype.card F) ^ s ≤
          ((Finset.univ.filter (fun t : F => v + t • lam ∈ Bset ∧
           ¬projectedWord (linComb U lam) (T (v + t • lam)) ∈
           projectedCode_submod LC (T (v + t • lam)))).card : ℝ) / (Fintype.card F) := by
    have hdir := exists_dir_line_ge lam (Bset.filter fun x => ¬projectedWord (linComb U lam) (T x) ∈
            LC.projectedCode_submod (T x))
    aesop
  refine ⟨![affineComb U v, linComb U lam], le_trans ?_ (hv.trans ?_ )⟩
  · convert mul_le_mul_of_nonneg_right
        (show (1 - 1 / (Fintype.card F : ℝ)) * m ≤ (
          Finset.filter (fun x => ¬projectedWord (linComb U lam ) ( T x ) ∈
          LC.projectedCode_submod (T x)) Bset |> Finset.card : ℝ) from ?_)
          (by positivity : 0 ≤ (Fintype.card F : ℝ) ⁻¹ ^ s) using 1
    · ring
    · ring
    · rw [one_sub_div, div_mul_eq_mul_div, div_le_iff₀] <;> norm_cast <;> norm_num
      · rw [le_div_iff₀ (Nat.cast_pos.mpr <| Fintype.card_pos)] at hlam
        norm_cast at *
        rw [Int.subNatNat_eq_coe]
        push_cast
        have hcard_gt_one : Fintype.card F > 1 := Fintype.one_lt_card
        have hpartition : Finset.card (Finset.filter
              (fun x => projectedWord (linComb U lam) (T x) ∈
                projectedCode_submod LC (T x)) Bset)
            + Finset.card (Finset.filter
              (fun x => ¬projectedWord (linComb U lam) (T x) ∈
                projectedCode_submod LC (T x)) Bset) = m := by
          rw [Finset.card_filter_add_card_filter_not]
        nlinarith [hcard_gt_one, hpartition]
  · gcongr
    intro h
    use T (v + ‹_› • lam)
    simp_all only [ge_iff_le, Finset.mem_univ, line_vecMul, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.exists_fin_two, not_false_eq_true, or_true,
      and_true]
    exact ⟨hT _ (Finset.mem_filter.mp h.1 |>.2 ) |>.1,
        by simpa only [affineComb_line] using hT _ (Finset.mem_filter.mp h.1 |>.2 ) |>.2.1⟩

end AffineMCA
