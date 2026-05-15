/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.NNReal.Basic
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Hamming ball volume

ABF26 Definition 2.4: the volume of a Hamming ball.

  `Vol_q(δ, n) := ∑_{i=0}^{⌊δ · n⌋} (n choose i) · (q-1)^i`

Counts the number of words in `Σ^n` (with `|Σ| = q`) within absolute Hamming
distance `⌊δ · n⌋` of any fixed center. Independent of the choice of center.

Used in:

- ABF26 Lemma 3.7 (Elias lower bound for `|Λ(C, δ)|`).
- ABF26 Corollary 3.8 (volume-based lower bound).

This file also provides the bridge between the volume function and the existing
`hammingBall` set in `ListDecodability.lean`.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace CodingTheory

/-- **ABF26 Definition 2.4.** Volume of the Hamming ball of relative radius `δ` over
an alphabet of size `q` and block length `n`:

  `Vol_q(δ, n) := ∑_{i=0}^{⌊δ · n⌋} (n choose i) · (q-1)^i`.

Counts the number of words in `Σ^n` (with `|Σ| = q`) within absolute Hamming distance
`⌊δ · n⌋` of any fixed center. Independent of the choice of center.

Used in `ABF26-L3.7` (Elias lower bound) and `ABF26-C3.8` (volume-based lower bound).

Noncomputable because the floor `⌊δ · n⌋₊` over `ℝ` is noncomputable (Mathlib's
`Nat.floor` on `ℝ` depends on a `noncomputable` `linearOrder` instance). -/
noncomputable def hammingBallVolume (q : ℕ) (δ : ℝ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (⌊δ * n⌋₊ + 1), Nat.choose n i * (q - 1) ^ i

@[simp]
lemma hammingBallVolume_zero_radius (q n : ℕ) : hammingBallVolume q 0 n = 1 := by
  simp [hammingBallVolume]

/-- **Key combinatorial identity.** The number of vectors `x : ι → F` at Hamming
distance exactly `i` from a fixed `y` is `C(n, i) · (q-1)^i`, where `n = |ι|` and
`q = |F|`. Independent of `y`.

Proof via an explicit bijection: `x` corresponds to the pair `(S, f)` where
`S := {j | x j ≠ y j}` (an `i`-element subset of `ι`) and `f : S → F` is the
restriction of `x` to `S` (each value forced into `F \ {y j}`). Counting:
`Σ S ∈ powersetCard i univ, ∏ j ∈ S, (|F| - 1) = C(n, i) · (q-1)^i`. -/
lemma card_filter_hammingDist_eq
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Fintype F] [DecidableEq F] (y : ι → F) (i : ℕ) :
    (Finset.univ.filter (fun x : ι → F => hammingDist y x = i)).card
      = Nat.choose (Fintype.card ι) i * (Fintype.card F - 1) ^ i := by
  sorry -- combinatorial; bijection to powersetCard × (F \ {y _})

/-- **Bridge to `hammingBall`.** The volume function counts the cardinality of the
existing `hammingBall` (set of words within radius `⌊δ·n⌋` of any fixed center). The
identity collapses to the standard combinatorial fact
`#{x ∈ F^n : Δ(x, y) ≤ r} = ∑_{i ≤ r} C(n, i) · (q-1)^i` independent of `y`.

Proof: partition `hammingBall y r` by exact distance via `card_filter_hammingDist_eq`,
then sum. -/
theorem hammingBallVolume_eq_ncard_hammingBall
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Fintype F] [DecidableEq F] (δ : ℝ) (y : ι → F) :
    hammingBallVolume (Fintype.card F) δ (Fintype.card ι)
      = (ListDecodable.hammingBall (F := F) y (⌊δ * Fintype.card ι⌋₊)).ncard := by
  set r : ℕ := ⌊δ * Fintype.card ι⌋₊
  -- Step 1: convert RHS ncard → Finset.card with explicit filter.
  have h_rhs :
      (ListDecodable.hammingBall (F := F) y r).ncard
        = (Finset.univ.filter (fun x : ι → F => hammingDist y x ≤ r)).card := by
    have h_finite : (ListDecodable.hammingBall (F := F) y r).Finite := Set.toFinite _
    rw [Set.ncard_eq_toFinset_card _ h_finite]
    apply Finset.card_bij (fun x _ => x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Set.Finite.mem_toFinset, ListDecodable.hammingBall, Set.mem_setOf_eq] at hx
      convert hx using 2
    · intros; assumption
    · intro x hx
      refine ⟨x, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Set.Finite.mem_toFinset, ListDecodable.hammingBall, Set.mem_setOf_eq]
      convert hx using 2
  -- Step 2: partition by exact distance.
  have h_partition :
      (Finset.univ.filter (fun x : ι → F => hammingDist y x ≤ r)).card
        = ∑ i ∈ Finset.range (r + 1),
            (Finset.univ.filter (fun x : ι → F => hammingDist y x = i)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
        Finset.mem_univ, true_and]
      refine ⟨fun h => ⟨hammingDist y x, by omega, rfl⟩,
              fun ⟨i, hi, hd⟩ => ?_⟩
      omega
    · -- disjointness
      intro a _ b _ hab
      simp only [Finset.disjoint_filter, Finset.mem_univ, true_implies]
      intro _ hxa hxb
      exact hab (hxa.symm.trans hxb)
  -- Combine.
  rw [h_rhs, h_partition]
  unfold hammingBallVolume
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (card_filter_hammingDist_eq y i).symm

end CodingTheory
