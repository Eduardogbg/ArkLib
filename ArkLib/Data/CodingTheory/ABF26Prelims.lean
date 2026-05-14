/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.NNReal.Basic
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Preliminaries specific to ABF26

Definitions from `ABF26.pdf` §2 (Preliminaries) that aren't already in ArkLib or Mathlib.

- `CodingTheory.qEntropy` — ABF26 Definition 2.2: `q`-ary entropy function `H_q`.
- `CodingTheory.restrictedRelHammingDist` — ABF26 Definition 2.3: `Δ_T(f, g)`, the
  fractional Hamming distance restricted to a subset `T`.
- `CodingTheory.hammingBallVolume` — ABF26 Definition 2.4: `Vol_q(δ, n)`.

These show up in:
- ABF26 Corollary 3.8 (volume-based lower bound for `|Λ(C, δ)|`).
- ABF26 Theorem 3.11 (random-linear-code lower bound) and Theorem 4.17 (capacity-regime CA
  breakdown), which involve `H_q` directly.
- ABF26 Definition 4.1 and 4.3 (`ε_ca`, `ε_mca`), which use `Δ_S` over a subset `S` of the
  block-length type. The existing `ε_ca` / `ε_mca` formalisations in `EpsilonErrors.lean`
  inline the restricted-distance condition pointwise; `restrictedRelHammingDist` here is
  the standalone definition for downstream proofs that want to manipulate it directly.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace CodingTheory

open Real NNReal

/-- **ABF26 Definition 2.2.** `q`-ary entropy function:

  `H_q(x) := x · log_q(q-1) - x · log_q(x) - (1-x) · log_q(1-x)`.

For `q = 2` this reduces to the standard binary entropy function. Mathlib's convention
`Real.log 0 = 0` makes the boundary cases `qEntropy q 0 = 0` and
`qEntropy q 1 = log_q (q-1)` well-defined (treating `0 · log 0 = 0` and
`log_q 1 = 0` automatically).

**Boundary behaviour for `q ≤ 1`.** The paper assumes `q ≥ 2` (alphabet size of an
error-correcting code). For `q ∈ {0, 1}`, `Real.logb q _` is identically `0` (since
`Real.log q = 0` there), so `qEntropy 0 x = qEntropy 1 x = 0` regardless of `x`. This
is mathematically uninformative but well-defined; downstream consumers that need a
meaningful q-ary entropy should guard with `2 ≤ q` themselves (as T4.17 does with
`10 ≤ Fintype.card F`, and T3.11 does via `Nat.Prime q`).

The paper's `H_S(x) := H_{|S|}(x)` set-entropy overload is provided as a wrapper at the
call site (a one-line `qEntropy (Fintype.card S) x`). -/
noncomputable def qEntropy (q : ℕ) (x : ℝ) : ℝ :=
  x * Real.logb q (q - 1) - x * Real.logb q x - (1 - x) * Real.logb q (1 - x)

@[simp]
lemma qEntropy_zero (q : ℕ) : qEntropy q 0 = 0 := by
  simp [qEntropy]

/-- **ABF26 Definition 2.3.** Restricted (fractional) Hamming distance:
`Δ_T(f, g) = Pr_{i ← T}[f i ≠ g i]`, equivalently the fraction of positions in `T` on
which `f` and `g` differ.

By NNReal's `0 / 0 = 0` convention this returns `0` when `T = ∅`, matching the intuition
that "the empty distribution agrees vacuously". -/
noncomputable def restrictedRelHammingDist
    {ι : Type*} [DecidableEq ι] {α : Type*} [DecidableEq α]
    (T : Finset ι) (f g : ι → α) : ℝ≥0 :=
  ((T.filter (fun i => f i ≠ g i)).card : ℝ≥0) / (T.card : ℝ≥0)

@[simp]
lemma restrictedRelHammingDist_self
    {ι : Type*} [DecidableEq ι] {α : Type*} [DecidableEq α]
    (T : Finset ι) (f : ι → α) : restrictedRelHammingDist T f f = 0 := by
  simp [restrictedRelHammingDist]

/-- **Bridge to `Code.relHammingDist`.** When `T = Finset.univ`, the restricted relative
Hamming distance coincides with ArkLib's existing `Code.relHammingDist` (cast to `ℝ≥0`).
Lets downstream theorems convert freely between the paper's `Δ_T` (this file) and the
existing `δᵣ(u, v)` notation in `Basic/RelativeDistance.lean`. -/
lemma restrictedRelHammingDist_univ
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type*} [DecidableEq F] (f g : ι → F) :
    restrictedRelHammingDist Finset.univ f g
      = ((Code.relHammingDist f g : ℚ≥0) : ℝ≥0) := by
  simp only [restrictedRelHammingDist, Code.relHammingDist, hammingDist,
    Finset.card_univ]
  push_cast
  rfl

/-- **ABF26 Definition 2.4.** Volume of the Hamming ball of relative radius `δ` over an
alphabet of size `q` and block length `n`:

  `Vol_q(δ, n) := ∑_{i=0}^{⌊δ · n⌋} (n choose i) · (q-1)^i`.

Counts the number of words in `Σ^n` (with `|Σ| = q`) within absolute Hamming distance
`⌊δ · n⌋` of any fixed center. Independent of the choice of center.

Used in `ABF26-L3.7` (Elias lower bound) and `ABF26-C3.8` (volume-based lower bound).

Noncomputable because the floor `⌊δ · n⌋₊` over `ℝ` is noncomputable (Mathlib's `Nat.floor`
on `ℝ` depends on a `noncomputable` `linearOrder` instance). -/
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
  -- Set→Finset cardinality conversion. The two `hammingDist y x ≤ r` propositions
  -- below are propositionally equal but use different `Decidable` instances at the
  -- syntactic level (Set.Finite.toFinset uses one; my Finset.filter another). The
  -- bridge is purely a Mathlib-API/instance-elim exercise; admitted as a tagged
  -- sub-sorry while the substantive partition + counting steps proceed below.
  have h_rhs :
      (ListDecodable.hammingBall (F := F) y r).ncard
        = (Finset.univ.filter (fun x : ι → F => hammingDist y x ≤ r)).card := by
    sorry -- Set/Finset card conversion; Decidable-instance mismatch.
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
