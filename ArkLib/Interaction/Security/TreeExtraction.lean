/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Gomes
-/
import ArkLib.Interaction.Security.Rewinding

/-!
# Error and cost quantities for tree extraction

The knowledge error and expected-cost figures of the tree-extraction reduction of
[ACK21, Thm. 1] at uniform arity `k` over `depth` challenge rounds with challenge sets of
size `N`, in the shape consumed by `rewindingKnowledgeSoundnessAcceptingWith`
(`Security.Rewinding`):

- `ackKnowledgeError k N depth = depth · (k − 1) / N` — the additive (union-bound)
  knowledge error;
- `ackPolyBound k depth = ∑_{d = 1}^{depth} k ^ d` — the expected number of
  extractor-owned draws, i.e. the *edge* count of the `(k, …, k)`-tree;
- `ackNecessaryTranscripts k depth = k ^ depth` — the number of accepting transcripts the
  extractor assembles, i.e. the *leaf* count `K = ∏ kᵢ` of [ACK21, Def. 9].

The last two are deliberately kept in distinct units. [ACK21, Lem. 5] states its expected
cost in queries to the prover (one unit per complete run), bounded by the leaf count `K`;
`ackPolyBound` counts per-round prover resumptions (one unit per edge). The two determine
each other exactly (`ackPolyBound_exact`), and at any arity `k ≥ 2` the edge count is at
most twice the leaf count (`ackPolyBound_le_two_mul`) — the same polynomial class.

## References

- [ACK21] Attema, Cramer, Kohl, *A Compressed Σ-Protocol Theory for Lattices*,
  ePrint 2021/307.
- [AFK21] Attema, Fehr, Klooß, *Fiat–Shamir Transformation of Multi-Round Interactive
  Proofs*, ePrint 2021/1377.
-/

namespace Interaction.Security

open scoped ENNReal

section ACK

/-- The additive knowledge error at uniform arity `k` over `depth` rounds with `N`-sized
challenge sets: `κ = depth · (k − 1) / N`, the right-hand side of the union bound in
[ACK21, Thm. 1] (`κ = (N^μ − ∏(N − kᵢ + 1)) / N^μ ≤ ∑ᵢ (kᵢ − 1) / Nᵢ`; [AFK21, Eq. (1)]
restates the exact form as `Er(k; N)`).

This is the linear budget a per-level telescope proves, not the tighter exact form
`1 − (1 − (k − 1)/N)^depth` — a smaller quantity by the same union bound. -/
noncomputable def ackKnowledgeError (k N depth : ℕ) : ℝ≥0∞ :=
  (depth : ℝ≥0∞) * (((k : ℝ≥0∞) - 1) / (N : ℝ≥0∞))

/-- The expected-cost bound at uniform arity `k` over `depth` rounds, in per-round draw
units (one unit per prover resumption / extractor column draw): the edge count of the
`(k, …, k)`-tree, `∑_{d = 1}^{depth} k ^ d`, from the cost telescope
`C(d + 1) ≤ k · (1 + C(d))`, `C(0) = 0` of [ACK21, Lem. 5, §3.2]. In the papers' own unit
(complete prover runs) the same tree costs `k ^ depth` — the leaf count; see
`ackPolyBound_exact` and `ackPolyBound_le_two_mul` for the exact relation. -/
noncomputable def ackPolyBound (k depth : ℕ) : ℝ≥0∞ :=
  ∑ d ∈ Finset.range depth, (k : ℝ≥0∞) ^ (d + 1)

/-- The necessary transcript count at uniform arity `k` over `depth` rounds:
`K = ∏ kᵢ = k ^ depth`, the number of accepting transcripts (tree leaves) the extractor
assembles ([ACK21, Def. 9]; `TranscriptForestDesc.numLeaves_eq_pow`). This is a
deterministic count of the assembled output object, not a draw cost — the draw cost is
`ackPolyBound`. -/
noncomputable def ackNecessaryTranscripts (k depth : ℕ) : ℝ≥0∞ := (k : ℝ≥0∞) ^ depth

/-- `ackNecessaryTranscripts k depth = ∏ kᵢ` at uniform arity `k` — the product form of
[ACK21, Def. 9] specialized to constant arity. -/
theorem ackNecessaryTranscripts_eq_prod (k depth : ℕ) :
    ackNecessaryTranscripts k depth = ∏ _ ∈ Finset.range depth, (k : ℝ≥0∞) := by
  rw [ackNecessaryTranscripts, Finset.prod_const, Finset.card_range]

/-- ℕ core of `ackPolyBound_exact`: the geometric telescope
`(k − 1) · ∑_{d = 1}^{depth} k ^ d + k = k · k ^ depth`, with ℕ-truncated subtraction but
valid for all `k` (at `depth = 0` it reads `k = k · 1`; at `k ∈ {0, 1}` both sides
collapse). Induction on `depth`. -/
theorem ackPolyBound_exact_nat (k depth : ℕ) :
    (k - 1) * (∑ d ∈ Finset.range depth, k ^ (d + 1)) + k = k * k ^ depth := by
  induction depth with
  | zero => simp
  | succ d ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · rw [Finset.sum_range_succ, Nat.mul_add, add_right_comm, ih]
      calc k * k ^ d + (k - 1) * k ^ (d + 1)
          = 1 * k ^ (d + 1) + (k - 1) * k ^ (d + 1) := by
            rw [one_mul, pow_succ, mul_comm (k ^ d) k]
        _ = (1 + (k - 1)) * k ^ (d + 1) := (add_mul _ _ _).symm
        _ = k * k ^ (d + 1) := by rw [Nat.add_sub_cancel' hk]

/-- The exact edge/leaf relation: the draw-cost bound `ackPolyBound k depth` (edges) and
the necessary transcript count `ackNecessaryTranscripts k depth` (leaves) determine each
other by `(k − 1) · ackPolyBound + k = k · ackNecessaryTranscripts`, at every `depth`
(at `depth = 0`: `k = k · 1`) and every `k`. -/
theorem ackPolyBound_exact (k depth : ℕ) :
    ((k : ℝ≥0∞) - 1) * ackPolyBound k depth + k = k * ackNecessaryTranscripts k depth := by
  have h := congrArg (fun n : ℕ => (n : ℝ≥0∞)) (ackPolyBound_exact_nat k depth)
  push_cast [ENNReal.natCast_sub] at h
  simpa [ackPolyBound, ackNecessaryTranscripts] using h

/-- ℕ core of `ackPolyBound_le_two_mul`: from the exact telescope,
`(k − 1) · ∑ k ^ d ≤ k · k ^ depth ≤ (k − 1) · (2 · k ^ depth)` (using `k ≤ 2(k − 1)` at
`k ≥ 2`), then cancel `k − 1 > 0`. -/
theorem ackPolyBound_le_two_mul_nat (k depth : ℕ) (hk : 2 ≤ k) :
    (∑ d ∈ Finset.range depth, k ^ (d + 1)) ≤ 2 * k ^ depth := by
  have h1 : (k - 1) * (∑ d ∈ Finset.range depth, k ^ (d + 1)) ≤ k * k ^ depth :=
    Nat.le.intro (ackPolyBound_exact_nat k depth)
  have h2 : k * k ^ depth ≤ (k - 1) * (2 * k ^ depth) := by
    calc k * k ^ depth ≤ (2 * (k - 1)) * k ^ depth :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (k - 1) * (2 * k ^ depth) := by ring
  exact Nat.le_of_mul_le_mul_left (le_trans h1 h2) (by omega)

/-- At any arity `k ≥ 2`, the expected-draw bound `ackPolyBound k depth` (edges) is at
most twice the necessary transcript count `ackNecessaryTranscripts k depth` (leaves) — so
the per-draw cost figure is in the same polynomial class as the per-run bound
`E[queries to the prover] ≤ K` of [ACK21, Lem. 5]. -/
theorem ackPolyBound_le_two_mul (k depth : ℕ) (hk : 2 ≤ k) :
    ackPolyBound k depth ≤ 2 * ackNecessaryTranscripts k depth := by
  have h := (Nat.cast_le (α := ℝ≥0∞)).mpr (ackPolyBound_le_two_mul_nat k depth hk)
  push_cast at h
  simpa [ackPolyBound, ackNecessaryTranscripts] using h

end ACK

end Interaction.Security
