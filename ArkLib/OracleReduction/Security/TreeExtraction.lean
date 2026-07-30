/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Gomes
-/

import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

/-!
# Error and cost bounds for tree extraction

The knowledge-error and expected-cost quantities in the tree-extraction reduction of
[ACK21, Thm. 1], specialized to uniform arity `k`, `depth` challenge rounds, and challenge
sets of size `N`:

- `ackKnowledgeError k N depth = depth · (k - 1) / N` is the additive knowledge error;
- `ackPolyBound k depth = ∑_{d = 1}^{depth} k ^ d` is the number of edges in the
  `(k, ..., k)` extraction tree;
- `ackNecessaryTranscripts k depth = k ^ depth` is the number of leaves, hence accepting
  transcripts, in that tree.

The last two quantities use different accounting units. [ACK21, Lem. 5] bounds expected
queries to the prover in complete-run units by the leaf count, while `ackPolyBound` counts
individual per-round resumptions. They determine each other exactly (`ackPolyBound_exact`);
for `k ≥ 2`, the edge count is at most twice the leaf count
(`ackPolyBound_le_two_mul`).

## References

- [ACK21] Attema, Cramer, Kohl, *A Compressed Σ-Protocol Theory for Lattices*,
  ePrint 2021/307.
- [AFK21] Attema, Fehr, Klooß, *Fiat-Shamir Transformation of Multi-Round Interactive
  Proofs*, ePrint 2021/1377.
-/

namespace Interaction.Security

open scoped ENNReal

section ACK

/-- The additive knowledge error at uniform arity `k` over `depth` rounds with `N`-sized
challenge sets: `κ = depth · (k - 1) / N`, the union bound from [ACK21, Thm. 1].
[AFK21, Eq. (1)] restates the corresponding exact expression as `Er(k; N)`.

This is the linear budget obtained by summing the per-level errors, rather than the tighter
exact expression `1 - (1 - (k - 1) / N) ^ depth`. -/
noncomputable def ackKnowledgeError (k N depth : ℕ) : ℝ≥0∞ :=
  (depth : ℝ≥0∞) * (((k : ℝ≥0∞) - 1) / (N : ℝ≥0∞))

/-- The expected-cost bound at uniform arity `k` over `depth` rounds, measured in
per-round resumption units: the edge count `∑_{d = 1}^{depth} k ^ d` from the recurrence
`C(d + 1) ≤ k · (1 + C(d))`, `C(0) = 0`, in [ACK21, Lem. 5, §3.2].

In complete-run units the same tree has cost bounded by the leaf count `k ^ depth`; see
`ackPolyBound_exact` and `ackPolyBound_le_two_mul`. -/
noncomputable def ackPolyBound (k depth : ℕ) : ℝ≥0∞ :=
  ∑ d ∈ Finset.range depth, (k : ℝ≥0∞) ^ (d + 1)

/-- The necessary transcript count at uniform arity `k` over `depth` rounds:
`K = ∏ kᵢ = k ^ depth`, the number of accepting transcripts at the leaves of the
extraction tree from [ACK21, Def. 9]. This is a deterministic output count, not the
per-round draw cost `ackPolyBound`. -/
noncomputable def ackNecessaryTranscripts (k depth : ℕ) : ℝ≥0∞ :=
  (k : ℝ≥0∞) ^ depth

/-- `ackNecessaryTranscripts k depth = ∏ kᵢ` at uniform arity `k`, the product form of
[ACK21, Def. 9] specialized to constant arity. -/
theorem ackNecessaryTranscripts_eq_prod (k depth : ℕ) :
    ackNecessaryTranscripts k depth = ∏ _ ∈ Finset.range depth, (k : ℝ≥0∞) := by
  rw [ackNecessaryTranscripts, Finset.prod_const, Finset.card_range]

/-- Natural-number core of `ackPolyBound_exact`: the geometric identity
`(k - 1) · ∑_{d = 1}^{depth} k ^ d + k = k · k ^ depth`, valid also for
`depth = 0` and `k ∈ {0, 1}`. -/
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

/-- The exact edge/leaf relation:
`(k - 1) · ackPolyBound k depth + k = k · ackNecessaryTranscripts k depth`. -/
theorem ackPolyBound_exact (k depth : ℕ) :
    ((k : ℝ≥0∞) - 1) * ackPolyBound k depth + k = k * ackNecessaryTranscripts k depth := by
  have h := congrArg (fun n : ℕ => (n : ℝ≥0∞)) (ackPolyBound_exact_nat k depth)
  push_cast [ENNReal.natCast_sub] at h
  simpa [ackPolyBound, ackNecessaryTranscripts] using h

/-- Natural-number core of `ackPolyBound_le_two_mul`, obtained from the exact geometric
identity and `k ≤ 2 * (k - 1)` for `k ≥ 2`. -/
theorem ackPolyBound_le_two_mul_nat (k depth : ℕ) (hk : 2 ≤ k) :
    (∑ d ∈ Finset.range depth, k ^ (d + 1)) ≤ 2 * k ^ depth := by
  have h1 : (k - 1) * (∑ d ∈ Finset.range depth, k ^ (d + 1)) ≤ k * k ^ depth :=
    Nat.le.intro (ackPolyBound_exact_nat k depth)
  have h2 : k * k ^ depth ≤ (k - 1) * (2 * k ^ depth) := by
    calc k * k ^ depth ≤ (2 * (k - 1)) * k ^ depth :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (k - 1) * (2 * k ^ depth) := by ring
  exact Nat.le_of_mul_le_mul_left (le_trans h1 h2) (by omega)

/-- At any arity `k ≥ 2`, the per-round resumption bound `ackPolyBound k depth` is at
most twice the accepting-transcript count `ackNecessaryTranscripts k depth`. Thus the
edge-count and complete-run bounds lie in the same polynomial class. -/
theorem ackPolyBound_le_two_mul (k depth : ℕ) (hk : 2 ≤ k) :
    ackPolyBound k depth ≤ 2 * ackNecessaryTranscripts k depth := by
  have h := (Nat.cast_le (α := ℝ≥0∞)).mpr (ackPolyBound_le_two_mul_nat k depth hk)
  push_cast at h
  simpa [ackPolyBound, ackNecessaryTranscripts] using h

/--
info: 'Interaction.Security.ackNecessaryTranscripts_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ackNecessaryTranscripts_eq_prod

/--
info: 'Interaction.Security.ackPolyBound_exact_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ackPolyBound_exact_nat

/--
info: 'Interaction.Security.ackPolyBound_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ackPolyBound_exact

/--
info: 'Interaction.Security.ackPolyBound_le_two_mul_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ackPolyBound_le_two_mul_nat

/--
info: 'Interaction.Security.ackPolyBound_le_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ackPolyBound_le_two_mul

end ACK

end Interaction.Security
