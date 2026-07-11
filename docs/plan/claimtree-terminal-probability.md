# WIP: terminal probability bound for sound claim trees

## Scope and base

This work targets `ClaimTree.IsSound.bound_terminalProb` in
`ArkLib/Interaction/Security/ClaimTree.lean`. It is based on upstream PR #433's
`quang/core-rebuild` branch, mirrored on the fork as `quang/core-rebuild`.

The branch adapts the approximately 155-line proof draft that was commented out
immediately below the theorem. The adaptation removes the placeholder `sorry`
and activates that draft, but it is **not build-verified**.

## Proof argument

The proof proceeds by induction on the claim tree.

- A completed tree has terminal error probability zero because the starting
  claim is assumed bad.
- At a sender node, soundness keeps the claim bad for every prover-selected
  message. The induction hypothesis bounds each child by its path error, and a
  weighted sum over prover outputs is bounded by the supremum of those child
  errors.
- At a receiver node, split on whether the sampled challenge makes the claim
  good. Soundness bounds that event by the node error. Conditional on the claim
  remaining bad, the induction hypothesis bounds the continuation by the
  supremum of child errors. The bind/event union bound then gives their sum,
  exactly `maxPathError` for the receiver node.

## Remaining verification

Run `lake build` to confirm the adapted proof. If it fails, use the first Lean
diagnostic to update the draft for the current `ProbComp` event/bind lemmas and
the current dependent transcript types, then rerun the targeted build until the
theorem closes without `sorry`.
