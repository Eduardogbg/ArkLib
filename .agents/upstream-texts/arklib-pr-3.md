## What is not verified or done

- No Lean build was run on this branch in the 2026-07-30 cleanup wave. The last targeted
  build reported in the previous body predates this wave and is not repeated as current
  verification.
- There is no theorem producing a transcript forest from black-box prover access, and no
  end-to-end tree-special-soundness-to-knowledge-soundness theorem in this PR.
- The black-box factoring lemma is not implemented. `Rewinding.lean` now records the
  concrete next-wave plan: re-spell `proverResumeAt` on `main`'s API, define the
  prover-oracle bridge, then prove the factoring theorem for pinned extractors.
- This branch is still based on the ArkLib #532 prototype slice
  (`upstream-pr/532-core-rebuild-1`), not `main`. Per the contribution plan, the interface
  package is slated to be re-based and re-spelled on current `main`; that proof work is
  intentionally outside this cleanup wave.

## What this PR provides

- `TranscriptForest.lean`: a selected-challenge forest carrier, distinctness and
  all-accepting predicates, leaf counting, and a pinned tree-special-soundness interface.
- `Rewinding.lean`: prover resume-from-prefix, the `Extractor.Rewinding` carrier, a run
  derived from its two-factor program, expected query cost derived from the same program,
  and acceptance-conditioned pinned/existential knowledge-soundness notions.
- The derived-cost design keeps execution and accounting attached to one program; it does
  not carry an independently asserted cost field.

This is an interface package. It does not contain the tree-producing half theorem.

## Generic pieces being split out

Standalone, main-based ports are pushed on the fork:

- ACK21 extraction arithmetic:
  https://github.com/Eduardogbg/ArkLib/tree/feat/tree-extraction-bounds
- Two-factor seeded runs, moved to VCVio:
  https://github.com/Eduardogbg/VCV-io/tree/feat/two-factor-seeded-runs

The prototype branch still contains its original local copies so that its current
#532-based dependency graph remains self-contained. They are intended to be removed from
the package during the planned rebase after the VCVio dependency is available.

## Axiom and build status

No `#print axioms` audit or Lean build was run on this prototype branch in this cleanup
wave. The two standalone ports carry `#guard_msgs`-gated `#print axioms` checks and were
target-built in their own worktrees; those checks do not verify this branch.
