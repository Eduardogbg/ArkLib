# Seeded prover oracle: fill the rewinding stub

> **Not ready to file:** the arbitrary-depth straight-line adequacy theorem against
> `Prover.runToRound` is not proved.  The branch contains the canonical straight-line
> program and direct fixed-challenge run, plus exact per-round send and fork equations,
> but the dependent `Fin.induction` round trip remains open.  Do not present this draft
> as a completed adequacy result.

## Defect

The existing black-box interface is indexed by:

```lean
(message index, statement, partial transcript)
```

The proposed interface is indexed by:

```lean
start statement | send message at run handle | feed challenge to run handle
```

The existing index has no run identity.  Repeating a query can therefore run a
randomized prover afresh, so siblings of a purported rewind need not share their prefix
coins.  This is a semantic defect for checkpoint-and-restore rewinding, not merely
missing state plumbing.

## Fix

This branch adds a prover-independent `ProverRunQuery` grammar and
`OracleSpec.seededProverOracle`.  A private append-only `RunStore` maps opaque `RunId`
handles to realized checkpoints.

At a pending challenge, the store contains the already-realized continuation
`Challenge → PrvState`.  Feeding two challenges to the same handle applies that same
stored function twice; it does not rerun the oracle computation that produced the
function.  Prover effects after a fork remain fresh, as required by the rewinding game.

`ProverInteraction.seededImpl` is the `BlackBox.CheckpointRestore` implementation in
the extractor taxonomy.  The existing `OracleSpec.proverOracle` and
`Extractor.Rewinding` stub are intentionally preserved; replacing the latter is a
separate design decision.  A strategy-carrier follow-up would be framed as
`BlackBox.PrefixOracle`.

Invalid or round-mismatched handles are totalized: they return the supplied handle and,
for `sendMsg`, an inhabited junk message, without changing the store.  The canonical
program allocates every handle it uses.

## Proven interface facts

- `seededImpl_store_appendOnly`: successful allocations append a checkpoint and never
  overwrite an existing entry.
- `seededImpl_feedChal_pure`: a valid challenge query applies the stored realized
  continuation; only normalization of later rounds can perform further oracle effects.
- `seededImpl_fork_shares_prefix`: two challenges sent to one handle use the identical
  stored continuation.
- `seededImpl_sendMsg_eq_processRound`: a valid send query is exactly
  `P.sendMessage` followed by checkpoint normalization.

The branch also defines `straightlineScript{To}` and `runToRoundFixed`.  Their
arbitrary-depth equality is **not yet a theorem**.  The approved R1 fallback is to state
an alternating-protocol restriction as explicit generality debt if the fully general
dependent induction cannot be completed; no restriction or behavioral hypothesis on
the prover may be introduced.

## Verification

```text
lake build ArkLib.OracleReduction.Security.Rewinding
Build completed successfully (2953 jobs).
```

The `#guard_msgs` gates for every new theorem report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Sorry delta in `ArkLib/OracleReduction/Security/Rewinding.lean`: **0**.  The only
`sorry` strings in the file remain in the two pre-existing commented-out stub
declarations.

## Scope

One existing file is changed, additively.  No existing declaration is deleted, and no
upstream issue or pull request is opened by this preparation.
