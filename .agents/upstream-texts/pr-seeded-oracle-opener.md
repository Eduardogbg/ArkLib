# Seeded prover oracle: fill the rewinding stub

The arbitrary-depth straight-line adequacy theorem is proved against the repository's
actual `Prover.runToRound` semantics.  The result observes both the transcript and final
prover checkpoint, so a constant-transcript or junk-handler implementation cannot
satisfy it.

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

- `seededImpl_store_appendOnly`: for every handler query and every result in the
  computation's support, the returned store has the input store as a prefix.  Thus no
  successful, pure, or junk path can overwrite an existing entry.
- `seededImpl_feedChal_pure`: a valid challenge query applies the stored realized
  continuation; only normalization of later rounds can perform further oracle effects.
- `seededImpl_fork_shares_prefix`: two challenges sent to one handle use the identical
  stored continuation.
- `seededImpl_sendMsg_eq_processRound`: a valid send query is exactly
  `P.sendMessage` followed by checkpoint normalization.
- `seededImpl_straightline_eq_runToRound`: simulating the canonical
  `straightlineScript` through `seededImpl` is equal to
  `simulateQ fixedChallengeImpl (P.runToRound ...)`, after observing the returned
  transcript and checkpoint.  The proof is fully general over protocol directions and
  uses no behavioral hypothesis on the prover.

## Verification

```text
lake build ArkLib.OracleReduction.Security.Rewinding
Build completed successfully (2953 jobs).
```

The `#guard_msgs` gates pin every new theorem to its exact axiom set, each a subset of:

```text
[propext, Classical.choice, Quot.sound]
```

Sorry delta in `ArkLib/OracleReduction/Security/Rewinding.lean`: **0**.  The only
`sorry` strings in the file remain in the two pre-existing commented-out stub
declarations.

## Scope

One Lean source file is changed additively, along with this draft.  No existing
declaration is deleted, and no upstream issue or pull request is opened by this
preparation.
