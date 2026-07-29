## What was not verified

- No full-repository build was run. This wave ran only
  `lake build ArkLib.Data.Hash.Poseidon2` at upstream `main` `fad5cbf8`.
- Plonky3 was not executed. The in-tree width-16 and width-24 vectors come from
  `leanEthereum/leanSpec` at `7d16d183`, whose Poseidon2 constants were reordered by
  [leanSpec#251](https://github.com/leanEthereum/leanSpec/pull/251) to match Plonky3.
- The first two diagnostic rows in the triangulation table below were established while
  preparing the fix and were not rerun in this wave. This wave re-elaborated the two
  current in-tree KATs.
- Upstream CI and style/lint CI were not run. The split branch was pushed to the fork,
  but no fork CI run is visible because it does not have a pull request.

## Summary

`Poseidon2.permute` produces wrong digests for both existing parameter sets because two
independent parts of the round-constant schedule disagree with the reference:

1. Both full-round halves stride width-sized constant windows by the round index instead
   of by `round * width`.
2. `rawConstants16` and `RAW_CONSTANTS_24` use the pre-leanSpec#251 order, with the
   internal constants after both external halves instead of between them.

This commit fixes both defects and adds `native_decide` known-answer tests for widths 16
and 24. It is the only commit on `fix/poseidon2-rc-schedule` and is independently
cherry-pickable.

## Full-round stride

Both full-round halves previously sliced a width-sized chunk as:

```lean
rcs.extract rc_idx (rc_idx + params.width)
```

Here `rc_idx` is the round index, so consecutive rounds read overlapping windows
`[0, width)`, `[1, width + 1)`, and so on. The corrected offset is
`rc_idx * params.width`.

The private length lemmas did not detect the bug because they only proved that each
extracted window had length `width`; that remains true at the wrong offset. Their
statements and proofs now use the corrected offset. The partial-round path was already
correct: it starts after `halfNumFullRounds * width` constants and consumes one constant
per partial round.

## Constant-table order

The two KoalaBear tables were copied from leanSpec before leanSpec#251 moved the internal
constants between the two external halves. This commit reorders the same constants into
`[external-first | internal | external-second]`, which is the order `permute` consumes.

The diagnostic matrix from preparation was:

| Permute code | Constant table | Expected vector | Result |
| --- | --- | --- | --- |
| upstream `main` (stride bug) | pre-#251 in-tree order | leanSpec Sep-2025 | `false` |
| stride fixed | pre-#251 in-tree order | leanSpec Sep-2025 | `true` |
| stride fixed | reordered Plonky3 order | leanSpec `7d16d183`, widths 16 and 24 | `true` |

The first two rows isolate the two defects. The third row is represented by the two
in-tree KATs and was rerun in this wave.

## Verification

At `fix/poseidon2-rc-schedule` `7ac4f10e`, rebased on upstream `main` `fad5cbf8`:

```text
$ lake build ArkLib.Data.Hash.Poseidon2
✔ [1914/1914] Built ArkLib.Data.Hash.Poseidon2 (20s)
Build completed successfully (1914 jobs).
```

The targeted build emitted no warnings. The diff adds no `sorry`.

`#print axioms` was run in the module after every named changed declaration, including
the two private slicing lemmas:

```text
'Poseidon2.rawConstants16' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poseidon2.RAW_CONSTANTS_24' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.ArkLib.Data.Hash.Poseidon2.0.Poseidon2.firstHalfRoundConstants_extract_length'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.ArkLib.Data.Hash.Poseidon2.0.Poseidon2.secondHalfRoundConstants_extract_length'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'Poseidon2.permute' depends on axioms: [propext, Classical.choice, Quot.sound]
```
