## What was not verified

- No full-repository build was run. This wave ran only
  `lake build ArkLib.Data.Hash.Poseidon2` at upstream `main` `fad5cbf8`.
- Plonky3 and Noir/TACEO were not independently executed. The KoalaBear vectors are
  carried from leanSpec `7d16d183`; the BN254-T4 vectors are carried from lampe, which
  validates them against Noir/TACEO.
- The targeted build succeeds, but the current head toolchain reports seven
  `overlappingInstances` linter warnings in the new sponge helpers (`init`,
  `addCacheToState`, `performDuplex`, `absorb?`, `squeeze?`, `absorbPrefix?`, and
  `hashWithIV?`). This PR does not claim a warning-free build.
- The first two diagnostic rows in the KAT triangulation table below were established
  while preparing the schedule fix and were not rerun in this wave.
- Upstream CI was not run. The bundled fork PR #2 triggered
  [fork CI](https://github.com/Eduardogbg/ArkLib/actions/runs/30479384529) at
  `91f7929a`; it was queued when this text was refreshed.

## Summary

This is the field-generic refactor on top of the schedule-only fix. It generalizes
`Params` and `permute` from KoalaBear to an arbitrary field, preserves the corrected
round-constant schedule structurally, and adds a BN254 scalar-field width-4 instance with
two permutation and two sponge KATs.

The intended base is `fix/poseidon2-rc-schedule` at `7ac4f10e`; the refactor commit is
`df7e40f7`. The schedule fix remains independently reviewable and cherry-pickable.

## Changes

- `Params F` now carries the S-box exponent, width, round counts, internal diagonal,
  external layer, and round constants.
- `params16` and `params24` retain their names and reordered KoalaBear tables. Their
  `native_decide` KATs now exercise the generic path.
- Full-round chunks are read with `Vector.ofFn` at `round * width`, with bounds discharged
  by `omega`; the slicing lemmas are no longer needed.
- `cheapExternalLayer4` implements the dedicated width-4 external matrix, while
  `m4DiffusionExternalLayer` retains the wider `M4` block-and-diffusion construction used
  by widths 16 and 24.
- `Poseidon2.BN254.paramsBN254T4` uses the existing
  `CompPoly.Fields.BN254.ScalarField`, an `x^5` S-box, TACEO/Noir constants, and a cached
  additive sponge. No new dependency is introduced.

## KAT coverage

The KoalaBear schedule triangulation carried by the base fix is:

| Permute code | Constant table | Expected vector | Result |
| --- | --- | --- | --- |
| upstream `main` (stride bug) | pre-#251 in-tree order | leanSpec Sep-2025 | `false` |
| stride fixed | pre-#251 in-tree order | leanSpec Sep-2025 | `true` |
| stride fixed | reordered Plonky3 order | leanSpec `7d16d183`, widths 16 and 24 | `true` |

The refactor preserves the third row through the generic path. It also elaborates four
BN254-T4 `native_decide` vectors: permutations of `[0,1,2,3]` and `[1,2,3,4]`, the
fixed-length hash of `[1,2,3]`, and the variable-length hash of `[1,2]`.

## Verification

At bundled head `df7e40f7`, rebased on upstream `main` `fad5cbf8`:

```text
$ lake build ArkLib.Data.Hash.Poseidon2
⚠ [1915/1915] Built ArkLib.Data.Hash.Poseidon2 (12s)
warning: seven overlapping-instance linter sites in the sponge helpers
Build completed successfully (1915 jobs).
```

The KATs elaborate at the head toolchain, and the diff adds no `sorry`.

`#print axioms` was run for every named declaration added or changed by this refactor.
Results are grouped below exactly by dependency set:

```text
[propext]:
  Poseidon2.Params
  Poseidon2.Params.instNeZeroNatWidth
  Poseidon2.Params.instNeZeroNatNumFullRounds
  Poseidon2.Params.instNeZeroNatNumPartialRounds
  Poseidon2.Params.width_pos
  Poseidon2.Params.widthDiv4
  Poseidon2.Params.widthDiv4_mul_4_eq_width
  Poseidon2.Params.halfNumFullRounds
  Poseidon2.zeroVector
  Poseidon2.SpongeParams.init
  Poseidon2.SpongeParams.addCacheToState
  Poseidon2.SpongeParams.performDuplex
  Poseidon2.SpongeParams.absorb?
  Poseidon2.SpongeParams.squeeze?
  Poseidon2.SpongeParams.absorbPrefix?
  Poseidon2.SpongeToyTest.testParams

[propext, Quot.sound]:
  Poseidon2.Params.numFullRounds_dvd_by_2
  Poseidon2.Params.halfNumFullRounds_mul_2_eq_numFullRounds
  Poseidon2.Params.half_full_le
  Poseidon2.m4Matrix
  Poseidon2.applyM4
  Poseidon2.cheapExternalLayer4
  Poseidon2.internalLinearLayer
  Poseidon2.fullRound
  Poseidon2.partialRound
  Poseidon2.fullRoundChunk
  Poseidon2.permute
  Poseidon2.SpongeParams.hashWithIV?

[propext, Classical.choice, Quot.sound]:
  Poseidon2.m4DiffusionExternalLayer
  Poseidon2.params16
  Poseidon2.params24
  Poseidon2.BN254.matDiagM1
  Poseidon2.BN254.roundConstants88
  Poseidon2.BN254.paramsBN254T4
  Poseidon2.BN254.bn254Sponge
  Poseidon2.BN254.noirIV
  Poseidon2.BN254.noirHash?

No axioms:
  Poseidon2.SpongeParams
  Poseidon2.SpongeState
  Poseidon2.BN254.Fr
  Poseidon2.BN254.c
  Poseidon2.BN254.vals
  Poseidon2.BN254.val?
```
