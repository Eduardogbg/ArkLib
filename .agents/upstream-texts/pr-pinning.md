Title: fix(security): pin tree-special-sound extractor

Body:

> Not done in this wave: no upstream PR was opened and no full-repository build was run locally.
> After this text was committed, the clean-build step in
> [fork CI run 30519277986](https://github.com/Eduardogbg/ArkLib/actions/runs/30519277986)
> passed with `Build completed successfully (4122 jobs)`. The overall workflow remained red only
> because its later validation-wrapper step reported the unrelated knowledge-base error
> `Paper page without matching BibTeX key: docs/kb/papers/NOZ26.md`. This independent branch was
> rebuilt from `main` at `fad5cbf808774838924dc8273715724c6a6caa1f`; the touched Security module,
> the compatibility probe, the positive witness, and guarded axiom reports were compiled locally
> in this wave. Sorry delta: `+0 / -0`.

## Degenerate satisfaction at the current signature

The issue probe compiles at current `main` and proves that, with `[Inhabited WitIn]`, the bare
existential is classically equivalent to an extractor-free language implication:

```lean
theorem treeSpecialSound_iff_language [Inhabited WitIn] … :
    verifier.treeSpecialSound init impl S relIn relOut ↔
      ∀ stmtIn,
        (∃ tree, tree.IsStructured S ∧ tree.IsAccepting …) →
        stmtIn ∈ relIn.language
```

The forward direction is hypothesis-free. The reverse direction uses `Classical.choice` to
manufacture an extractor and `default` only away from structured accepting trees. Therefore the
existential over a bare function has no computability or cost content.

## Signature-preserving fix

Expose the pinned form and keep the existing property as its existential closure:

```lean
def treeSpecialSoundWith … (E : Extractor.TreeBased …) : Prop :=
  ∀ stmtIn tree, tree.IsStructured S → tree.IsAccepting … →
    (stmtIn, E stmtIn tree) ∈ relIn

def treeSpecialSound … : Prop :=
  ∃ E, verifier.treeSpecialSoundWith init impl S relIn relOut E

theorem treeSpecialSound_iff … : treeSpecialSound … ↔ ∃ E, ∀ stmtIn tree, … :=
  Iff.rfl
```

No existing caller's statement changes. Composition code continues to consume the existential
closure; future rewinding code can take `treeSpecialSoundWith` and run the concrete extractor.

This seam matches an existing upstream use. PR
[#602](https://github.com/Verified-zkEVM/ArkLib/pull/602) added
[`treeSpecialSound_of_isEmpty_challengeIdx`](https://github.com/Verified-zkEVM/ArkLib/blob/fad5cbf808774838924dc8273715724c6a6caa1f/ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/NoChallenge.lean#L104-L114),
which takes extractor data `e`, constructs a concrete tree extractor, and closes the existential
immediately. The pinned form exposes exactly the intermediate fact that theorem already builds.

## Positive non-vacuity witness

Mirroring the role of `Verifier.id_knowledgeSoundness` in
[#569](https://github.com/Verified-zkEVM/ArkLib/pull/569), this change proves the strengthened
predicate at a concrete extractor:

```lean
theorem Verifier.id_treeSpecialSoundWith (S : ChallengeTreeShape !p[])
    (relOut : Set (StmtIn × WitOut)) :
    (Verifier.id : Verifier oSpec StmtIn StmtIn !p[]).treeSpecialSoundWith
      init impl S {pair | pair.1 = pair.2} relOut (fun stmtIn _ => stmtIn) := by
  intro stmtIn _ _ _
  rfl
```

The identity verifier and the extractor that returns the input statement inhabit
`treeSpecialSoundWith` for the diagonal relation. No assumption was added to make this theorem
provable.

## Verification

On this branch, the complete issue probe exits zero:

```text
$ lake env lean probes/TreeSpecialSoundProbes.lean
$ echo $?
0
```

That includes probe 1 after the refactor. It also intentionally includes the arity-zero probe:
this branch does not contain the independent arity guard. The sibling
`fix/distinct-shape-arity-guard` branch is where that instantiation is type-rejected.

Targeted build:

```text
$ lake build ArkLib.OracleReduction.Security.TranscriptTree.Basic
✔ [2953/2953] Built ArkLib.OracleReduction.Security.TranscriptTree.Basic (7.0s)
Build completed successfully (2953 jobs).
```

The in-file `#guard_msgs` checks compile these exact axiom reports:

```text
'Verifier.treeSpecialSoundWith' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Verifier.treeSpecialSound' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Verifier.treeSpecialSound_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Verifier.id_treeSpecialSoundWith' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

This follows the same validation shape as the merged vacuity fixes
[#569](https://github.com/Verified-zkEVM/ArkLib/pull/569) and
[#577](https://github.com/Verified-zkEVM/ArkLib/pull/577): compiled degenerate satisfaction first,
minimal signature-preserving repair, a positive witness in the same change, and an explicit sorry
and axiom report.
