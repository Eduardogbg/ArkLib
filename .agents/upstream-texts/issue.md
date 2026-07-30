Title: Tree special soundness: existential extractor carries no algorithmic content; distinctShape admits arity 0

Body:

> Not done in this wave: no issue or pull request was filed upstream, and no full-repository build
> was run locally. The subsequent fork CI clean-build for head `8ffa15d0` in
> [fork CI run 30519277986](https://github.com/Eduardogbg/ArkLib/actions/runs/30519277986)
> passed with `Build completed successfully (4122 jobs)`. The overall workflow remained red only
> because its later validation-wrapper step reported the unrelated knowledge-base error
> `Paper page without matching BibTeX key: docs/kb/papers/NOZ26.md`. This wave rebuilt the fix as
> two independent branches from `main` at `fad5cbf808774838924dc8273715724c6a6caa1f`, reran the
> probe below, and completed targeted builds of every touched Security module. The sorry delta is
> zero.

Two related observations concern
[`Verifier.treeSpecialSound`](https://github.com/Verified-zkEVM/ArkLib/blob/fad5cbf808774838924dc8273715724c6a6caa1f/ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean#L292-L316)
and
[`distinctShape` / `specialSound`](https://github.com/Verified-zkEVM/ArkLib/blob/fad5cbf808774838924dc8273715724c6a6caa1f/ArkLib/OracleReduction/Security/SpecialSoundness.lean#L38-L93).

## 1. The existential extractor carries no algorithmic content

`Verifier.treeSpecialSound` quantifies the extractor existentially over a bare function:

```lean
∃ E : Extractor.TreeBased StmtIn WitIn pSpec S.arity,
∀ stmtIn tree, tree.IsStructured S → tree.IsAccepting … →
  (stmtIn, E stmtIn tree) ∈ relIn
```
There is no computability or cost condition on `E`. With `[Inhabited WitIn]`, this is classically
equivalent to the extractor-free implication that every statement admitting a structured accepting
tree lies in `relIn.language`: `Classical.choice` manufactures the function. The `Inhabited`
assumption is needed only in the reverse direction, to define the function away from structured
accepting trees. The forward implication needs no such assumption.

This matters for the planned rewinding layer: that reduction must run one concrete extractor on the
tree it produces, so an existentially hidden function is not a usable interface. The
signature-preserving fix is to expose

```lean
def treeSpecialSoundWith … (E : Extractor.TreeBased …) : Prop := …
def treeSpecialSound … : Prop := ∃ E, treeSpecialSoundWith … E
```

and certify the old inline statement with `treeSpecialSound_iff : … := Iff.rfl`.

There is already an upstream consumer pointing in this direction. PR
[#602](https://github.com/Verified-zkEVM/ArkLib/pull/602) added
[`treeSpecialSound_of_isEmpty_challengeIdx`](https://github.com/Verified-zkEVM/ArkLib/blob/fad5cbf808774838924dc8273715724c6a6caa1f/ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/NoChallenge.lean#L104-L114):
it takes concrete extractor data `e`, builds the corresponding tree extractor, and immediately
closes the existential. The pinned predicate makes that concrete data available to downstream
consumers instead of hiding it again.

## 2. `distinctShape` admits arity zero

At `arity i = 0`, a challenge node has no children. Consequently:

- `IsStructured (distinctShape fun _ => 0)` is vacuous (`Function.Injective` on `Fin 0`);
- `IsAccepting` is vacuous for every verifier and statement because `fullTranscripts` is empty.

Therefore `specialSound` at arity zero requires an input witness for every statement and is
unsatisfiable for any relation whose language is not universal. The coordinate-wise notion already
rules this out with `CWSSStructure.soundnessParam : … → {k // 2 ≤ k}`.

The proposed guard uses the same subtype:

```lean
def distinctShape (k : pSpec.ChallengeIdx → {k : ℕ // 2 ≤ k}) : …
```

`1 ≤ k` would remove the empty-tree vacuity, but `2` is the smallest arity with special-soundness
extraction content and matches the existing CWSS convention. This is not a new downstream
assumption: the existing bridge theorem
[`toShape_ofSpecialSound_eq_distinctShape`](https://github.com/Verified-zkEVM/ArkLib/blob/fad5cbf808774838924dc8273715724c6a6caa1f/ArkLib/OracleReduction/Security/Implications.lean#L224-L243)
already takes `hk : ∀ i, 2 ≤ k i` at line 229. The fix moves that existing consumer hypothesis onto
the notion.

## Machine-checked probe

At `main` (`fad5cbf8`):

```text
$ lake env lean probes/TreeSpecialSoundProbes.lean
$ echo $?
0
```

On `fix/distinct-shape-arity-guard`, probe 1 elaborates before probe 2 and the first arity-zero use
is rejected:

```text
probes/TreeSpecialSoundProbes.lean:78:55: error(lean.synthInstanceFailed):
failed to synthesize instance of type class
  OfNat { k // 2 ≤ k } 0
```

On the independent `fix/tree-special-sound-pinned` branch, the complete probe still exits zero:
that branch deliberately preserves the original arity API and only exposes the pinned extractor
form. The arity rejection belongs to the sibling guard branch.

The relevant probe declarations are:

```lean
theorem treeSpecialSound_iff_language [Inhabited WitIn] … :
    verifier.treeSpecialSound init impl S relIn relOut ↔
      ∀ stmtIn,
        (∃ tree, tree.IsStructured S ∧
          tree.IsAccepting init impl verifier stmtIn relOut.language) →
        stmtIn ∈ relIn.language := by
  classical
  unfold Verifier.treeSpecialSound
  constructor
  · rintro ⟨E, hE⟩ stmtIn ⟨tree, hStructured, hAccepting⟩
    exact (Set.mem_language_iff relIn stmtIn).mpr
      ⟨E stmtIn tree, hE stmtIn tree hStructured hAccepting⟩
  · intro h
    refine ⟨fun stmtIn tree =>
      if h' : tree.IsStructured S ∧
          tree.IsAccepting init impl verifier stmtIn relOut.language
      then ((Set.mem_language_iff relIn stmtIn).mp (h stmtIn ⟨tree, h'⟩)).choose
      else default,
      fun stmtIn tree hStructured hAccepting => ?_⟩
    have h' := And.intro hStructured hAccepting
    simp only [dif_pos h']
    exact ((Set.mem_language_iff relIn stmtIn).mp (h stmtIn ⟨tree, h'⟩)).choose_spec

def zeroArityTree : ChallengeTree oneChalSpec (fun _ => 0) 0 :=
  .chalNode 0 rfl Fin.elim0 Fin.elim0

theorem zeroArityTree_isStructured :
    zeroArityTree.IsStructured (distinctShape fun _ => 0) :=
  ⟨fun a => a.elim0, fun j => j.elim0⟩

theorem specialSound_zeroArity_forces_trivial_language …
    (h : verifier.specialSound init impl (fun _ => 0) relIn relOut) :
    ∀ stmtIn, stmtIn ∈ relIn.language := by
  obtain ⟨E, hE⟩ := h
  intro stmtIn
  exact (Set.mem_language_iff relIn stmtIn).mpr
    ⟨E stmtIn zeroArityTree,
      hE stmtIn zeroArityTree zeroArityTree_isStructured
        (zeroArityTree_isAccepting init impl verifier stmtIn relOut.language)⟩
```
