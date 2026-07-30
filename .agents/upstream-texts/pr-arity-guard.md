Title: fix(security): guard distinct-shape arity

Body:

> Not done in this wave: no upstream PR was opened and no full-repository build was run. The
> previously combined fork change passed fork CI on 2026-07-15. This split branch was rebuilt from
> `main` at `fad5cbf808774838924dc8273715724c6a6caa1f`; targeted builds and the arity probe were rerun
> here. The first two cold targeted-build invocations reached the 7200-second cap while populating
> dependencies; the repeated command completed successfully. Sorry delta: `+0 / -0`.

## Degenerate satisfaction at the current signature

At arity zero, the challenge node has no children. The probe constructs such a tree and proves both
obligations without using the verifier:

```lean
def zeroArityTree : ChallengeTree oneChalSpec (fun _ => 0) 0 :=
  .chalNode 0 rfl Fin.elim0 Fin.elim0

theorem zeroArityTree_isStructured :
    zeroArityTree.IsStructured (distinctShape fun _ => 0) :=
  ⟨fun a => a.elim0, fun j => j.elim0⟩

theorem zeroArityTree_isAccepting … :
    zeroArityTree.IsAccepting init impl verifier stmtIn langOut := by
  intro tr htr
  simp [zeroArityTree, ChallengeTree.fullTranscripts, ChallengeTree.transcripts] at htr
```
Thus arity-zero `specialSound` forces every statement into the input language and is unsatisfiable
for non-universal languages.

## Minimal fix

Require the existing CWSS subtype at the three plain entry points:

```lean
def distinctShape (k : pSpec.ChallengeIdx → {k : ℕ // 2 ≤ k}) : …
def Verifier.specialSound (k : pSpec.ChallengeIdx → {k : ℕ // 2 ≤ k}) …
def OracleVerifier.specialSound (k : pSpec.ChallengeIdx → {k : ℕ // 2 ≤ k}) …
```

`ChallengeTree` and `ChallengeTreeShape` remain fully general. The bridge statements only package
their already-present hypothesis as `fun i => ⟨k i, hk i⟩`; their proofs are otherwise unchanged.
In particular,
[`Implications.lean:229`](https://github.com/Verified-zkEVM/ArkLib/blob/fad5cbf808774838924dc8273715724c6a6caa1f/ArkLib/OracleReduction/Security/Implications.lean#L224-L243)
already carries `hk : ∀ i, 2 ≤ k i` on
`toShape_ofSpecialSound_eq_distinctShape`. This fix moves an existing consumer hypothesis onto the
notion.

The subtype excludes both the empty arity and the one-transcript case, matches
`CWSSStructure.soundnessParam`, and leaves the `ℓ = 1` shape equality definitional after packaging
`hk`.

## Verification

The exact baseline probe exits zero at `main`; on this branch the arity-zero instantiation is
type-rejected:

```text
probes/TreeSpecialSoundProbes.lean:78:55: error(lean.synthInstanceFailed):
failed to synthesize instance of type class
  OfNat { k // 2 ≤ k } 0
```

Targeted build:

```text
$ lake build ArkLib.OracleReduction.Security.SpecialSoundness \
    ArkLib.OracleReduction.Security.Implications
⚠ [2969/2969] Built ArkLib.OracleReduction.Security.Implications (58s)
warning: ArkLib/OracleReduction/Security/Implications.lean:48:8: declaration uses `sorry`
…
warning: ArkLib/OracleReduction/Security/Implications.lean:179:8: declaration uses `sorry`
Build completed successfully (2969 jobs).
```

Those `Implications.lean` sorries predate this change. No touched declaration adds a sorry.

`#print axioms`:

```text
'distinctShape' does not depend on any axioms
'Verifier.specialSound' depends on axioms: [propext, Classical.choice, Quot.sound]
'OracleVerifier.specialSound' depends on axioms: [propext, Classical.choice, Quot.sound]
'toShape_ofSpecialSound_eq_distinctShape' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'OracleVerifier.coordinateWiseSpecialSound_ofSpecialSound_iff' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```
