/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Gomes
-/
import ArkLib.Interaction.Reduction

/-!
# Transcript forests and tree special soundness

This file defines the *tree of transcripts* carrier for the `Interaction` model, together
with the (extractor-pinned) tree special-soundness notion. It is the interaction-native
counterpart of `ProtocolSpec.ChallengeTree` (`OracleReduction/Security/TranscriptTree`),
which plays the same role over the flat `ProtocolSpec n` API: the family of transcripts a
rewinding extractor produces, sharing prefixes along shared challenges, from which a
tree-based extractor recovers a witness.

Two carriers are provided:

- `TranscriptForest` is *flat*: every node sits over the same fixed `Context : Spec`, and
  a leaf records a full `Spec.Transcript Context` path.
- `TranscriptForestDesc` is *descending*: the spec is a per-depth family `Sp : ℕ → Spec`,
  a depth-`d + 1` node carries exactly one round's challenges and prover message, and its
  children are forests over the residual `Sp d`. This is the shape of the tree-finding
  algorithm of [ACK21, §3.2], whose fork descends one round at a time — and the shape a
  resume-from-prefix executor naturally emits, since peeling one round of the spec is
  exactly what prover-side resumption (`Security.Rewinding.proverResumeAt`) does.

Both carriers branch `k` ways at every internal node, carry the sibling challenges as a
function `Fin k → Chal` (required pairwise-distinct by `Distinct`), and carry the prover's
per-round message `NodeMsg` at the node. The message payload is what lets a forest be
inverted back to the interaction that produced it: a tree-based extractor needs the
prover's per-round messages, not just the challenges. Leaves store the realized residual
transcript together with the verifier's output along it, so acceptance can be read off the
forest without re-running the verifier.

## Main definitions

- `TranscriptForest` / `TranscriptForestDesc` — the flat and descending `k`-ary carriers.
- `Distinct` — the sibling challenges at every node are pairwise distinct.
- `AllAccept` — every leaf output satisfies a caller-supplied acceptance predicate.
- `TranscriptForestDesc.numLeaves` / `numLeaves_eq_pow` — a depth-`d` forest has exactly
  `k ^ d` leaves; this is the necessary transcript count `K = ∏ kᵢ` of [ACK21, Def. 9]
  at uniform arity.
- `TreeSpeciallySound` — tree special soundness with the extractor as a *parameter*: for
  every distinct, accepting forest, the extracted witness is in the input relation.

## Design notes

The acceptance argument of `TreeSpeciallySound` is a *forest-level* invariant, not a
per-leaf predicate recursed via `AllAccept`. For protocols whose verifier folds the
statement round by round (each node's instance is determined by its parent's via the round
challenge), a leaf-local predicate cannot thread the folded instance down the spine; a
forest-level invariant can. The per-leaf `AllAccept` convention still exists on the
carrier and is used, independently, by the probabilistic layer (`Security.Rewinding`).

The arity is a uniform `k` at every level; a per-round arity function (as in
`ProtocolSpec.ChallengeTree`) is a straightforward generalization.

## References

- [ACK21] Attema, Cramer, Kohl, *A Compressed Σ-Protocol Theory for Lattices*,
  ePrint 2021/307.
-/

universe u v w

namespace Interaction.Security

open Interaction Interaction.TwoParty

variable {m : Type u → Type u}

/-- A `k`-ary forest of transcript paths through a fixed protocol `Context : Spec`, with a
challenge attached to each child edge.

`Chal` is the per-node challenge type and `NodeMsg` the per-node prover-message payload;
`StmtOutLeaf` is the verifier output type carried at a leaf (typically the `StatementOut`
along the realized path).

- `leaf` carries the realized transcript path `tr : Spec.Transcript Context` and the
  verifier's output `out : StmtOutLeaf tr` along it.
- `node` has fixed arity `k`, attaches a challenge `chal : Fin k → Chal` to its edges
  (required pairwise-distinct by `Distinct`, below), carries the prover message
  `nodeMsg : NodeMsg` produced at that node, and a child subtree per challenge index. -/
inductive TranscriptForest (Context : Spec.{u}) (Chal : Type u) (NodeMsg : Type u)
    (StmtOutLeaf : Spec.Transcript Context → Type u) (k : ℕ) : ℕ → Type u
  | leaf (tr : Spec.Transcript Context) (out : StmtOutLeaf tr) :
      TranscriptForest Context Chal NodeMsg StmtOutLeaf k 0
  | node {depth : ℕ} (chal : Fin k → Chal) (nodeMsg : NodeMsg)
      (child : Fin k → TranscriptForest Context Chal NodeMsg StmtOutLeaf k depth) :
      TranscriptForest Context Chal NodeMsg StmtOutLeaf k (depth + 1)

namespace TranscriptForest

variable {Context : Spec.{u}} {Chal : Type u} {NodeMsg : Type u}
  {StmtOutLeaf : Spec.Transcript Context → Type u} {k : ℕ}

/-- The distinct-challenge condition: at every `node`, the `k` edge challenges are
pairwise distinct. This is the special-soundness side condition on the tree. -/
def Distinct : {depth : ℕ} → TranscriptForest Context Chal NodeMsg StmtOutLeaf k depth → Prop
  | 0, .leaf _ _ => True
  | _ + 1, .node chal _ child =>
      (∀ i j, i ≠ j → chal i ≠ chal j) ∧ ∀ i, (child i).Distinct

/-- All leaf paths of the forest end in an accepting verifier output, as judged by a
caller-supplied acceptance predicate on `(path, output)` pairs. -/
def AllAccept (accept : (tr : Spec.Transcript Context) → StmtOutLeaf tr → Prop) :
    {depth : ℕ} → TranscriptForest Context Chal NodeMsg StmtOutLeaf k depth → Prop
  | 0, .leaf tr out => accept tr out
  | _ + 1, .node _ _ child => ∀ i, (child i).AllAccept accept

end TranscriptForest

/-! ## The descending forest carrier

`TranscriptForest` is flat: every node carries the same fixed `Context : Spec`, and a leaf
records a full transcript path — faithful to a verifier that re-runs all rounds at every
node. The tree-finding algorithm of [ACK21, §3.2] instead descends one round per level:
a depth-`d + 1` node peels its own round and each child is a forest one round shorter,
over the residual spec. `TranscriptForestDesc` is that descending twin: `Context` becomes
a per-depth family `Sp : ℕ → Spec`, a node carries exactly one round's challenges and
prover message, and the recursion bottoms out at a leaf carrying the residual transcript
over `Sp 0`. -/
inductive TranscriptForestDesc (Sp : ℕ → Spec.{u}) (Chal : Type u) (NodeMsg : Type u)
    (StmtOutLeaf : (tr : Spec.Transcript (Sp 0)) → Type u) (k : ℕ) : ℕ → Type u
  | leaf (tr : Spec.Transcript (Sp 0)) (out : StmtOutLeaf tr) :
      TranscriptForestDesc Sp Chal NodeMsg StmtOutLeaf k 0
  | node {depth : ℕ} (chal : Fin k → Chal) (nodeMsg : NodeMsg)
      (child : Fin k → TranscriptForestDesc Sp Chal NodeMsg StmtOutLeaf k depth) :
      TranscriptForestDesc Sp Chal NodeMsg StmtOutLeaf k (depth + 1)

namespace TranscriptForestDesc

variable {Sp : ℕ → Spec.{u}} {Chal : Type u} {NodeMsg : Type u}
  {StmtOutLeaf : (tr : Spec.Transcript (Sp 0)) → Type u} {k : ℕ}

/-- The distinct-challenge condition for the descending forest: at every `node`, the `k`
edge challenges of that round are pairwise distinct. Mirrors `TranscriptForest.Distinct`. -/
def Distinct :
    {depth : ℕ} → TranscriptForestDesc Sp Chal NodeMsg StmtOutLeaf k depth → Prop
  | 0, .leaf _ _ => True
  | _ + 1, .node chal _ child =>
      (∀ i j, i ≠ j → chal i ≠ chal j) ∧ ∀ i, (child i).Distinct

/-- All leaf paths of the descending forest end in an accepting verifier output, as judged
by a caller-supplied acceptance predicate on the residual-`Sp 0` `(path, output)` pair.
Mirrors `TranscriptForest.AllAccept`. -/
def AllAccept (accept : (tr : Spec.Transcript (Sp 0)) → StmtOutLeaf tr → Prop) :
    {depth : ℕ} → TranscriptForestDesc Sp Chal NodeMsg StmtOutLeaf k depth → Prop
  | 0, .leaf tr out => accept tr out
  | _ + 1, .node _ _ child => ∀ i, (child i).AllAccept accept

open scoped BigOperators in
/-- The number of leaves (transcripts) of a descending forest: a `leaf` is one transcript,
a `node` sums over its `k` children. This is the transcript count `K = ∏ kᵢ` of
[ACK21, Def. 9] — a count of the assembled output object, distinct from the extractor's
draw cost (`ackPolyBound`, in `Security.TreeExtraction`). -/
def numLeaves :
    {depth : ℕ} → TranscriptForestDesc Sp Chal NodeMsg StmtOutLeaf k depth → ℕ
  | 0, .leaf _ _ => 1
  | _ + 1, .node _ _ child => ∑ i, (child i).numLeaves

open scoped BigOperators in
/-- Every descending forest of type-index `depth` has exactly `k ^ depth` leaves. The
count is forced by the carrier type — each `node` has exactly `k` children and `depth` is
a type index — so this is an unconditional structural induction, independent of the
challenges and messages carried. -/
theorem numLeaves_eq_pow {depth : ℕ}
    (f : TranscriptForestDesc Sp Chal NodeMsg StmtOutLeaf k depth) :
    f.numLeaves = k ^ depth := by
  induction f with
  | leaf tr out => rfl
  | node chal nodeMsg child ih =>
    simp only [numLeaves, ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    rw [pow_succ, mul_comm]

end TranscriptForestDesc

/-! ## The special-soundness property

A verifier is *tree-specially sound* with extractor `extract` if, for every forest of
accepting transcripts with pairwise-distinct sibling challenges, `extract` returns a
witness in the input relation.

The extractor is a parameter of the notion rather than an existential: an existential over
bare functions carries no algorithmic content (it collapses classically to the implication
"every statement admitting an accepting distinct forest is in the language"), and the
rewinding reduction that consumes this notion must run one concrete extractor on the
forests it produces. -/
section SpeciallySound

variable [Monad m]
  {SharedIn : Type v} {Context : SharedIn → Spec.{u}}
  {Roles : (i : SharedIn) → RoleDecoration (Context i)}
  {StmtIn WitIn : SharedIn → Type u}
  {StmtOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
  {Chal NodeMsg : Type u}

/-- Tree special soundness with a fixed arity `k` and depth (number of receiver rounds)
`depth`: for every input `i`, statement `stmt`, and forest with pairwise-distinct sibling
challenges satisfying the acceptance invariant, the extracted witness is in `relIn`.

`accept i stmt` is a forest-level acceptance invariant on the whole forest, not a per-leaf
predicate: for verifiers that fold the statement round by round, each node's instance is
pinned to its parent's via the round challenge, which a leaf-local predicate cannot
express (see the module docstring). The verifier here is the ordinary `Verifier`; a
`PublicCoinVerifier` forgets to it via `toVerifier`. -/
def TreeSpeciallySound
    (_verifier : Verifier m SharedIn Context Roles StmtIn StmtOut)
    (k depth : ℕ)
    (accept : (i : SharedIn) → StmtIn i →
      TranscriptForest (Context i) Chal NodeMsg (StmtOut i) k depth → Prop)
    (relIn : (i : SharedIn) → StmtIn i → WitIn i → Prop)
    (extract : (i : SharedIn) →
      TranscriptForest (Context i) Chal NodeMsg (StmtOut i) k depth → WitIn i) : Prop :=
  ∀ (i : SharedIn) (stmt : StmtIn i)
    (forest : TranscriptForest (Context i) Chal NodeMsg (StmtOut i) k depth),
    forest.Distinct → accept i stmt forest →
      relIn i stmt (extract i forest)

end SpeciallySound

end Interaction.Security
