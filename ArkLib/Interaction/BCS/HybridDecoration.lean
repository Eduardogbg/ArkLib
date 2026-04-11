/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Core

/-!
# Hybrid Decoration, Sender Independence, and Query Handles

This module introduces the infrastructure for the "partial" BCS transformation,
where only a subset of prover messages are oracle-queryable (and hence committed).
The remaining messages are plain metadata (trace length, layout info, sumcheck
binding order, etc.) that may legitimately shape the protocol tree.

## Main definitions

- `HybridDecoration` — assigns an *optional* `OracleInterface` at each sender
  node. Defined as `Role.Refine (fun X => Option (OracleInterface X))`.
  Plain senders (`none`) pass through unchanged in BCS. Oracle senders
  (`some oi`) will be committed.

- `HybridDecoration.OracleSenderIndependent` — well-formedness predicate for
  BCS: at oracle sender nodes, the continuation must not depend on the specific
  message value. At plain sender nodes, dependency is allowed.

- `HybridDecoration.QueryHandle` — index type for oracle queries given a
  transcript path. Only oracle sender nodes contribute query indices; plain
  sender nodes are transparent.

- `HybridDecoration.toOracleSpec` — the `OracleSpec` for querying oracle-sender
  messages along a given transcript path.

- `HybridDecoration.answerQuery` — answer oracle queries using message values
  from a transcript.

## Design rationale

The existing `OracleDecoration` (`Role.Refine OracleInterface`) requires every
sender node to carry an `OracleInterface`. This works for pure IOPs/IORs but
fails for real protocols where some prover messages are metadata. The
`HybridDecoration` generalizes this by making the oracle interface optional,
aligning with the `OracleInterfaces` TODO in `ProtocolSpec/Basic.lean` and the
functional BCS literature (eprint 2025/902).

## See also

- `Oracle/Core.lean` — the full `OracleDecoration` and its infrastructure
- `BCS/SpecTransform.lean` — the BCS spec transformation using this decoration
-/

universe u v

open OracleComp OracleSpec

namespace Interaction

/-- A hybrid decoration assigns an *optional* `OracleInterface` at each sender
node. `none` means plain metadata (sent in the clear, may shape the tree).
`some oi` means oracle message (queryable, will be committed by BCS).

Defined as `Role.Refine (fun X => Option (OracleInterface X))`. -/
abbrev HybridDecoration (spec : Spec) (roles : RoleDecoration spec) :=
  Interaction.Role.Refine (fun X => Option (OracleInterface X)) spec roles

namespace HybridDecoration

/-! ## Sender independence -/

/-- At an oracle sender node, the continuation must not depend on the specific
oracle message value (since BCS will hide it behind a commitment). At plain
sender nodes, dependency is allowed and expected. At receiver nodes, no
constraint is imposed beyond recursive well-formedness.

This is the minimal well-formedness condition for BCS. -/
def OracleSenderIndependent :
    (spec : Spec) → (roles : RoleDecoration spec) →
    HybridDecoration spec roles → Prop
  | .done, _, _ => True
  | .node X rest, ⟨.sender, rRest⟩, ⟨oi?, hdRest⟩ =>
      (oi?.isSome → ∀ x₁ x₂ : X, rest x₁ = rest x₂) ∧
      (∀ x, OracleSenderIndependent (rest x) (rRest x) (hdRest x))
  | .node _ rest, ⟨.receiver, rRest⟩, hdFn =>
      ∀ x, OracleSenderIndependent (rest x) (rRest x) (hdFn x)

/-! ## Query handles and oracle spec -/

/-- Index type for oracle queries given a transcript path through a hybrid
decoration. Only oracle sender nodes contribute query indices (via `.inl`);
plain sender nodes are skipped, and the query handle recurses into the
subtree determined by the transcript. Receiver nodes recurse immediately. -/
def QueryHandle :
    (spec : Spec) → (roles : RoleDecoration spec) →
    HybridDecoration spec roles → Spec.Transcript spec → Type
  | .done, _, _, _ => Empty
  | .node _ rest, ⟨.sender, rRest⟩, ⟨none, hdRest⟩, ⟨x, trRest⟩ =>
      QueryHandle (rest x) (rRest x) (hdRest x) trRest
  | .node _ rest, ⟨.sender, rRest⟩, ⟨some oi, hdRest⟩, ⟨x, trRest⟩ =>
      oi.Query ⊕ QueryHandle (rest x) (rRest x) (hdRest x) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, hdFn, ⟨x, trRest⟩ =>
      QueryHandle (rest x) (rRest x) (hdFn x) trRest

/-- The oracle specification for querying oracle-sender messages along a given
transcript path. Maps each `QueryHandle` to its response type. Plain sender
nodes do not contribute any queries. -/
def toOracleSpec :
    (spec : Spec) → (roles : RoleDecoration spec) →
    (hd : HybridDecoration spec roles) →
    (tr : Spec.Transcript spec) → OracleSpec (QueryHandle spec roles hd tr)
  | .done, _, _, _ => Empty.elim
  | .node _ rest, ⟨.sender, rRest⟩, ⟨none, hdRest⟩, ⟨x, trRest⟩ =>
      toOracleSpec (rest x) (rRest x) (hdRest x) trRest
  | .node _ rest, ⟨.sender, rRest⟩, ⟨some oi, hdRest⟩, ⟨x, trRest⟩ =>
    fun
    | .inl q => oi.toOC.spec q
    | .inr handle => toOracleSpec (rest x) (rRest x) (hdRest x) trRest handle
  | .node _ rest, ⟨.receiver, rRest⟩, hdFn, ⟨x, trRest⟩ =>
      toOracleSpec (rest x) (rRest x) (hdFn x) trRest

/-- Answer oracle queries using the message values from a transcript. At each
oracle sender node, the transcript provides the actual move `x : X`, which is
used as the message argument to `OracleInterface`'s implementation. Plain
sender nodes are skipped. -/
def answerQuery :
    (spec : Spec) → (roles : RoleDecoration spec) →
    (hd : HybridDecoration spec roles) →
    (tr : Spec.Transcript spec) →
    QueryImpl (toOracleSpec spec roles hd tr) Id
  | .done, _, _, _ => fun q => q.elim
  | .node _ rest, ⟨.sender, rRest⟩, ⟨none, hdRest⟩, ⟨x, trRest⟩ =>
      answerQuery (rest x) (rRest x) (hdRest x) trRest
  | .node _ rest, ⟨.sender, rRest⟩, ⟨some oi, hdRest⟩, ⟨x, trRest⟩ =>
    fun
    | .inl q => (oi.toOC.impl q).run x
    | .inr handle => answerQuery (rest x) (rRest x) (hdRest x) trRest handle
  | .node _ rest, ⟨.receiver, rRest⟩, hdFn, ⟨x, trRest⟩ =>
      answerQuery (rest x) (rRest x) (hdFn x) trRest

/-! ## Conversion from OracleDecoration -/

/-- Every `OracleDecoration` can be viewed as a `HybridDecoration` where all
sender nodes carry `some oi`. -/
def ofOracleDecoration :
    (spec : Spec) → (roles : RoleDecoration spec) →
    OracleDecoration spec roles → HybridDecoration spec roles
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩ =>
      ⟨some oi, fun x => ofOracleDecoration (rest x) (rRest x) (odRest x)⟩
  | .node _ rest, ⟨.receiver, rRest⟩, odFn =>
      fun x => ofOracleDecoration (rest x) (rRest x) (odFn x)

/-- A trivial hybrid decoration where no sender carries an oracle interface. -/
def plain :
    (spec : Spec) → (roles : RoleDecoration spec) →
    HybridDecoration spec roles
  | .done, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩ =>
      ⟨none, fun x => plain (rest x) (rRest x)⟩
  | .node _ rest, ⟨.receiver, rRest⟩ =>
      fun x => plain (rest x) (rRest x)

/-- The plain hybrid decoration is trivially oracle-sender-independent
(the condition is vacuously true at every sender node). -/
theorem plain_oracleSenderIndependent :
    (spec : Spec) → (roles : RoleDecoration spec) →
    OracleSenderIndependent spec roles (plain spec roles)
  | .done, _ => trivial
  | .node _ rest, ⟨.sender, rRest⟩ =>
      ⟨fun h => absurd h (by simp), fun x => plain_oracleSenderIndependent (rest x) (rRest x)⟩
  | .node _ rest, ⟨.receiver, rRest⟩ =>
      fun x => plain_oracleSenderIndependent (rest x) (rRest x)

/-! ## Node commitments and commitment decoration -/

/-- Per-oracle-sender commitment configuration. Bundles a commitment type,
randomness type, and commit function. Only meaningful at sender nodes
where `HybridDecoration` provides `some oi`. -/
structure NodeCommitment {ι : Type} (oSpec : OracleSpec.{0, 0} ι) (X : Type)
    [OracleInterface X] where
  CommType : Type
  RandType : Type
  commit : X → RandType → OracleComp oSpec CommType

/-- A commitment decoration threads `NodeCommitment` data through the tree,
carrying data only at oracle sender nodes. Plain sender nodes carry no
commitment data. -/
def CommitmentDecoration {ι : Type} (oSpec : OracleSpec.{0, 0} ι) :
    (spec : Spec.{0}) → (roles : RoleDecoration spec) →
    HybridDecoration spec roles → Type 1
  | .done, _, _ => PUnit
  | .node X rest, ⟨.sender, rRest⟩, ⟨none, hdRest⟩ =>
      (x : X) → CommitmentDecoration oSpec (rest x) (rRest x) (hdRest x)
  | .node X rest, ⟨.sender, rRest⟩, ⟨some oi, hdRest⟩ =>
      @NodeCommitment _ oSpec X oi ×
      ((x : X) → CommitmentDecoration oSpec (rest x) (rRest x) (hdRest x))
  | .node _ rest, ⟨.receiver, rRest⟩, hdFn =>
      (x : _) → CommitmentDecoration oSpec (rest x) (rRest x) (hdFn x)

end HybridDecoration

end Interaction
