/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ArkLib.OracleReduction.Security.Basic
import ArkLib.Interaction.Reduction

open Interaction.TwoParty

/-!
# Commitment Schemes with Oracle Openings

A commitment scheme, relative to an oracle `oSpec : OracleSpec ι`, and for a given function
`oracle : Data → Query → Response` transforming underlying data `Data` into an oracle `Query →
Response`, is a tuple of two operations:

- Commit, which is a function `commit : Data → Randomness → OracleComp oSpec Commitment`
- Open, which is (roughly) an interactive proof (relative to `oSpec`) for the following relation:
  - `StmtIn := (cm : Commitment) × (x : Query) × (y : Response)`
  - `WitIn := (d : Data) × (r : Randomness)`
  - `rel : StmtIn → WitIn → Prop := fun ⟨cm, x, y⟩ ⟨d, r⟩ => commit d r = cm ∧ oracle d x = y`

There is one inaccuracy about the relation above: `commit` is an oracle computation, and not a
deterministic function; hence the relation is not literally true as described. This is why
security definitions for commitment schemes have to be stated differently than those for IOPs.

## Frameworks

This file contains both the legacy (`ProtocolSpec`-based) and new (`Interaction`-based) versions
of the commitment scheme structures. The new `Interaction`-based versions are in the
`Commitment.Interaction` namespace and will eventually supersede the legacy versions.
-/

-- Note: remove this once we properly define the security definitions for commitment schemes
set_option linter.unusedVariables false

namespace Commitment

open OracleSpec OracleComp SubSpec

variable {ι : Type} (oSpec : OracleSpec ι) (Data Randomness Commitment : Type)

structure Commit where
  commit : Data → Randomness → OracleComp oSpec Commitment

variable [O : OracleInterface Data] {n : ℕ} (pSpec : ProtocolSpec n)

structure Opening where
  opening : Proof oSpec (Commitment × (q : O.Query) × O.Response q) (Data × Randomness) pSpec

structure Scheme extends
    Commit oSpec Data Randomness Commitment,
    Opening oSpec Data Randomness Commitment pSpec

section Security

noncomputable section

open scoped NNReal

variable [DecidableEq ι]
  {oSpec : OracleSpec ι} {Data : Type} [O : OracleInterface Data] {Randomness : Type}
  {Commitment : Type} [oSpec.Fintype] [oSpec.Inhabited]
  {n : ℕ} {pSpec : ProtocolSpec n}
  [[pSpec.Challenge]ₒ.Inhabited] [[pSpec.Challenge]ₒ.Fintype]

/-- A commitment scheme satisfies **correctness** with error `correctnessError` if for all
  `data : Data`, `randomness : Randomness`, and `query : O.Query`, the probability of accepting upon
  executing the commitment and opening procedures honestly is at least `1 - correctnessError`. -/
def correctness (scheme : Scheme oSpec Data Randomness Commitment pSpec)
    (correctnessError : ℝ≥0)
    : Prop :=
  ∀ data : Data,
  ∀ randomness : Randomness,
  ∀ query : O.Query,
    Pr[ fun x => x.2.1 | do
        let cm ← liftM (scheme.commit data randomness)
        let z ← scheme.opening.run
          (show Commitment × (q : O.Query) × O.Response q from ⟨cm, query, O.answer data query⟩)
          (show Data × Randomness from ⟨data, randomness⟩)
        return z.1] ≥ 1 - correctnessError

/-- A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
-/
def perfectCorrectness (scheme : Scheme oSpec Data Randomness Commitment pSpec) : Prop :=
  correctness scheme 0

/-- An adversary in the (evaluation) binding game returns a commitment `cm`, a query `q`, two
  purported responses `r₁, r₂` to the query, and an auxiliary private state (to be passed to the
  malicious prover in the opening procedure). -/
def BindingAdversary (oSpec : OracleSpec ι) (Data Commitment AuxState : Type)
    [O : OracleInterface Data] :=
  OracleComp oSpec (Commitment × (q : O.Query) × O.Response q × O.Response q × AuxState)

/-- A commitment scheme satisfies **(evaluation) binding** with error `bindingError` if for all
    adversaries that output a commitment `cm`, query `q`, two responses `resp₁, resp₂`, and
    auxiliary state `st`, and for all malicious provers in the opening procedure taking in `st`, the
    probability that:

  1. The responses are different (`resp₁ ≠ resp₂`);
  2. The verifier accepts both openings

  is at most `bindingError`.

  Informally, evaluation binding says that it's computationally infeasible to open a commitment to
  two different responses for the same query. -/
def binding (scheme : Scheme oSpec Data Randomness Commitment pSpec)
    (bindingError : ℝ≥0) : Prop :=
  ∀ AuxState : Type,
  ∀ adversary : BindingAdversary oSpec Data Commitment AuxState,
  ∀ prover : Prover oSpec (Commitment × (q : O.Query) × O.Response q) AuxState Bool Unit pSpec,
    False
    -- [ fun ⟨x, x', b₁, b₂⟩ => x ≠ x' ∧ b₁ ∧ b₂ | do
    --     let result ← liftM adversary
    --     let ⟨cm, query, resp₁, resp₂, st⟩ := result
    --     let proof : Proof pSpec oSpec (Commitment × O.Query × O.Response) AuxState :=
    --       ⟨prover, scheme.opening.verifier⟩
    --     let ⟨accept₁, _⟩ ← proof.run ⟨cm, query, resp₁⟩ st
    --     let ⟨accept₂, _⟩ ← proof.run ⟨cm, query, resp₂⟩ st
    --     return (resp₁, resp₂, accept₁, accept₂)] ≤ bindingError

/-- A **straightline extractor** for a commitment scheme takes in the commitment, the log of queries
    made during the commitment phase, and returns the underlying data for the commitment. -/
def StraightlineExtractor (oSpec : OracleSpec ι) (Data Commitment : Type) :=
  Commitment → QueryLog oSpec → Data

/-- An adversary in the extractability game is an oracle computation that returns a commitment, a
  query, a response value, and some auxiliary state (to be used in the opening procedure). -/
def ExtractabilityAdversary (oSpec : OracleSpec ι) (Data Commitment AuxState : Type)
    [O : OracleInterface Data] :=
  OracleComp oSpec (Commitment × (q : O.Query) × O.Response q × AuxState)

/-- A commitment scheme satisfies **extractability** with error `extractabilityError` if there
    exists a straightline extractor `E` such that for all adversaries that output a commitment `cm`,
    a query `q`, a response `r`, and some auxiliary state `st`, and for all malicious provers in the
    opening procedure that takes in `st`, the probability that:

  1. The verifier accepts in the opening procedure given `cm, q, r`
  2. The extracted data `d` is inconsistent with the claimed response (i.e., `O.answer d q ≠ r`)

  is at most `extractabilityError`.

  Informally, extractability says that if an adversary can convince the verifier to accept an
  opening, then the extractor must be able to recover some underlying data that is consistent with
  the evaluation query. -/
def extractability (scheme : Scheme oSpec Data Randomness Commitment pSpec)
    (extractabilityError : ℝ≥0) : Prop :=
  ∃ extractor : StraightlineExtractor oSpec Data Commitment,
  ∀ AuxState : Type,
  ∀ adversary : ExtractabilityAdversary oSpec Data Commitment AuxState,
  ∀ prover : Prover oSpec (Commitment × (q : O.Query) × O.Response q) AuxState Bool Unit pSpec,
    False
    -- [ fun ⟨b, d, q, r⟩ => b ∧ O.answer d q = r | do
    --     let result ← liftM (simulate loggingOracle ∅ adversary)
    --     let ⟨⟨cm, query, response, st⟩, queryLog⟩ := result
    --     let proof : Proof pSpec oSpec (Commitment × O.Query × O.Response) AuxState :=
    --       ⟨prover, scheme.opening.verifier⟩
    --     let ⟨accept, _⟩ ← proof.run ⟨cm, query, response⟩ st
    --     letI data := extractor cm queryLog
    --     return (accept, data, query, response)] ≤ extractabilityError

-- TODO: version where the query is chosen according to some public coin?

-- TODO: multi-instance versions?

/-- A commitment scheme satisfies **hiding** with error `hidingError` if ....

Note: have to put it as `hiding'` because `hiding` is already used somewhere else. -/
def hiding' (scheme : Scheme oSpec Data Randomness Commitment pSpec) : Prop := sorry


end

end Security

/-! ## Interaction-based commitment scheme

Modular commitment scheme built on the `Interaction` framework. The scheme
is decomposed into two independently reusable components:

- `Interaction.Commit`: the commitment phase (`Interaction.Reduction`).
- `Interaction.Opening`: the opening phase (`Interaction.Proof`).
- `Interaction.CommitmentScheme`: the product of `Commit` and `Opening`.

All structures abstract over the monad `m : Type → Type`, decoupling from
`OracleComp`. Instantiate with `m := OracleComp oSpec` to recover the concrete
oracle computation setting. -/

namespace Interaction

/-- The commitment phase of a commitment scheme, modeled as an
`Interaction.Reduction`. The prover starts with `Data`, the verifier with
no input. After interacting according to `spec`, the prover outputs
`CommType × WitnessType` while the verifier outputs `CommType`. -/
structure Commit (m : Type → Type)
    (Data : Type) (CommType : Type) (WitnessType : Type) where
  spec : Interaction.Spec.{0}
  roles : RoleDecoration spec
  reduction : Interaction.Reduction m Unit
    (fun _ => spec) (fun _ => roles)
    (fun _ => Unit) (fun _ => Data)
    (fun _ _ => CommType) (fun _ _ => WitnessType)

/-- The opening phase of a commitment scheme, modeled as an
`Interaction.Proof`. Given a commitment, query, and claimed response, the
prover (holding `WitnessType`) convinces the verifier to accept or reject. -/
structure Opening (m : Type → Type)
    (Data : Type) (CommType : Type) (WitnessType : Type)
    [oi : OracleInterface Data] where
  spec : Interaction.Spec.{0}
  roles : RoleDecoration spec
  proof : Interaction.Proof m Unit
    (fun _ => spec) (fun _ => roles)
    (fun _ => CommType × (q : oi.Query) × oi.Response q)
    (fun _ => WitnessType)
    (fun _ _ => Bool)

/-- A full commitment scheme: the product of a commitment phase and an
opening phase. Fix a `Commit` and vary the `Opening` to get different
schemes over the same commitment mechanism. -/
structure CommitmentScheme (m : Type → Type)
    (Data : Type) (CommType : Type) (WitnessType : Type)
    [oi : OracleInterface Data] where
  commit : Commit m Data CommType WitnessType
  opening : Opening m Data CommType WitnessType

namespace Commit

variable {m : Type → Type} {Data CommType WitnessType : Type}

/-- Build a `Commit` from a non-interactive commitment function. The
resulting protocol has a single sender round: the prover computes the
commitment, sends `CommType` to the verifier, and retains `WitnessType`. -/
def ofFunction [Monad m] (f : Data → m (CommType × WitnessType)) :
    Commit m Data CommType WitnessType where
  spec := .node CommType (fun _ => .done)
  roles := ⟨.sender, fun _ => ⟨⟩⟩
  reduction := {
    prover := fun () () data =>
      pure (do
        let ⟨cm, wit⟩ ← f data
        pure ⟨cm, (cm, wit)⟩)
    verifier := fun () () =>
      fun cm => pure cm
  }

end Commit

namespace Opening

variable {m : Type → Type} {Data CommType WitnessType : Type}

/-- Build an `Opening` from a reveal-and-check function. The resulting protocol
has a single sender round: the prover sends `WitnessType` to the verifier,
which checks it against the statement. -/
def ofRevealCheck [Monad m] [oi : OracleInterface Data]
    (check : CommType × (q : oi.Query) × oi.Response q → WitnessType → Bool) :
    Opening m Data CommType WitnessType where
  spec := .node WitnessType (fun _ => .done)
  roles := ⟨.sender, fun _ => ⟨⟩⟩
  proof := {
    prover := fun () stmt wit =>
      pure (pure ⟨wit, (check stmt wit, ⟨⟩)⟩)
    verifier := fun () stmt =>
      fun w => pure (check stmt w)
  }

end Opening

end Interaction

end Commitment

