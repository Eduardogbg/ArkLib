/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Interaction.Oracle.Core

/-!
# Oracle Interaction Examples

Small clients of the oracle interaction layer. These examples are intentionally
minimal: they exercise the core `Interaction.Spec`/`OracleDecoration` idioms
used by downstream protocols without depending on a larger proof system.
-/

open OracleComp OracleSpec

namespace Interaction.Oracle.Examples

namespace SumcheckStyle

open Interaction.TwoParty

/-! ## Two appended oracle rounds in the style used by Sumcheck -/

/-- A toy oracle message with the same shape as an evaluation oracle: queries are
points, and responses are values. -/
abbrev RoundOracle : Type :=
  Bool → Nat

abbrev Challenge : Type :=
  Bool

/-- One round: prover sends an oracle message, verifier sends a public challenge. -/
abbrev roundSpec : Interaction.Spec :=
  .node RoundOracle fun _ =>
    .node Challenge fun _ =>
      .done

/-- Same sender-then-receiver role pattern as `Sumcheck.roundRoles`. -/
abbrev roundRoles : RoleDecoration roundSpec :=
  ⟨.sender, fun _ => ⟨.receiver, fun _ => ⟨⟩⟩⟩

/-- Same oracle-decoration pattern as `Sumcheck.roundOracleDecoration`: attach
an oracle interface to the sender's round message and skip receiver nodes. -/
abbrev roundOracleDecoration :
    Interaction.OracleDecoration roundSpec roundRoles :=
  ⟨inferInstanceAs (OracleInterface RoundOracle), fun _ => fun _ => ⟨⟩⟩

/-- The oracle spec that becomes available after the prover sends the round
oracle message. This is the `oiSpec` idiom used by Sumcheck's verifier step. -/
abbrev roundOracleSpec : OracleSpec Bool :=
  @OracleInterface.spec RoundOracle inferInstance

/-- A minimal verifier step: after the sender message, query that oracle and
return a receiver challenge plus an output. -/
noncomputable def verifierStep
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) :
    Interaction.OracleDecoration.OracleCounterpart oSpec OStmtIn
      (fun {ιₐ} (_ : OracleSpec ιₐ) => Nat)
      roundSpec roundRoles roundOracleDecoration accSpec :=
  fun _ =>
    let receiverStep :
        OracleComp (oSpec + [OStmtIn]ₒ + (accSpec + roundOracleSpec))
          ((_ : Challenge) × Nat) := do
      let valueAtFalse : Nat ← liftM <| roundOracleSpec.query false
      pure ⟨true, valueAtFalse⟩
    receiverStep

/-- Two rounds composed by the same `Spec.append` surface used in Sumcheck. -/
abbrev protocolSpec : Interaction.Spec :=
  roundSpec.append fun _ => roundSpec

abbrev protocolRoles : RoleDecoration protocolSpec :=
  Interaction.Spec.Decoration.append roundRoles (fun _ => roundRoles)

abbrev protocolOracleDecoration :
    Interaction.OracleDecoration protocolSpec protocolRoles :=
  Role.Refine.append roundOracleDecoration (fun _ => roundOracleDecoration)

abbrev roundTranscript (oracle : RoundOracle) (challenge : Challenge) :
    Interaction.Spec.Transcript roundSpec :=
  ⟨oracle, ⟨challenge, ⟨⟩⟩⟩

abbrev protocolTranscript (oracle1 : RoundOracle) (challenge1 : Challenge)
    (oracle2 : RoundOracle) (challenge2 : Challenge) :
    Interaction.Spec.Transcript protocolSpec :=
  Interaction.Spec.Transcript.append roundSpec (fun _ => roundSpec)
    (roundTranscript oracle1 challenge1)
    (roundTranscript oracle2 challenge2)

abbrev roundQuery (oracle : RoundOracle) (challenge query : Bool) :
    Interaction.OracleDecoration.QueryHandle
      roundSpec roundRoles roundOracleDecoration (roundTranscript oracle challenge) :=
  .inl query

/-- Embed a first-round query into the composed protocol. -/
abbrev firstRoundQuery (oracle1 : RoundOracle) (challenge1 : Challenge)
    (oracle2 : RoundOracle) (challenge2 : Challenge) (query : Bool) :
    Interaction.OracleDecoration.QueryHandle
      protocolSpec protocolRoles protocolOracleDecoration
      (protocolTranscript oracle1 challenge1 oracle2 challenge2) :=
  Interaction.OracleDecoration.QueryHandle.appendLeft
    roundSpec (fun _ => roundSpec)
    roundRoles (fun _ => roundRoles)
    roundOracleDecoration (fun _ => roundOracleDecoration)
    (roundTranscript oracle1 challenge1)
    (roundTranscript oracle2 challenge2)
    (roundQuery oracle1 challenge1 query)

/-- Embed a second-round query into the composed protocol. -/
abbrev secondRoundQuery (oracle1 : RoundOracle) (challenge1 : Challenge)
    (oracle2 : RoundOracle) (challenge2 : Challenge) (query : Bool) :
    Interaction.OracleDecoration.QueryHandle
      protocolSpec protocolRoles protocolOracleDecoration
      (protocolTranscript oracle1 challenge1 oracle2 challenge2) :=
  Interaction.OracleDecoration.QueryHandle.appendRight
    roundSpec (fun _ => roundSpec)
    roundRoles (fun _ => roundRoles)
    roundOracleDecoration (fun _ => roundOracleDecoration)
    (roundTranscript oracle1 challenge1)
    (roundTranscript oracle2 challenge2)
    (roundQuery oracle2 challenge2 query)

theorem answerQuery_firstRound (oracle1 : RoundOracle) (challenge1 : Challenge)
    (oracle2 : RoundOracle) (challenge2 : Challenge) (query : Bool) :
    Interaction.OracleDecoration.answerQuery
      protocolSpec protocolRoles protocolOracleDecoration
      (protocolTranscript oracle1 challenge1 oracle2 challenge2)
      (firstRoundQuery oracle1 challenge1 oracle2 challenge2 query) = oracle1 query :=
  rfl

theorem answerQuery_secondRound (oracle1 : RoundOracle) (challenge1 : Challenge)
    (oracle2 : RoundOracle) (challenge2 : Challenge) (query : Bool) :
    Interaction.OracleDecoration.answerQuery
      protocolSpec protocolRoles protocolOracleDecoration
      (protocolTranscript oracle1 challenge1 oracle2 challenge2)
      (secondRoundQuery oracle1 challenge1 oracle2 challenge2 query) = oracle2 query :=
  rfl

end SumcheckStyle

end Interaction.Oracle.Examples
