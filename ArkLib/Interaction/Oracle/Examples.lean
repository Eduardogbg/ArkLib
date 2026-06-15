/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Interaction.Oracle.Core

/-!
# Oracle Interaction Examples

Small clients of the oracle interaction layer. These examples are intentionally
minimal: they exercise the protocol shape, role decoration, oracle decoration,
public transcript projection, and query answering without depending on a larger
proof system.
-/

open OracleComp OracleSpec

namespace Interaction.Oracle.Examples

namespace TwoRound

/-! ## Two oracle rounds with public-transcript-dependent continuation -/

/-- The second-round challenge space depends on the first public challenge. -/
abbrev RoundTwoChallenge (firstChallenge : Bool) : Type :=
  Fin (if firstChallenge then 2 else 3)

/-- The second oracle is queried at a `Bool` point and returns a value in the
challenge-dependent finite space. -/
abbrev RoundTwoMessage (firstChallenge : Bool) : Type :=
  Bool → RoundTwoChallenge firstChallenge

/-- The first round: the prover sends one `Nat` as an oracle message, then the
verifier sends one public `Bool` challenge. -/
abbrev roundOneSpec : Spec :=
  .oracle Nat (.public Bool (fun _ => .done))

/-- The second round depends on the public transcript of the first round. The
oracle payload is a function so queries have nontrivial inputs. -/
abbrev roundTwoSpec : roundOneSpec.PublicTranscript → Spec
  | ⟨firstChallenge, ⟨⟩⟩ =>
      .oracle (RoundTwoMessage firstChallenge)
        (.public (RoundTwoChallenge firstChallenge) (fun _ => .done))

/-- The composed two-round protocol. -/
abbrev protocolSpec : Spec :=
  roundOneSpec.append roundTwoSpec

/-- Round one has a receiver public message. The oracle node is implicitly a
sender message. -/
abbrev roundOneRoles : roundOneSpec.RoleDeco :=
  ⟨.receiver, fun _ => ⟨⟩⟩

/-- Round two also has a receiver public message, with its type selected by the
first public challenge. -/
abbrev roundTwoRoles : (pt : roundOneSpec.PublicTranscript) → (roundTwoSpec pt).RoleDeco
  | ⟨_, ⟨⟩⟩ => ⟨.receiver, fun _ => ⟨⟩⟩

/-- Role decoration for the composed protocol. -/
abbrev roles : protocolSpec.RoleDeco :=
  Spec.RoleDeco.append roundOneSpec roundTwoSpec roundOneRoles roundTwoRoles

/-- The first oracle uses the default interface: a trivial query returns the
entire `Nat` payload. -/
abbrev roundOneOracleDeco : roundOneSpec.OracleDeco :=
  ⟨OracleInterface.instDefault, fun _ => ⟨⟩⟩

/-- The second oracle uses the function interface: a `Bool` query evaluates the
function payload at that point. -/
abbrev roundTwoOracleDeco :
    (pt : roundOneSpec.PublicTranscript) → (roundTwoSpec pt).OracleDeco
  | ⟨firstChallenge, ⟨⟩⟩ =>
      ⟨inferInstanceAs (OracleInterface (RoundTwoMessage firstChallenge)), fun _ => ⟨⟩⟩

/-- Oracle decoration for the composed protocol. -/
abbrev oracleDeco : protocolSpec.OracleDeco :=
  Spec.OracleDeco.append roundOneSpec roundTwoSpec roundOneOracleDeco roundTwoOracleDeco

/-- Full transcript of the first round. -/
abbrev roundOneTranscript (firstMessage : Nat) (firstChallenge : Bool) :
    Interaction.Spec.Transcript roundOneSpec.toInteractionSpec :=
  ⟨firstMessage, ⟨firstChallenge, ⟨⟩⟩⟩

/-- Public transcript of the first round. -/
abbrev roundOnePublicTranscript (firstChallenge : Bool) : roundOneSpec.PublicTranscript :=
  ⟨firstChallenge, ⟨⟩⟩

/-- Full transcript of the second round after the first public challenge has
selected the finite challenge space. -/
abbrev roundTwoTranscript (firstChallenge : Bool)
    (secondMessage : RoundTwoMessage firstChallenge)
    (secondChallenge : RoundTwoChallenge firstChallenge) :
    Interaction.Spec.Transcript
      (roundTwoSpec (roundOnePublicTranscript firstChallenge)).toInteractionSpec :=
  ⟨secondMessage, ⟨secondChallenge, ⟨⟩⟩⟩

/-- Public transcript of the second round. -/
abbrev roundTwoPublicTranscript (firstChallenge : Bool)
    (secondChallenge : RoundTwoChallenge firstChallenge) :
    (roundTwoSpec (roundOnePublicTranscript firstChallenge)).PublicTranscript :=
  ⟨secondChallenge, ⟨⟩⟩

/-- A full transcript of the composed protocol is assembled from the two phase
transcripts. -/
abbrev transcript (firstMessage : Nat) (firstChallenge : Bool)
    (secondMessage : RoundTwoMessage firstChallenge)
    (secondChallenge : RoundTwoChallenge firstChallenge) :
    Interaction.Spec.Transcript protocolSpec.toInteractionSpec :=
  Spec.transcriptAppend roundOneSpec roundTwoSpec
    (roundOneTranscript firstMessage firstChallenge)
    (roundTwoTranscript firstChallenge secondMessage secondChallenge)

/-- The public transcript contains both verifier messages and forgets both
oracle payloads. -/
abbrev publicTranscript (firstChallenge : Bool)
    (secondChallenge : RoundTwoChallenge firstChallenge) :
    protocolSpec.PublicTranscript :=
  Spec.PublicTranscript.append roundOneSpec roundTwoSpec
    (roundOnePublicTranscript firstChallenge)
    (roundTwoPublicTranscript firstChallenge secondChallenge)

/-- Projection from the full transcript keeps only the public messages from both
rounds. -/
theorem projectPublic_eq (firstMessage : Nat) (firstChallenge : Bool)
    (secondMessage : RoundTwoMessage firstChallenge)
    (secondChallenge : RoundTwoChallenge firstChallenge) :
    protocolSpec.projectPublic
      (transcript firstMessage firstChallenge secondMessage secondChallenge) =
        publicTranscript firstChallenge secondChallenge :=
  rfl

/-- Splitting the composed public transcript recovers the per-round public
transcripts. -/
theorem splitPublicTranscript_eq (firstChallenge : Bool)
    (secondChallenge : RoundTwoChallenge firstChallenge) :
    Spec.PublicTranscript.split roundOneSpec roundTwoSpec
      (publicTranscript firstChallenge secondChallenge) =
        ⟨roundOnePublicTranscript firstChallenge,
          roundTwoPublicTranscript firstChallenge secondChallenge⟩ :=
  rfl

/-- Query handle for the first-round oracle before it is embedded into the
composed protocol. -/
abbrev roundOneMessageQuery (firstChallenge : Bool) :
    roundOneSpec.QueryHandle roundOneOracleDeco (roundOnePublicTranscript firstChallenge) :=
  .inl ()

/-- Query handle for the second-round function oracle before it is embedded into
the composed protocol. -/
abbrev roundTwoMessageQuery (firstChallenge : Bool)
    (secondChallenge : RoundTwoChallenge firstChallenge) (query : Bool) :
    (roundTwoSpec (roundOnePublicTranscript firstChallenge)).QueryHandle
      (roundTwoOracleDeco (roundOnePublicTranscript firstChallenge))
      (roundTwoPublicTranscript firstChallenge secondChallenge) :=
  .inl query

/-- The first-round query handle embedded into the composed protocol. -/
abbrev firstRoundQuery (firstChallenge : Bool)
    (secondChallenge : RoundTwoChallenge firstChallenge) :
    protocolSpec.QueryHandle oracleDeco (publicTranscript firstChallenge secondChallenge) :=
  Spec.QueryHandle.appendLeft roundOneSpec roundTwoSpec roundOneOracleDeco roundTwoOracleDeco
    (roundOnePublicTranscript firstChallenge)
    (roundTwoPublicTranscript firstChallenge secondChallenge)
    (roundOneMessageQuery firstChallenge)

/-- The second-round query handle embedded into the composed protocol. -/
abbrev secondRoundQuery (firstChallenge : Bool)
    (secondChallenge : RoundTwoChallenge firstChallenge) (query : Bool) :
    protocolSpec.QueryHandle oracleDeco (publicTranscript firstChallenge secondChallenge) :=
  Spec.QueryHandle.appendRight roundOneSpec roundTwoSpec roundOneOracleDeco roundTwoOracleDeco
    (roundOnePublicTranscript firstChallenge)
    (roundTwoPublicTranscript firstChallenge secondChallenge)
    (roundTwoMessageQuery firstChallenge secondChallenge query)

/-- Querying the first-round oracle through the composed handle returns the
first oracle payload. -/
theorem answerQuery_firstRound (firstMessage : Nat) (firstChallenge : Bool)
    (secondMessage : RoundTwoMessage firstChallenge)
    (secondChallenge : RoundTwoChallenge firstChallenge) :
    protocolSpec.answerQuery oracleDeco
      (transcript firstMessage firstChallenge secondMessage secondChallenge)
      (firstRoundQuery firstChallenge secondChallenge) = firstMessage :=
  rfl

/-- Querying the second-round oracle through the composed handle evaluates the
function payload at the requested point. -/
theorem answerQuery_secondRound (firstMessage : Nat) (firstChallenge : Bool)
    (secondMessage : RoundTwoMessage firstChallenge)
    (secondChallenge : RoundTwoChallenge firstChallenge) (query : Bool) :
    protocolSpec.answerQuery oracleDeco
      (transcript firstMessage firstChallenge secondMessage secondChallenge)
      (secondRoundQuery firstChallenge secondChallenge query) = secondMessage query :=
  rfl

/-- The first-round query has a `Nat` response. -/
example (firstChallenge : Bool) (secondChallenge : RoundTwoChallenge firstChallenge) :
    protocolSpec.toOracleSpec oracleDeco (publicTranscript firstChallenge secondChallenge)
      (firstRoundQuery firstChallenge secondChallenge) = Nat :=
  rfl

/-- The second-round query response type depends on the first public challenge. -/
example (firstChallenge : Bool) (secondChallenge : RoundTwoChallenge firstChallenge)
    (query : Bool) :
    protocolSpec.toOracleSpec oracleDeco (publicTranscript firstChallenge secondChallenge)
      (secondRoundQuery firstChallenge secondChallenge query) =
        RoundTwoChallenge firstChallenge :=
  rfl

end TwoRound

end Interaction.Oracle.Examples
