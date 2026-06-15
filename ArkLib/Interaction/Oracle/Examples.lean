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

namespace OneOracle

/-! ## One oracle message followed by one public verifier message -/

/-- A toy protocol: the prover sends one `Nat` as an oracle message, then the
verifier sends one public `Bool`. -/
abbrev protocolSpec : Spec :=
  .oracle Nat (.public Bool (fun _ => .done))

/-- Only the public node needs a role; the oracle node is implicitly a prover
message. -/
abbrev roles : protocolSpec.RoleDeco :=
  ⟨.receiver, fun _ => ⟨⟩⟩

/-- The oracle message uses the default interface: one trivial query returns the
entire `Nat` message. -/
abbrev oracleDeco : protocolSpec.OracleDeco :=
  ⟨OracleInterface.instDefault, fun _ => ⟨⟩⟩

/-- A full transcript contains both the oracle payload and the public message. -/
abbrev transcript (message : Nat) (challenge : Bool) :
    Interaction.Spec.Transcript protocolSpec.toInteractionSpec :=
  ⟨message, ⟨challenge, ⟨⟩⟩⟩

/-- The public transcript intentionally forgets the oracle payload. -/
abbrev publicTranscript (challenge : Bool) : protocolSpec.PublicTranscript :=
  ⟨challenge, ⟨⟩⟩

/-- Projection from the full transcript keeps only public messages. -/
theorem projectPublic_eq (message : Nat) (challenge : Bool) :
    protocolSpec.projectPublic (transcript message challenge) = publicTranscript challenge :=
  rfl

/-- The query handle for the unique oracle message available along the public
transcript. -/
abbrev messageQuery (challenge : Bool) :
    protocolSpec.QueryHandle oracleDeco (publicTranscript challenge) :=
  .inl ()

/-- Querying the oracle message through the generated query handle returns the
payload from the full transcript. -/
theorem answerQuery_message (message : Nat) (challenge : Bool) :
    protocolSpec.answerQuery oracleDeco (transcript message challenge)
      (messageQuery challenge) = message :=
  rfl

/-- The induced oracle spec exposes a `Nat` response for the unique message
query. -/
example (challenge : Bool) :
    protocolSpec.toOracleSpec oracleDeco (publicTranscript challenge)
      (messageQuery challenge) = Nat :=
  rfl

end OneOracle

end Interaction.Oracle.Examples
