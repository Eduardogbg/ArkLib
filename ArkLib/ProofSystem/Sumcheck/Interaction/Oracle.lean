/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Defs
import ArkLib.Interaction.Oracle.Core

/-!
# Interaction-Native Sum-Check: Native Oracle Round Primitives

This module rebuilds the one-round sum-check oracle surface on the native
`Interaction.Oracle.Spec` API.

The round polynomial is a native `.oracle` node, so it is omitted from the
verifier's `PublicTranscript` and is accessed only through
`Oracle.Spec.QueryHandle`. The verifier's challenge is a `.public` receiver
node.
-/

namespace Sumcheck

open Interaction CompPoly CPoly OracleComp OracleSpec

namespace NativeOracle

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R]
variable (deg : ℕ)

/-- Native oracle-spec shape for one round: the prover provides the round
polynomial as an oracle message, then the verifier samples a public challenge. -/
def roundSpec : Interaction.Oracle.Spec :=
  .oracle (CDegreeLE R deg) <|
    .public R fun _ =>
      .done

/-- Native role decoration for one sum-check round. The oracle polynomial node
is implicitly prover-owned; the only public node is the verifier challenge. -/
def roundRoles : Interaction.Oracle.Spec.RoleDeco (roundSpec R deg) :=
  ⟨.receiver, fun _ => ⟨⟩⟩

/-- Native oracle decoration for one round: the prover's univariate round
polynomial is queryable via its evaluation oracle interface. -/
def roundOracleDeco : Interaction.Oracle.Spec.OracleDeco (roundSpec R deg) :=
  ⟨instOracleInterfaceCDegreeLE, fun _ => ⟨⟩⟩

/-- Forgetting the native oracle round recovers the legacy interaction shape. -/
@[simp]
theorem roundSpec_toInteractionSpec :
    (roundSpec R deg).toInteractionSpec = Sumcheck.roundSpec R deg :=
  rfl

/-- Forgetting native oracle roles recovers the legacy role decoration. -/
@[simp]
theorem roundRoles_toSpecRoles :
    (roundSpec R deg).toSpecRoles (roundRoles R deg) = Sumcheck.roundRoles R deg :=
  rfl

/-- Public transcript of a native oracle round. It contains the verifier
challenge but not the prover's oracle polynomial message. -/
abbrev RoundPublicTranscript :=
  Interaction.Oracle.Spec.PublicTranscript (roundSpec R deg)

/-- Extract the verifier challenge from a native oracle round public transcript. -/
abbrev roundChallenge (pt : RoundPublicTranscript R deg) : R :=
  pt.1

/-- The verifier counterpart type for one native oracle sum-check round. -/
abbrev RoundCounterpart
    {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    (Output : Interaction.Spec.Transcript (roundSpec R deg).toInteractionSpec → Type) :=
  Interaction.Spec.Counterpart.withMonads
    (roundSpec R deg).toInteractionSpec
    ((roundSpec R deg).toSpecRoles (roundRoles R deg))
    ((roundSpec R deg).toMonadDecoration oSpec OStmtIn
      (roundRoles R deg) (roundOracleDeco R deg) accSpec)
    Output

/-- The live-claim oracle verifier for one native sum-check round.

The verifier observes only the oracle handle for the prover's round polynomial,
queries it on the domain, checks the sum against the current target, samples a
challenge, and returns the next claim on success. -/
noncomputable def verifierStep
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    {m_dom : ℕ} (D : Fin m_dom → R) (target : RoundClaim R)
    (sampleChallenge : OracleComp oSpec R) :
    RoundCounterpart R deg oSpec OStmtIn accSpec (fun _ => Option (RoundClaim R)) :=
  let oiSpec := @OracleInterface.spec (CDegreeLE R deg) instOracleInterfaceCDegreeLE
  fun _ =>
    let receiverStep :
        OracleComp (oSpec + [OStmtIn]ₒ + (accSpec + oiSpec))
          ((_ : R) × Option (RoundClaim R)) := do
        let total ← (Finset.univ : Finset (Fin m_dom)).toList.foldlM
          (fun (acc : R) (j : Fin m_dom) => do
            let val : R ← liftM <| oiSpec.query (D j)
            pure (acc + val))
          (0 : R)
        let chal : R ← liftM sampleChallenge
        if total == target then do
          let polyAtChal : R ← liftM <| oiSpec.query chal
          pure ⟨chal, some polyAtChal⟩
        else
          pure ⟨chal, none⟩
    receiverStep

/-- The chained verifier step for one native sum-check round.

Once a previous round has rejected, later rounds keep the same interaction shape
but preserve the rejecting `none` state. -/
noncomputable def verifierStepOption
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    {m_dom : ℕ} (D : Fin m_dom → R) (target : Option (RoundClaim R))
    (sampleChallenge : OracleComp oSpec R) :
    RoundCounterpart R deg oSpec OStmtIn accSpec (fun _ => Option (RoundClaim R)) :=
  match target with
  | none =>
      fun _ =>
        let receiverStep :
            OracleComp
              (oSpec + [OStmtIn]ₒ +
                (accSpec + @OracleInterface.spec (CDegreeLE R deg)
                  instOracleInterfaceCDegreeLE))
              ((_ : R) × Option (RoundClaim R)) := do
            let chal : R ← liftM sampleChallenge
            pure ⟨chal, none⟩
        receiverStep
  | some target =>
      verifierStep (R := R) (deg := deg) OStmtIn accSpec D target sampleChallenge

end

end NativeOracle

end Sumcheck
