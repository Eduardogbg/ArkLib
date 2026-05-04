/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound
import ArkLib.Interaction.Oracle.Chain

/-!
# Interaction-Native Sum-Check: Native Multi-Round Surface

This module builds the native `n`-round sum-check oracle reduction as a
state-machine fold over the native oracle chain. The prover's private state is
the residual polynomial witness; its type shrinks from `PolyStmt ... (n + 1)`
to `PolyStmt ... n` at each round.
-/

namespace Sumcheck

open Interaction CompPoly OracleComp OracleSpec

namespace NativeOracle

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] (deg : ℕ)

/-- The native `n`-round sum-check oracle chain.

Each level is the existing one-round native oracle spec. The continuation is
constant because the next round shape does not depend on the public challenge;
participant state is handled by the parties, not by the protocol shape. -/
def fullChain : (n : Nat) → Interaction.Oracle.Spec.Chain n :=
  Interaction.Oracle.Spec.Chain.replicate
    (roundSpec R deg) (roundRoles R deg) (roundOracleDeco R deg)

/-- Native `n`-round sum-check oracle spec, flattened from `fullChain`. -/
abbrev fullSpec (n : Nat) : Interaction.Oracle.Spec :=
  Interaction.Oracle.Spec.Chain.toSpec n (fullChain R deg n)

/-- Native role decoration for `fullSpec`. -/
abbrev fullRoles (n : Nat) : Interaction.Oracle.Spec.RoleDeco (fullSpec R deg n) :=
  Interaction.Oracle.Spec.Chain.toRoles n (fullChain R deg n)

/-- Native oracle decoration for `fullSpec`. -/
abbrev fullOracleDeco (n : Nat) :
    Interaction.Oracle.Spec.OracleDeco (fullSpec R deg n) :=
  Interaction.Oracle.Spec.Chain.toOracleDeco n (fullChain R deg n)

end

section

variable {R : Type} [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] {deg : ℕ}

/-- Honest prover state for the native chain fold. The current claim mirrors
the verifier state so the honest prover can emit the terminal statement, while
the residual polynomial is the typed private witness that shrinks each round. -/
private structure ProverState {ιₛᵢ : Type} (OStatementIn : ιₛᵢ → Type)
    (k : Nat) where
  claim : Option (RoundClaim R)
  oracleStmt : OracleStatement OStatementIn
  residual : Sumcheck.PolyStmt R deg k

/-- Prover round handlers for the concrete native sum-check chain. -/
private noncomputable def proverRoundSteps
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStatementIn : ιₛᵢ → Type)
    {m_dom : ℕ} (D : Fin m_dom → R) :
    (n : Nat) →
      Interaction.Oracle.Spec.Chain.Prover.RoundSteps (m := OracleComp oSpec)
        (fun {k} _ => ProverState (R := R) (deg := deg) OStatementIn k)
        n (fullChain R deg n)
  | 0 => PUnit.unit
  | n + 1 =>
      ⟨fun state => do
        let sentPoly := honestRoundPoly (R := R) (deg := deg) D state.residual
        pure <|
          roundProverStepStateful (m := OracleComp oSpec) (R := R) (deg := deg)
            D state.residual
            (fun chal =>
              { claim := state.claim.bind fun _ => some (CPolynomial.eval chal sentPoly.1)
                oracleStmt := state.oracleStmt
                residual := stepResidual (R := R) (deg := deg) chal state.residual }),
        fun _ => proverRoundSteps (oSpec := oSpec) OStatementIn D n⟩

/-- Verifier round handlers for the concrete native sum-check chain. -/
private noncomputable def verifierRoundSteps
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStatementIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStatementIn i)]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    (n : Nat) →
      Interaction.Oracle.Spec.Chain.Verifier.RoundSteps
        (oSpec := oSpec) (OStmtIn := OStatementIn)
        (fun {_k} _ => Option (RoundClaim R))
        n (fullChain R deg n)
  | 0 => PUnit.unit
  | n + 1 =>
      ⟨fun claim =>
        verifierStepOption (R := R) (deg := deg) OStatementIn []ₒ D claim sampleChallenge,
        fun _ => verifierRoundSteps (oSpec := oSpec) OStatementIn D sampleChallenge n⟩

/-- Extract the terminal honest-prover state selected by the public transcript. -/
private def proverOutputState
    {ιₛᵢ : Type} {OStatementIn : ιₛᵢ → Type} :
    (n : Nat) →
      (pt : Interaction.Oracle.Spec.PublicTranscript (fullSpec R deg n)) →
      Interaction.Oracle.Spec.Chain.outputFamily
        (fun {k} _ => ProverState (R := R) (deg := deg) OStatementIn k)
        n (fullChain R deg n) pt →
      ProverState (R := R) (deg := deg) OStatementIn 0
  | 0, _, state => state
  | n + 1, pt, state =>
      let split :=
        Interaction.Oracle.Spec.Chain.splitPublicTranscript
          n (fullChain R deg (n + 1)) pt
      proverOutputState n split.2 state

/-- Extract the terminal verifier state selected by the public transcript. -/
private def verifierOutputState :
    (n : Nat) →
      (pt : Interaction.Oracle.Spec.PublicTranscript (fullSpec R deg n)) →
      Interaction.Oracle.Spec.Chain.outputFamily
        (fun {_k} _ => Option (RoundClaim R))
        n (fullChain R deg n) pt →
      Option (RoundClaim R)
  | 0, _, state => state
  | n + 1, pt, state =>
      let split :=
        Interaction.Oracle.Spec.Chain.splitPublicTranscript
          n (fullChain R deg (n + 1)) pt
      verifierOutputState n split.2 state

/-- Native stateful `n`-round sum-check reduction, built by composing native
one-round oracle reductions.

The input statement is the initial claim. The input oracle statement is carried
unchanged through all rounds, while the private residual polynomial witness
shrinks from `n` variables to zero variables. The output statement is
`Option (RoundClaim R)`, with `none` representing verifier rejection. -/
noncomputable def reductionStateful
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStatementIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStatementIn i)]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) (n : Nat) :
    Interaction.Oracle.Reduction oSpec
      (RoundClaim R)
      (fun _ => fullSpec R deg n)
      (fun _ => fullRoles R deg n)
      (fun _ => fullOracleDeco R deg n)
      (fun _ => PUnit)
      (fun _ => OStatementIn)
      (fun _ => Sumcheck.PolyStmt R deg n)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => OStatementIn)
      (fun _ _ => Sumcheck.PolyStmt R deg 0) := by
  simpa [fullSpec, fullRoles, fullOracleDeco] using
    Interaction.Oracle.Reduction.ofChain
      (oSpec := oSpec)
      (SharedIn := RoundClaim R)
      (StatementIn := fun _ => PUnit)
      (WitnessIn := fun _ => Sumcheck.PolyStmt R deg n)
      (ιₛᵢ := fun _ : RoundClaim R => ιₛᵢ)
      (OStatementIn := fun _ => OStatementIn)
      (n := n)
      (c := fun _ => fullChain R deg n)
      (StatementOut := fun _ _ => Option (RoundClaim R))
      (ιₛₒ := fun _ _ => ιₛᵢ)
      (OStatementOut := fun _ _ => OStatementIn)
      (WitnessOut := fun _ _ => Sumcheck.PolyStmt R deg 0)
      (ProverState := fun _ {k} _ => ProverState (R := R) (deg := deg) OStatementIn k)
      (VerifierState := fun _ {_k} _ => Option (RoundClaim R))
      (fun shared sWithOracles witness =>
        { claim := some shared
          oracleStmt := sWithOracles.oracleStmt
          residual := witness })
      (fun shared _ => some shared)
      (fun _ => proverRoundSteps (R := R) (deg := deg) (oSpec := oSpec) OStatementIn D n)
      (fun _ =>
        verifierRoundSteps (R := R) (deg := deg) (oSpec := oSpec)
          OStatementIn D sampleChallenge n)
      (fun _ pt state => (proverOutputState (R := R) (deg := deg) n pt state).claim)
      (fun _ pt state => verifierOutputState (R := R) (deg := deg) n pt state)
      (fun _ pt state => (proverOutputState (R := R) (deg := deg) n pt state).oracleStmt)
      (fun _ pt state => (proverOutputState (R := R) (deg := deg) n pt state).residual)
      (fun _ _ q => liftM <| ([OStatementIn]ₒ).query q)

end

end NativeOracle

end Sumcheck
