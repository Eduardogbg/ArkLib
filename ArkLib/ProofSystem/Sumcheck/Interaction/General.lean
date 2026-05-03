/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound
import ArkLib.Interaction.Oracle.Composition

/-!
# Interaction-Native Sum-Check: Native Multi-Round Surface

This module tests the lightweight state story for native `Interaction.Oracle.Spec`.
Rather than adding a foundational state-chain object, the multi-round prover and
verifier carry their state in the ordinary continuation structure of their
strategies/counterparts.

For sum-check:

* the prover continuation closes over the private residual polynomial;
* the verifier continuation closes over the live optional claim;
* the protocol spec itself is just a recursive append of the native one-round
  oracle spec.
-/

namespace Sumcheck

open Interaction CompPoly OracleComp OracleSpec

namespace NativeOracle

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] (deg : ℕ)

/-- Native `n`-round sum-check oracle spec.

Each round contributes one oracle polynomial node and one public verifier
challenge. No protocol state is stored in the spec: state is carried by the
participant continuations. -/
def fullSpec : Nat → Interaction.Oracle.Spec
  | 0 => .done
  | n + 1 => (roundSpec R deg).append fun _ => fullSpec n

/-- Native role decoration for the `n`-round sum-check oracle spec. -/
def fullRoles : (n : Nat) → Interaction.Oracle.Spec.RoleDeco (fullSpec R deg n)
  | 0 => ⟨⟩
  | n + 1 =>
      Interaction.Oracle.Spec.RoleDeco.append
        (roundSpec R deg) (fun _ => fullSpec R deg n)
        (roundRoles R deg) (fun _ => fullRoles n)

/-- Native oracle decoration for the `n`-round sum-check oracle spec. -/
def fullOracleDeco : (n : Nat) → Interaction.Oracle.Spec.OracleDeco (fullSpec R deg n)
  | 0 => ⟨⟩
  | n + 1 =>
      Interaction.Oracle.Spec.OracleDeco.append
        (roundSpec R deg) (fun _ => fullSpec R deg n)
        (roundOracleDeco R deg) (fun _ => fullOracleDeco n)

end

section

variable {R : Type} [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] {deg : ℕ}

/-- Honest multi-round prover strategy whose private state is the residual
polynomial captured by recursive continuations.

This is the clean monadic-state example: after each verifier challenge, the
continuation receives the next residual polynomial and recurses. No separate
state-chain spec is needed. -/
noncomputable def proverStrategy
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R) :
    (n : Nat) →
    Sumcheck.PolyStmt R deg n →
    OracleComp oSpec
      (Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
        (fullSpec R deg n).toInteractionSpec
        ((fullSpec R deg n).toSpecRoles (fullRoles R deg n))
        (fun _ => Sumcheck.PolyStmt R deg 0))
  | 0, residual => by
      simpa [fullSpec, fullRoles] using (pure residual)
  | n + 1, residual => by
      let roundStrat :=
        roundProverStepStateful (m := OracleComp oSpec) (R := R) (deg := deg)
          D residual
          (fun chal => stepResidual (R := R) (deg := deg) chal residual)
      simpa [fullSpec, fullRoles] using
        Interaction.Oracle.Prover.compAux
          (roundSpec R deg) (fun _ => fullSpec R deg n)
          (roundRoles R deg) (fun _ => fullRoles R deg n)
          (OutType := fun _ _ => Sumcheck.PolyStmt R deg 0)
          roundStrat
          (fun _tr₁ nextResidual => proverStrategy D n nextResidual)

/-- Multi-round verifier counterpart whose public state is the live optional
claim captured by recursive continuations.

The accumulated oracle spec is still handled by the native oracle monad
decoration; the protocol state itself is an ordinary recursive parameter. -/
noncomputable def verifierCounterpartOption
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    (n : Nat) →
    Option (RoundClaim R) →
    Interaction.Spec.Counterpart.withMonads
      (fullSpec R deg n).toInteractionSpec
      ((fullSpec R deg n).toSpecRoles (fullRoles R deg n))
      ((fullSpec R deg n).toMonadDecoration oSpec OStmtIn
        (fullRoles R deg n) (fullOracleDeco R deg n) accSpec)
      (fun _ => Option (RoundClaim R))
  | 0, target => by
      simpa [fullSpec, fullRoles, fullOracleDeco] using target
  | n + 1, target => by
      let roundVerifier :=
        verifierStepOption (R := R) (deg := deg)
          OStmtIn accSpec D target sampleChallenge
      simpa [fullSpec, fullRoles, fullOracleDeco] using
        Interaction.Oracle.Verifier.compAux
          (roundSpec R deg) (fun _ => fullSpec R deg n)
          (roundRoles R deg) (fun _ => fullRoles R deg n)
          (roundOracleDeco R deg) (fun _ => fullOracleDeco R deg n)
          accSpec
          (OutType := fun _ _ => Option (RoundClaim R))
          roundVerifier
          (fun accSpec' _tr₁ nextTarget =>
            verifierCounterpartOption OStmtIn accSpec' D sampleChallenge n nextTarget)

/-- Top-level multi-round verifier counterpart starting from a live claim. -/
noncomputable def verifierCounterpart
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R)
    (n : Nat) (target : RoundClaim R) :
    Interaction.Spec.Counterpart.withMonads
      (fullSpec R deg n).toInteractionSpec
      ((fullSpec R deg n).toSpecRoles (fullRoles R deg n))
      ((fullSpec R deg n).toMonadDecoration oSpec OStmtIn
        (fullRoles R deg n) (fullOracleDeco R deg n) accSpec)
      (fun _ => Option (RoundClaim R)) :=
  verifierCounterpartOption (R := R) (deg := deg)
    OStmtIn accSpec D sampleChallenge n (some target)

end

end NativeOracle

end Sumcheck
