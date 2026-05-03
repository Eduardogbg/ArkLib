/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.Oracle
import ArkLib.Interaction.Oracle.Execution

/-!
# Interaction-Native Sum-Check: Native Single Round

This module ports the single-round sum-check oracle reduction to the native
`Interaction.Oracle.Spec` layer.
-/

namespace Sumcheck

open Interaction CompPoly CPoly OracleComp OracleSpec

namespace NativeOracle

section

variable {R : Type} [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] {deg : ℕ}

/-- Advance a residual polynomial by fixing its first variable to the sampled
challenge. This is the stateful prover update for one sum-check round. -/
def stepResidual (chal : R)
    {numVars : ℕ} (poly : Sumcheck.PolyStmt R deg (numVars + 1)) :
    Sumcheck.PolyStmt R deg numVars :=
  ⟨CMvPolynomial.partialEvalFirst chal poly.1,
    CMvPolynomial.partialEvalFirst_individualDegreeLE chal poly.1 poly.2⟩

/-- The residual polynomial obtained by evaluating the first `prefixLen`
variables of the original polynomial at the sampled challenge prefix. -/
private def currentResidualGo :
    (prefixLen : Nat) →
    {n : Nat} →
    (h : prefixLen ≤ n) →
    (vals : Fin prefixLen → R) →
    (poly : Sumcheck.PolyStmt R deg n) →
    Sumcheck.PolyStmt R deg (n - prefixLen)
  | 0, _n, _, _, poly => by
      simpa using poly
  | prefixLen + 1, 0, h, _, _ => by
      exact False.elim (Nat.not_succ_le_zero _ h)
  | prefixLen + 1, n + 1, h, vals, poly => by
      simpa using
        currentResidualGo
          prefixLen
          (n := n)
          (Nat.le_of_succ_le_succ h)
          (fun i => vals i.succ)
          (stepResidual (R := R) (deg := deg) (vals 0) poly)
termination_by currentResidualGo prefixLen _ _ _ => prefixLen
decreasing_by simp_wf

/-- The residual polynomial obtained by evaluating the first `prefixLen`
variables of the original polynomial at the sampled challenge prefix. -/
def currentResidual {n prefixLen : Nat} (h : prefixLen ≤ n)
    (vals : Fin prefixLen → R)
    (poly : Sumcheck.PolyStmt R deg n) :
    Sumcheck.PolyStmt R deg (n - prefixLen) :=
  currentResidualGo (R := R) (deg := deg) prefixLen h vals poly

/-- The active residual for the round after a prefix of length `prefixLen`. -/
def currentRoundResidual {n prefixLen : Nat} (h : prefixLen < n)
    (prefixTr : Interaction.Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n) :
    Sumcheck.PolyStmt R deg ((n - (prefixLen + 1)) + 1) := by
  let residual :=
    currentResidual (R := R) (deg := deg) (n := n) (prefixLen := prefixLen)
      (Nat.le_of_lt h)
      (Sumcheck.challengePrefix R deg prefixLen prefixTr)
      poly
  have hk : n - prefixLen = (n - (prefixLen + 1)) + 1 := by
    omega
  simpa [hk] using residual

/-- The honest round polynomial computed from the current active residual. -/
def honestRoundPoly {m_dom : ℕ} (D : Fin m_dom → R)
    {numVars : ℕ}
    (poly : Sumcheck.PolyStmt R deg (numVars + 1)) :
    CDegreeLE R deg :=
  ⟨CMvPolynomial.roundPoly D numVars poly.1,
    CMvPolynomial.roundPoly_natDegree_le D poly.1 (fun mono hmono =>
      poly.2 ⟨0, by omega⟩ mono hmono)⟩

/-- The honest round polynomial sent after the prefix transcript `prefixTr`. -/
def honestRoundPolyAtPrefix {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Interaction.Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n) :
    CDegreeLE R deg :=
  honestRoundPoly (R := R) (deg := deg) D <|
    currentRoundResidual (R := R) (deg := deg) h prefixTr poly

/-- The honest prover step for one native oracle round, specialized to the
original polynomial and already-recorded challenge prefix. -/
def roundProverStep (m : Type → Type) [Monad m]
    {NextState : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Interaction.Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n)
    (computeNext : R → NextState) :
    Interaction.Spec.Strategy.withRoles m
      (roundSpec R deg).toInteractionSpec
      ((roundSpec R deg).toSpecRoles (roundRoles R deg))
      (fun _ => NextState) :=
  let sentPoly := honestRoundPolyAtPrefix (R := R) (deg := deg) D h prefixTr poly
  pure ⟨sentPoly, fun chal => pure (computeNext chal)⟩

/-- The honest prover step for one native oracle round, specialized to a private
residual polynomial witness that is threaded across rounds. -/
def roundProverStepStateful (m : Type → Type) [Monad m]
    {NextState : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {numVars : ℕ}
    (poly : Sumcheck.PolyStmt R deg (numVars + 1))
    (computeNext : R → NextState) :
    Interaction.Spec.Strategy.withRoles m
      (roundSpec R deg).toInteractionSpec
      ((roundSpec R deg).toSpecRoles (roundRoles R deg))
      (fun _ => NextState) :=
  let sentPoly := honestRoundPoly (R := R) (deg := deg) D poly
  pure ⟨sentPoly, fun chal => pure (computeNext chal)⟩

@[simp]
theorem roundProverStepStateful_fromResidual
    {m : Type → Type} [Monad m]
    {NextState : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {n prefixLen : ℕ} (h : prefixLen < n)
    (prefixTr : Interaction.Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n)
    (computeNext : R → NextState) :
    roundProverStepStateful (m := m) (R := R) (deg := deg) D
      (currentRoundResidual (R := R) (deg := deg) h prefixTr poly)
      computeNext =
      roundProverStep (m := m) (R := R) (deg := deg) D h prefixTr poly computeNext := by
  rfl

/-- Native one-round sum-check oracle reduction. The input oracle statement is
the original polynomial in `numVars + 1` variables, and it is preserved
unchanged as the output oracle statement. -/
noncomputable def roundReduction
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Reduction oSpec
      (RoundClaim R)
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDeco R deg)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ _ => PUnit) where
  prover target sWithOracles _ := do
    let prefixTr : Interaction.Spec.Transcript (Sumcheck.fullSpec R deg 0) := by
      simpa [Sumcheck.fullSpec] using
        (show Interaction.Spec.Transcript ((Sumcheck.roundSpec R deg).replicate 0) from ⟨⟩)
    let poly := sWithOracles.oracleStmt ()
    pure <|
      roundProverStep (m := OracleComp oSpec) (R := R) (deg := deg) D
        (n := numVars + 1) (prefixLen := 0) (Nat.succ_pos numVars) prefixTr poly
        (fun chal =>
          let nextClaim : Option (RoundClaim R) :=
            some <|
              CPolynomial.eval chal
                (honestRoundPolyAtPrefix (R := R) (deg := deg) D
                  (Nat.succ_pos numVars) prefixTr poly).1
          (⟨⟨nextClaim, sWithOracles.oracleStmt⟩, PUnit.unit⟩ :
            HonestProverOutput
              (StatementWithOracles (fun _ => Option (RoundClaim R))
                (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) target)
              PUnit))
  verifier := {
    toFun := fun target _ =>
      verifierStep (R := R) (deg := deg)
        (Sumcheck.PolyFamily R deg (numVars + 1)) []ₒ D target sampleChallenge
    simulate := fun _ _ q =>
      liftM <| ([Sumcheck.PolyFamily R deg (numVars + 1)]ₒ).query q
  }

/-- Native one-round sum-check oracle reduction with a private residual
polynomial witness. The public oracle statement stays fixed as the original
polynomial, while the witness shrinks from `numVars + 1` variables to
`numVars` after the sampled challenge. -/
noncomputable def roundReductionStateful
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (numVars : ℕ)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Reduction oSpec
      (RoundClaim R)
      (fun _ => roundSpec R deg)
      (fun _ => roundRoles R deg)
      (fun _ => roundOracleDeco R deg)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ => Sumcheck.PolyStmt R deg (numVars + 1))
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg (numVars + 1))
      (fun _ _ => Sumcheck.PolyStmt R deg numVars) where
  prover target sWithOracles witness := do
    let sentPoly := honestRoundPoly (R := R) (deg := deg) D witness
    pure <|
      roundProverStepStateful (m := OracleComp oSpec) (R := R) (deg := deg) D witness
        (fun chal =>
          let nextClaim : Option (RoundClaim R) := some (CPolynomial.eval chal sentPoly.1)
          (⟨⟨nextClaim, sWithOracles.oracleStmt⟩,
              stepResidual (R := R) (deg := deg) chal witness⟩ :
            HonestProverOutput
              (StatementWithOracles (fun _ => Option (RoundClaim R))
                (fun _ => Sumcheck.PolyFamily R deg (numVars + 1)) target)
              (Sumcheck.PolyStmt R deg numVars)))
  verifier := {
    toFun := fun target _ =>
      verifierStep (R := R) (deg := deg)
        (Sumcheck.PolyFamily R deg (numVars + 1)) []ₒ D target sampleChallenge
    simulate := fun _ _ q =>
      liftM <| ([Sumcheck.PolyFamily R deg (numVars + 1)]ₒ).query q
  }

end

end NativeOracle

end Sumcheck
