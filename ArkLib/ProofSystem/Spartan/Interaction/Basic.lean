/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.ConstraintSystem.R1CS
import ArkLib.Data.Fin.Basic
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Interaction.Oracle.Composition
import ArkLib.Interaction.Boundary.Reification
import ArkLib.ProofSystem.Sumcheck.Interaction.General

/-!
# Spartan Interaction Layer

This module starts the Spartan PIOP directly on `Interaction.Oracle.Reduction`.
The prefix formalized here is the protocol setup:

1. the prover exposes the witness multilinear extension as an oracle message;
2. the verifier samples the first challenge `τ : Fin ℓ_m → R`;
3. the resulting state keeps the R1CS matrix oracles and witness oracle in one
   oracle-statement family, ready for the first sum-check boundary/view.

The first sum-check polynomial is virtual: it is derived from the statement,
matrix oracles, witness oracle, and challenge. We name the relevant types here,
but leave the actual derived-oracle view to the next layer so the query-routing
API can be shared by Spartan and other protocols.
-/

open MvPolynomial Matrix
open Interaction OracleComp OracleSpec
open scoped BigOperators

namespace Spartan

namespace OracleLayer

noncomputable section

/-- Public parameters for the padded Spartan protocol. The R1CS dimensions are
`2 ^ ℓ_m`, `2 ^ ℓ_n`, and `2 ^ ℓ_w`. -/
structure PublicParams where
  ℓ_m : ℕ
  ℓ_n : ℕ
  ℓ_w : ℕ
  ℓ_w_le_ℓ_n : ℓ_w ≤ ℓ_n := by omega

namespace PublicParams

/-- R1CS dimensions determined by Spartan's padded public parameters. -/
def toSizeR1CS (pp : PublicParams) : R1CS.Size where
  m := 2 ^ pp.ℓ_m
  n := 2 ^ pp.ℓ_n
  n_w := 2 ^ pp.ℓ_w
  n_w_le_n := Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n

end PublicParams

section Types

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)

/-- Public R1CS input. -/
abbrev Statement : Type :=
  R1CS.Statement R pp.toSizeR1CS

/-- Matrix oracle family for the R1CS instance. -/
abbrev InputOracleFamily : R1CS.MatrixIdx → Type :=
  R1CS.OracleStatement R pp.toSizeR1CS

/-- Private R1CS witness. -/
abbrev Witness : Type :=
  R1CS.Witness R pp.toSizeR1CS

/-- The R1CS relation induced by Spartan's padded public parameters. -/
abbrev relation
    (stmt : Statement R pp)
    (oracleStmt : OracleStatement (InputOracleFamily R pp))
    (witness : Witness R pp) : Prop :=
  R1CS.relation R pp.toSizeR1CS stmt oracleStmt witness

/-- After the witness oracle message, the verifier has access to both the input
matrix oracle family and the witness oracle. -/
abbrev WithWitnessOracleFamily : R1CS.MatrixIdx ⊕ Unit → Type :=
  Sum.elim (InputOracleFamily R pp) (fun _ => Witness R pp)

/-- First Spartan challenge, sampled over the constraint-index variables. -/
abbrev FirstChallenge : Type :=
  Fin pp.ℓ_m → R

/-- Local state after the first challenge: challenge plus public R1CS input. -/
abbrev AfterFirstChallengeStatement : Type :=
  FirstChallenge R pp × Statement R pp

/-- Oracle family after the first challenge is unchanged from the post-witness
state. -/
abbrev AfterFirstChallengeOracleFamily : R1CS.MatrixIdx ⊕ Unit → Type :=
  WithWitnessOracleFamily R pp

/-- Spartan's first sum-check checks a degree-three virtual polynomial in the
constraint-index variables. -/
def firstSumcheckDegree : ℕ :=
  3

/-- The first sum-check input claim is the zero claim. -/
abbrev FirstSumcheckClaim : Type :=
  Sumcheck.RoundClaim R

/-- Queryable view of Spartan's first virtual sum-check polynomial. -/
abbrev FirstSumcheckOracle : Type :=
  (Fin pp.ℓ_m → R) → R

/-- Singleton oracle family carrying the first virtual sum-check polynomial. -/
abbrev FirstSumcheckOracleFamily : Unit → Type :=
  fun _ => FirstSumcheckOracle R pp

/-- Local state after the first sum-check: verifier result plus the previous
Spartan state. -/
abbrev AfterFirstSumcheckStatement : Type :=
  Option (FirstSumcheckClaim R) × AfterFirstChallengeStatement R pp

/-- The Spartan oracle family is unchanged by the first sum-check view. -/
abbrev AfterFirstSumcheckOracleFamily : R1CS.MatrixIdx ⊕ Unit → Type :=
  WithWitnessOracleFamily R pp

end Types

section SumcheckTypes

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R]
variable (pp : PublicParams)

/-- Typed witness for a materialized first sum-check polynomial. The actual
Spartan prover should obtain this through a reusable derived-oracle view rather
than by making the verifier carry an ad hoc polynomial witness. -/
abbrev FirstSumcheckWitness : Type :=
  Sumcheck.PolyStmt R firstSumcheckDegree pp.ℓ_m

end SumcheckTypes

section OracleInterfaces

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)

/-- Matrix oracles are queried by evaluating their multilinear extensions at a
constraint point and a variable point. -/
instance instOracleInterfaceInputOracleFamily :
    ∀ i, OracleInterface (InputOracleFamily R pp i) :=
  fun _ => {
    Query := (Fin pp.ℓ_m → R) × (Fin pp.ℓ_n → R)
    toOC.spec := fun _ => R
    toOC.impl := fun ⟨x, y⟩ => do
      return (← read).toMLE ⸨C ∘ x⸩ ⸨y⸩
  }

/-- The witness oracle is queried by evaluating the witness multilinear
extension. -/
instance instOracleInterfaceWitness :
    OracleInterface (Witness R pp) where
  Query := Fin pp.ℓ_w → R
  toOC.spec := fun _ => R
  toOC.impl := fun evalPoint => do
    return (MLE ((← read) ∘ finFunctionFinEquiv)) ⸨evalPoint⸩

/-- Oracle interface for the combined matrix-plus-witness oracle family. -/
instance instOracleInterfaceWithWitnessOracleFamily :
    ∀ i, OracleInterface (WithWitnessOracleFamily R pp i)
  | .inl i => instOracleInterfaceInputOracleFamily R pp i
  | .inr _ => instOracleInterfaceWitness R pp

/-- The virtual first sum-check oracle is queried by evaluation point. -/
instance instOracleInterfaceFirstSumcheckOracleFamily :
    ∀ i, OracleInterface (FirstSumcheckOracleFamily R pp i) :=
  fun _ => inferInstance

end OracleInterfaces

section FirstSumcheckView

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)

/-- Embed a public-input coordinate into the full padded R1CS vector index. -/
def publicFullIndex (i : Fin pp.toSizeR1CS.n_x) :
    Fin pp.toSizeR1CS.n :=
  ⟨i.1, lt_of_lt_of_le i.2 (by simp [R1CS.Size.n_x])⟩

/-- Embed a witness coordinate into the full padded R1CS vector index. -/
def witnessFullIndex (i : Fin pp.toSizeR1CS.n_w) :
    Fin pp.toSizeR1CS.n :=
  ⟨pp.toSizeR1CS.n_x + i.1, by
    have hn := pp.toSizeR1CS.n_w_le_n
    have hi := i.2
    simp [R1CS.Size.n_x] at hi ⊢
    omega⟩

/-- Evaluate the multilinear extension of the concatenated R1CS vector using
the public statement and queries to the witness oracle. -/
def zEvalByQueries
    (stmt : Statement R pp) (point : Fin pp.ℓ_n → R) :
    OracleComp [WithWitnessOracleFamily R pp]ₒ R := do
  let publicPart :=
    ∑ i : Fin pp.toSizeR1CS.n_x,
      MvPolynomial.eqWeight (R := R) point (publicFullIndex pp i) * stmt i
  let witnessTerms ← Fin.traverseM fun i : Fin pp.toSizeR1CS.n_w => do
    let wi : R ← liftM <|
      ([WithWitnessOracleFamily R pp]ₒ).query
        ⟨.inr (), MvPolynomial.booleanPoint (R := R) pp.ℓ_w i⟩
    pure <| MvPolynomial.eqWeight (R := R) point (witnessFullIndex pp i) * wi
  pure <| publicPart + ∑ i : Fin pp.toSizeR1CS.n_w, witnessTerms i

/-- Evaluate `M z` at a constraint point using queries to the matrix oracle and
the derived `z` evaluator. -/
def matrixVecEvalByQueries
    (matrix : R1CS.MatrixIdx) (stmt : Statement R pp)
    (constraintPoint : Fin pp.ℓ_m → R) :
    OracleComp [WithWitnessOracleFamily R pp]ₒ R := do
  let terms ← Fin.traverseM fun i : Fin pp.toSizeR1CS.n => do
    let variablePoint := MvPolynomial.booleanPoint (R := R) pp.ℓ_n i
    let matrixValue : R ← liftM <|
      ([WithWitnessOracleFamily R pp]ₒ).query
        ⟨.inl matrix, (constraintPoint, variablePoint)⟩
    let zValue ← zEvalByQueries (R := R) pp stmt variablePoint
    pure <| matrixValue * zValue
  pure <| ∑ i : Fin pp.toSizeR1CS.n, terms i

/-- Query evaluator for Spartan's first virtual sum-check polynomial. -/
def firstSumcheckEvalByQueries
    (state : AfterFirstChallengeStatement R pp)
    (constraintPoint : Fin pp.ℓ_m → R) :
    OracleComp [WithWitnessOracleFamily R pp]ₒ R := do
  let τ := state.1
  let stmt := state.2
  let a ← matrixVecEvalByQueries (R := R) pp .A stmt constraintPoint
  let b ← matrixVecEvalByQueries (R := R) pp .B stmt constraintPoint
  let c ← matrixVecEvalByQueries (R := R) pp .C stmt constraintPoint
  pure <| MvPolynomial.eval constraintPoint (eqPolynomial τ) * (a * b - c)

/-- Simulate queries to the first virtual sum-check oracle using the post-setup
R1CS matrix and witness oracle family. -/
def simulateFirstSumcheckOracle
    (state : AfterFirstChallengeStatement R pp) :
    QueryImpl [FirstSumcheckOracleFamily R pp]ₒ
      (OracleComp [WithWitnessOracleFamily R pp]ₒ)
  | ⟨(), point⟩ => firstSumcheckEvalByQueries (R := R) pp state point

/-- Materialize the first virtual sum-check oracle from concrete post-setup
oracle data. -/
def firstSumcheckOracle
    (state : AfterFirstChallengeStatement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp)) :
    FirstSumcheckOracle R pp :=
  fun point =>
    simulateQ
      (OracleInterface.toOracleImpl (WithWitnessOracleFamily R pp) oracleStmt)
      (firstSumcheckEvalByQueries (R := R) pp state point)

/-- Materialize the singleton first-sumcheck oracle family. -/
def firstSumcheckOracleStmt
    (state : AfterFirstChallengeStatement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp)) :
    OracleStatement (FirstSumcheckOracleFamily R pp)
  | () => firstSumcheckOracle (R := R) pp state oracleStmt

end FirstSumcheckView

section FirstSumcheckBoundary

variable (R : Type) [BEq R] [CommRing R] [IsDomain R] [Fintype R]
  [LawfulBEq R] [Nontrivial R]
variable (pp : PublicParams)

/-- Sum-check context used for Spartan's first virtual polynomial. -/
abbrev firstSumcheckContext : Interaction.Oracle.Spec :=
  Sumcheck.context R firstSumcheckDegree pp.ℓ_m

/-- Role decoration for Spartan's first sum-check. -/
abbrev firstSumcheckRoles :
    Interaction.Oracle.Spec.RoleDeco (firstSumcheckContext R pp) :=
  Sumcheck.roles R firstSumcheckDegree pp.ℓ_m

/-- Oracle-message decoration for Spartan's first sum-check. -/
abbrev firstSumcheckOracleDeco :
    Interaction.Oracle.Spec.OracleDeco (firstSumcheckContext R pp) :=
  Sumcheck.oracleDeco R firstSumcheckDegree pp.ℓ_m

/-- Boundary projection from Spartan's post-setup state to the zero sum-check
claim. -/
def firstSumcheckStatementProjection :
    Interaction.Boundary.OracleStatementProjection
      (AfterFirstChallengeStatement R pp)
      (FirstSumcheckClaim R)
      (fun _ => firstSumcheckContext R pp) where
  proj := fun _ => 0

/-- Lift the sum-check verifier result back into the Spartan state. -/
def firstSumcheckStatementLift :
    Interaction.Boundary.OracleStatementLift
      (firstSumcheckStatementProjection R pp)
      (fun _ _ => Option (FirstSumcheckClaim R))
      (fun _ _ => AfterFirstSumcheckStatement R pp) where
  lift := fun outer _ result => ⟨result, outer⟩

/-- Oracle-access boundary for Spartan's first virtual sum-check polynomial.

Input queries to the inner singleton polynomial oracle are evaluated through the
post-setup matrix and witness oracle family. Output queries keep the original
Spartan oracle family available after the sum-check. -/
def firstSumcheckOracleAccess
    (state : AfterFirstChallengeStatement R pp) :
    Interaction.Boundary.OracleStatementAccess
      (InnerContext := firstSumcheckContext R pp)
      (WithWitnessOracleFamily R pp)
      (FirstSumcheckOracleFamily R pp)
      (fun _ => FirstSumcheckOracleFamily R pp)
      (fun _ => AfterFirstSumcheckOracleFamily R pp) where
  simulateIn :=
    simulateFirstSumcheckOracle (R := R) pp state
  simulateOut := fun _ q =>
    liftM <| ([WithWitnessOracleFamily R pp]ₒ).query q

/-- Spartan's first sum-check verifier obtained by pulling the generic
sum-check verifier through the virtual-polynomial oracle boundary. -/
def firstSumcheckVerifier {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Verifier oSpec
      (AfterFirstChallengeStatement R pp)
      (fun _ => firstSumcheckContext R pp)
      (fun _ => firstSumcheckRoles R pp)
      (fun _ => firstSumcheckOracleDeco R pp)
      (fun _ => PUnit)
      (fun _ => WithWitnessOracleFamily R pp)
      (fun _ _ => AfterFirstSumcheckStatement R pp)
      (fun _ _ => AfterFirstSumcheckOracleFamily R pp) :=
  Interaction.Oracle.Verifier.pullback
    (projection := firstSumcheckStatementProjection R pp)
    (toStatement := firstSumcheckStatementLift R pp)
    (OuterOStmtIn := fun _ => WithWitnessOracleFamily R pp)
    (InnerOStmtIn := fun _ => FirstSumcheckOracleFamily R pp)
    (InnerOStmtOut := fun _ _ => FirstSumcheckOracleFamily R pp)
    (OuterOStmtOut := fun _ _ => AfterFirstSumcheckOracleFamily R pp)
    (fun outer => firstSumcheckOracleAccess R pp outer)
    (Sumcheck.reduction (R := R) (deg := firstSumcheckDegree)
      (OStatementIn := FirstSumcheckOracleFamily R pp)
      D sampleChallenge pp.ℓ_m).verifier

/-- Spartan's first sum-check reduction as a boundary around the generic
sum-check reduction.

The input witness is the materialized degree-bounded first sum-check
polynomial. The verifier sees it only through the derived virtual oracle
boundary; the prover materializes the singleton inner oracle from the concrete
post-setup matrix and witness oracle family. -/
def firstSumcheckReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Reduction oSpec
      (AfterFirstChallengeStatement R pp)
      (fun _ => firstSumcheckContext R pp)
      (fun _ => firstSumcheckRoles R pp)
      (fun _ => firstSumcheckOracleDeco R pp)
      (fun _ => PUnit)
      (fun _ => WithWitnessOracleFamily R pp)
      (fun _ => FirstSumcheckWitness R pp)
      (fun _ _ => AfterFirstSumcheckStatement R pp)
      (fun _ _ => AfterFirstSumcheckOracleFamily R pp)
      (fun _ _ => Sumcheck.PolyStmt R firstSumcheckDegree 0) where
  prover state sWithOracles witness := do
    let innerReduction :=
      Sumcheck.reduction (R := R) (deg := firstSumcheckDegree)
        (OStatementIn := FirstSumcheckOracleFamily R pp)
        D sampleChallenge pp.ℓ_m
    let innerOracleStmt :=
      firstSumcheckOracleStmt (R := R) pp state sWithOracles.oracleStmt
    let strat ←
      innerReduction.prover
        (0 : FirstSumcheckClaim R)
        ⟨PUnit.unit, innerOracleStmt⟩
        witness
    pure <|
      Interaction.Spec.Strategy.withRolesAndMonads.mapOutput
        (firstSumcheckContext R pp).toInteractionSpec
        ((firstSumcheckContext R pp).toSpecRoles (firstSumcheckRoles R pp))
        ((firstSumcheckContext R pp).toProverMonadDecoration oSpec)
        (fun _ out =>
          (⟨⟨⟨out.stmt.stmt, state⟩, sWithOracles.oracleStmt⟩, out.wit⟩ :
            HonestProverOutput
              (StatementWithOracles
                (fun _ => AfterFirstSumcheckStatement R pp)
                (fun _ => AfterFirstSumcheckOracleFamily R pp)
                state)
              (Sumcheck.PolyStmt R firstSumcheckDegree 0)))
        strat
  verifier :=
    firstSumcheckVerifier (R := R) (pp := pp) D sampleChallenge

end FirstSumcheckBoundary

section WitnessOracleRound

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)

/-- First Spartan round: the prover sends the witness oracle. -/
def witnessSpec : Interaction.Oracle.Spec :=
  .oracle (Witness R pp) .done

/-- The witness oracle is sent by the prover. -/
def witnessRoles :
    Interaction.Oracle.Spec.RoleDeco (witnessSpec R pp) :=
  ⟨⟩

/-- Oracle-interface decoration for the witness oracle message. -/
def witnessOracleDeco :
    Interaction.Oracle.Spec.OracleDeco (witnessSpec R pp) :=
  ⟨inferInstance, ⟨⟩⟩

/-- Route post-witness oracle queries either to the original matrix oracles or
to the newly sent witness oracle. -/
def simulateWithWitnessOracle :
    QueryImpl [WithWitnessOracleFamily R pp]ₒ
      (OracleComp
        ([InputOracleFamily R pp]ₒ +
          Interaction.Oracle.Spec.toOracleSpec
            (witnessSpec R pp)
            (witnessOracleDeco R pp)
            ⟨⟩))
  | ⟨.inl idx, q⟩ =>
      liftM <| ([InputOracleFamily R pp]ₒ).query ⟨idx, q⟩
  | ⟨.inr (), q⟩ =>
      liftM <|
        (Interaction.Oracle.Spec.toOracleSpec
          (witnessSpec R pp)
          (witnessOracleDeco R pp)
          ⟨⟩).query (.inl q)

/-- Spartan's first oracle reduction: append the witness oracle to the input
R1CS matrix oracle family. -/
def witnessReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι} :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => witnessSpec R pp)
      (fun _ => witnessRoles R pp)
      (fun _ => witnessOracleDeco R pp)
      (fun _ => Statement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx)
      (fun _ => InputOracleFamily R pp)
      (fun _ => Witness R pp)
      (fun _ _ => Statement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => WithWitnessOracleFamily R pp)
      (fun _ _ => PUnit) where
  prover _ sWithOracles witness := do
    let proverStep :
        Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
          (witnessSpec R pp).toInteractionSpec
          ((witnessSpec R pp).toSpecRoles (witnessRoles R pp))
          (fun _ =>
            HonestProverOutput
              (StatementWithOracles
                (fun _ => Statement R pp)
                (fun _ => WithWitnessOracleFamily R pp)
                PUnit.unit)
              PUnit) := do
      pure
        ⟨witness,
          (⟨⟨sWithOracles.stmt,
            fun
            | .inl idx => sWithOracles.oracleStmt idx
            | .inr () => witness⟩, PUnit.unit⟩ :
            HonestProverOutput
              (StatementWithOracles
                (fun _ => Statement R pp)
                (fun _ => WithWitnessOracleFamily R pp)
                PUnit.unit)
              PUnit)⟩
    pure <|
      Interaction.Spec.Strategy.withRolesAndMonads.ofWithRolesConstant
        (witnessSpec R pp).toInteractionSpec
        ((witnessSpec R pp).toSpecRoles (witnessRoles R pp))
        proverStep
  verifier := {
    toFun := fun _ stmt _ => stmt
    simulate := fun _ pt =>
      match pt with
      | ⟨⟩ => simulateWithWitnessOracle R pp
  }

end WitnessOracleRound

section FirstChallengeRound

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)

/-- Second Spartan setup round: the verifier samples `τ`. -/
def firstChallengeSpec : Interaction.Oracle.Spec :=
  .public (FirstChallenge R pp) fun _ => .done

/-- The verifier sends the first challenge. -/
def firstChallengeRoles :
    Interaction.Oracle.Spec.RoleDeco (firstChallengeSpec R pp) :=
  ⟨.receiver, fun _ => ⟨⟩⟩

/-- The first challenge round sends no oracle message. -/
def firstChallengeOracleDeco :
    Interaction.Oracle.Spec.OracleDeco (firstChallengeSpec R pp) :=
  fun _ => ⟨⟩

/-- Identity simulation for the oracle family across the first challenge. -/
def simulateAfterFirstChallenge
    (pt : Interaction.Oracle.Spec.PublicTranscript (firstChallengeSpec R pp)) :
    QueryImpl [WithWitnessOracleFamily R pp]ₒ
      (OracleComp
        ([WithWitnessOracleFamily R pp]ₒ +
          Interaction.Oracle.Spec.toOracleSpec
            (firstChallengeSpec R pp)
            (firstChallengeOracleDeco R pp)
            pt)) :=
  fun q => liftM <| ([WithWitnessOracleFamily R pp]ₒ).query q

/-- Sample the first Spartan challenge and remember it in the local statement. -/
def firstChallengeReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (sampleFirstChallenge : OracleComp oSpec (FirstChallenge R pp)) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => firstChallengeSpec R pp)
      (fun _ => firstChallengeRoles R pp)
      (fun _ => firstChallengeOracleDeco R pp)
      (fun _ => Statement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ => WithWitnessOracleFamily R pp)
      (fun _ => PUnit)
      (fun _ _ => AfterFirstChallengeStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => AfterFirstChallengeOracleFamily R pp)
      (fun _ _ => PUnit) where
  prover _ sWithOracles _ := do
    let proverStep :
        Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
          (firstChallengeSpec R pp).toInteractionSpec
          ((firstChallengeSpec R pp).toSpecRoles (firstChallengeRoles R pp))
          (fun _ =>
            HonestProverOutput
              (StatementWithOracles
                (fun _ => AfterFirstChallengeStatement R pp)
                (fun _ => AfterFirstChallengeOracleFamily R pp)
                PUnit.unit)
              PUnit) :=
      fun τ => do
        pure
          ⟨⟨⟨τ, sWithOracles.stmt⟩, sWithOracles.oracleStmt⟩, PUnit.unit⟩
    pure <|
      Interaction.Spec.Strategy.withRolesAndMonads.ofWithRolesConstant
        (firstChallengeSpec R pp).toInteractionSpec
        ((firstChallengeSpec R pp).toSpecRoles (firstChallengeRoles R pp))
        proverStep
  verifier := {
    toFun := fun _ stmt => do
      let τ ← sampleFirstChallenge
      pure ⟨τ, ⟨τ, stmt⟩⟩
    simulate := fun _ pt =>
      simulateAfterFirstChallenge R pp pt
  }

end FirstChallengeRound

section SetupPrefix

variable (R : Type) [CommRing R] [IsDomain R] [Fintype R] (pp : PublicParams)

/-- Spartan setup context: witness oracle message followed by the first
verifier challenge. -/
abbrev setupContext : Interaction.Oracle.Spec :=
  (witnessSpec R pp).append (fun _ => firstChallengeSpec R pp)

/-- Role decoration for the Spartan setup prefix. -/
abbrev setupRoles :
    Interaction.Oracle.Spec.RoleDeco (setupContext R pp) :=
  Interaction.Oracle.Spec.RoleDeco.append
    (witnessSpec R pp)
    (fun _ => firstChallengeSpec R pp)
    (witnessRoles R pp)
    (fun _ => firstChallengeRoles R pp)

/-- Oracle-message decoration for the Spartan setup prefix. -/
abbrev setupOracleDeco :
    Interaction.Oracle.Spec.OracleDeco (setupContext R pp) :=
  Interaction.Oracle.Spec.OracleDeco.append
    (witnessSpec R pp)
    (fun _ => firstChallengeSpec R pp)
    (witnessOracleDeco R pp)
    (fun _ => firstChallengeOracleDeco R pp)

/-- Spartan setup prefix as a composed oracle reduction. -/
def setupReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (sampleFirstChallenge : OracleComp oSpec (FirstChallenge R pp)) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => setupContext R pp)
      (fun _ => setupRoles R pp)
      (fun _ => setupOracleDeco R pp)
      (fun _ => Statement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx)
      (fun _ => InputOracleFamily R pp)
      (fun _ => Witness R pp)
      (fun _ _ => AfterFirstChallengeStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => AfterFirstChallengeOracleFamily R pp)
      (fun _ _ => PUnit) := by
  exact Interaction.Oracle.Reduction.comp
    (witnessReduction (R := R) (pp := pp) (oSpec := oSpec))
    (fun _ _ =>
      firstChallengeReduction (R := R) (pp := pp) (oSpec := oSpec)
        sampleFirstChallenge)

end SetupPrefix

end

end OracleLayer

end Spartan
