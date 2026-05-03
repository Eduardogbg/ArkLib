/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Fri.Interaction.Core
import ArkLib.Interaction.Oracle.Execution

/-!
# Interaction-Native FRI: Native Non-final Fold Round

This module packages one non-final FRI fold round as a native
`Interaction.Oracle.Reduction`.
-/

open Interaction CompPoly CPoly OracleComp OracleSpec

namespace Fri

namespace NativeOracle

section

variable {F : Type} [BEq F] [LawfulBEq F] [DecidableEq F] [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ}
variable [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)

/-- Oracle reduction for the `i`-th non-final FRI fold round. -/
def foldRoundReduction {SharedIn : Type} {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (i : Fin k)
    (sampleChallenge : SharedIn → OracleComp oSpec F) :
    Interaction.Oracle.Reduction (ι := ι) oSpec SharedIn
      (fun _ => foldRoundSpec (F := F) (n := n) D x s i)
      (fun _ => foldRoundRoles (F := F) (n := n) D x s i)
      (fun _ => foldRoundOD (F := F) (n := n) D x s i)
      (fun _ => FoldChallengePrefix (F := F) i.1)
      (ιₛᵢ := fun _ => Fin (i.1 + 1))
      (fun _ => FoldCodewordPrefix (F := F) (n := n) D x s i.1)
      (fun _ => HonestPoly (F := F) s d i.1)
      (fun _ _ => FoldChallengePrefix (F := F) i.1.succ)
      (ιₛₒ := fun _ _ => Fin (i.1.succ + 1))
      (fun _ _ => FoldCodewordPrefix (F := F) (n := n) D x s i.1.succ)
      (fun _ _ => HonestPoly (F := F) s d i.1.succ) where
  prover shared sWithOracles witness := do
    let proverStep :
        Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
          (foldRoundSpec (F := F) (n := n) D x s i).toInteractionSpec
          ((foldRoundSpec (F := F) (n := n) D x s i).toSpecRoles
            (foldRoundRoles (F := F) (n := n) D x s i))
          (fun _ =>
            HonestProverOutput
              (StatementWithOracles
                (fun _ => FoldChallengePrefix (F := F) i.1.succ)
                (fun _ => FoldCodewordPrefix (F := F) (n := n) D x s i.1.succ)
                shared)
              (HonestPoly (F := F) s d i.1.succ)) := by
      intro α
      let nextPoly : HonestPoly (F := F) s d i.1.succ :=
        honestFoldPoly (F := F) (s := s) (d := d) witness α
      let nextCodeword : Codeword (F := F) s n i.1.succ :=
        honestCodeword (F := F) (D := D) (x := x) (s := s) (d := d) i.1.succ nextPoly
      let nextCodewordLast :
          FoldCodewordPrefix (F := F) (n := n) D x s i.1.succ (Fin.last i.1.succ) := by
        simpa [FoldCodewordPrefix] using nextCodeword
      let nextChallenges : FoldChallengePrefix (F := F) i.1.succ :=
        Fin.snoc sWithOracles.stmt α
      let nextCodewords :
          OracleStatement (FoldCodewordPrefix (F := F) (n := n) D x s i.1.succ) :=
        Fin.snoc sWithOracles.oracleStmt nextCodewordLast
      let nextOutput :
          HonestProverOutput
            (StatementWithOracles
              (fun _ => FoldChallengePrefix (F := F) i.1.succ)
              (fun _ => FoldCodewordPrefix (F := F) (n := n) D x s i.1.succ)
              shared)
            (HonestPoly (F := F) s d i.1.succ) :=
        ⟨⟨nextChallenges, nextCodewords⟩, nextPoly⟩
      simpa [Spec.SyntaxOver.Family, Spec.pairedSyntax, Spec.Participant.focal] using
        (pure <|
          (pure <|
              (show (cw : Codeword (F := F) s n i.1.succ) ×
                HonestProverOutput
                  (StatementWithOracles
                    (fun _ => FoldChallengePrefix (F := F) i.1.succ)
                    (fun _ => FoldCodewordPrefix (F := F) (n := n) D x s i.1.succ)
                    shared)
                  (HonestPoly (F := F) s d i.1.succ) from
              ⟨nextCodeword, nextOutput⟩)) :
          OracleComp oSpec
            (OracleComp oSpec
              ((cw : Codeword (F := F) s n i.1.succ) ×
                HonestProverOutput
                  (StatementWithOracles
                    (fun _ => FoldChallengePrefix (F := F) i.1.succ)
                    (fun _ => FoldCodewordPrefix (F := F) (n := n) D x s i.1.succ)
                    shared)
                  (HonestPoly (F := F) s d i.1.succ))))
    pure proverStep
  verifier := {
    toFun := fun shared prevChallenges => do
      let α ← sampleChallenge shared
      return ⟨α, fun _ => Fin.snoc prevChallenges α⟩
    simulate := fun _ pt => fun ⟨j, q⟩ =>
      by
        cases j using Fin.lastCases with
        | last =>
            exact liftM <|
              ((foldRoundSpec (F := F) (n := n) D x s i).toOracleSpec
                (foldRoundOD (F := F) (n := n) D x s i) pt).query (.inl q)
        | cast j =>
            exact liftM <|
              ([FoldCodewordPrefix (F := F) (n := n) D x s i.1]ₒ).query ⟨j, q⟩
  }

end

end NativeOracle

end Fri
