/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound
import ArkLib.Interaction.Oracle.Chain

/-!
# Interaction-Native Sum-Check: Native Multi-Round Surface

This module is intentionally small: it uses `Interaction.Oracle.Spec.Chain` as
the protocol-shape primitive, then gives a concrete one-round `StateT` prover
example.

The point of the state example is limited but useful. Ordinary, non-dependent
participant state, such as a challenge log, is cleanly carried by the monad. The
sum-check residual witness is more dependent: its type changes from
`PolyStmt ... (n + 1)` to `PolyStmt ... n` each round. That fits the generalized
chain composition layer as a `State : {k : Nat} → Chain k → Type`; this file
keeps the example to an ordinary challenge log.
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
def fullChain : (n : Nat) → Interaction.Oracle.Spec.Chain n
  | 0 => ⟨⟩
  | n + 1 =>
      ⟨roundSpec R deg, roundRoles R deg, roundOracleDeco R deg, fun _ => fullChain n⟩

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

/-- One native sum-check round where the prover records the verifier challenge
in its monadic state.

This is a genuine stateful-monad example: the challenge log lives in the
strategy action monad, and the terminal strategy output is just `PUnit`. -/
def challengeLogRoundStrategy
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (poly : CDegreeLE R deg) :
    Interaction.Spec.Strategy.withRoles (StateT (List R) (OracleComp oSpec))
      (roundSpec R deg).toInteractionSpec
      ((roundSpec R deg).toSpecRoles (roundRoles R deg))
      (fun _ => PUnit) := by
  unfold roundSpec roundRoles
  change StateT (List R) (OracleComp oSpec)
    ((x : CDegreeLE R deg) × (R → StateT (List R) (OracleComp oSpec) PUnit))
  exact fun log =>
    let respond : R → StateT (List R) (OracleComp oSpec) PUnit :=
      fun chal log' => pure (PUnit.unit, log' ++ [chal])
    pure (Sigma.mk poly respond, log)

/-- One-round prover setup for `challengeLogRoundStrategy`.

The setup monad is also `StateT`, but this example keeps setup pure and uses
state in the actual party continuation where the verifier challenge arrives. -/
def challengeLogRoundProver
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (poly : CDegreeLE R deg) :
    StateT (List R) (OracleComp oSpec)
      (Interaction.Spec.Strategy.withRoles (StateT (List R) (OracleComp oSpec))
        (roundSpec R deg).toInteractionSpec
        ((roundSpec R deg).toSpecRoles (roundRoles R deg))
        (fun _ => PUnit)) :=
  pure (challengeLogRoundStrategy (oSpec := oSpec) poly)

end

end NativeOracle

end Sumcheck
