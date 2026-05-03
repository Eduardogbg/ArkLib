/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Core

/-!
# Native Oracle.Spec Execution

Concrete execution for native `Interaction.Oracle.Spec` reductions. The
transitional `OracleDecoration` execution layer has been quarantined under
`ArkLib.Interaction.Oracle.Legacy.Execution`.
-/

open OracleComp OracleSpec

namespace Interaction

/-! ## Execution for Oracle.Spec-based reductions -/

namespace Oracle

/-- Run a prover strategy against a verifier counterpart on `Oracle.Spec`,
threading accumulated oracle access. This is the `Oracle.Spec` analog of
`OracleDecoration.runWithOracleCounterpart`. -/
def Spec.runWithOracleCounterpart
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id) :
    (s : Spec) → (roles : Spec.RoleDeco s) → (od : Spec.OracleDeco s) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) → QueryImpl accSpec Id →
    {OutputP OutputC : Interaction.Spec.Transcript s.toInteractionSpec → Type} →
    Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
      s.toInteractionSpec (s.toSpecRoles roles) OutputP →
    Interaction.Spec.Counterpart.withMonads s.toInteractionSpec (s.toSpecRoles roles)
      (s.toMonadDecoration oSpec OStmtIn roles od accSpec) OutputC →
    OracleComp oSpec ((tr : Interaction.Spec.Transcript s.toInteractionSpec) ×
      OutputP tr × OutputC tr)
  | .done, _, _, _, _, _, _, _, output, cOutput =>
      pure ⟨⟨⟩, output, cOutput⟩
  | .«public» _ rest, ⟨.sender, rRest⟩, odRest, _, accSpec, accImpl, _, _,
      send, dualFn => do
      let ⟨x, next⟩ ← send
      let z ← runWithOracleCounterpart inputImpl
        (rest x) (rRest x) (odRest x) accSpec accImpl next (dualFn x)
      return ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
  | .«public» X rest, ⟨.receiver, rRest⟩, odRest, _, accSpec, accImpl, OutputP, OutputC,
      respond, dualSample => do
      let routeImpl : QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
        fun
        | .inl (.inl q) => liftM (oSpec.query q)
        | .inl (.inr q) => liftM (inputImpl q)
        | .inr q => liftM (accImpl q)
      have dualSample' : OracleComp ((oSpec + [OStmtIn]ₒ) + accSpec) _ := by
        simpa using dualSample
      let z' : Sigma (fun x =>
          Interaction.Spec.Counterpart.withMonads (rest x).toInteractionSpec
            ((rest x).toSpecRoles (rRest x))
            ((rest x).toMonadDecoration oSpec OStmtIn (rRest x) (odRest x) accSpec)
            (fun p => OutputC ⟨x, p⟩)) ←
        simulateQ routeImpl dualSample'
      let x := z'.1
      let dualRest := z'.2
      let next ← respond x
      let z ← runWithOracleCounterpart inputImpl
        (rest x) (rRest x) (odRest x) accSpec accImpl next dualRest
      return ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
  | .oracle _ rest, roles, ⟨oi, odRest⟩, _, accSpec, accImpl, _, _,
      send, dualFn => do
      let ⟨x, next⟩ ← send
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id :=
        fun q => (oi.toOC.impl q).run x
      let z ← runWithOracleCounterpart inputImpl
        rest roles odRest (accSpec + @OracleInterface.spec _ oi)
        (QueryImpl.add accImpl implX) next (dualFn x)
      return ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩

/-- Execute an `Oracle.Reduction` against concrete oracle input statements.
Produces the realized transcript, prover output (statement + oracle statements +
witness), and verifier output (statement + output oracle simulation). -/
def Reduction.executeConcrete
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn shared) :
    OracleComp oSpec
      ((tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) ×
       HonestProverOutput
         (StatementWithOracles
           (fun _ => StatementOut shared ((Context shared).projectPublic tr))
           (fun _ => OStatementOut shared ((Context shared).projectPublic tr))
           shared)
         (WitnessOut shared ((Context shared).projectPublic tr)) ×
       (StatementOut shared ((Context shared).projectPublic tr) ×
        QueryImpl [OStatementOut shared ((Context shared).projectPublic tr)]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Context shared).toOracleSpec (OracleDeco shared)
                ((Context shared).projectPublic tr))))) := do
  let strategy ← reduction.prover shared s w
  let strategy' :=
    Interaction.Spec.Strategy.withRolesAndMonads.toWithRolesConstant
      (Context shared).toInteractionSpec
      ((Context shared).toSpecRoles (Roles shared))
      strategy
  let ⟨tr, proverOut, stmtOutV⟩ ←
    Spec.runWithOracleCounterpart
      (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
      (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
      strategy' (reduction.verifier.toFun shared s.stmt)
  pure ⟨tr, proverOut,
    ⟨stmtOutV,
     reduction.verifier.simulate shared ((Context shared).projectPublic tr)⟩⟩

/-- Run an arbitrary prover strategy against an `Oracle.Verifier`, producing the
full transcript, prover output, and the verifier's statement output paired with
its output oracle simulation. This is the `Oracle.Spec` analog of
`OracleVerifier.run`. -/
def Verifier.run
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut)
    (shared : SharedIn)
    (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStatementIn shared]ₒ Id)
    {OutputP : Interaction.Spec.Transcript (Context shared).toInteractionSpec → Type}
    (prover : Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
      (Context shared).toInteractionSpec
      ((Context shared).toSpecRoles (Roles shared)) OutputP) :
    OracleComp oSpec
      ((tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) ×
       OutputP tr ×
       (StatementOut shared ((Context shared).projectPublic tr) ×
        QueryImpl [OStatementOut shared ((Context shared).projectPublic tr)]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Context shared).toOracleSpec (OracleDeco shared)
                ((Context shared).projectPublic tr))))) := do
  let ⟨tr, outP, stmtOutV⟩ ←
    Spec.runWithOracleCounterpart inputImpl
      (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
      prover (verifier.toFun shared stmt)
  pure ⟨tr, outP,
    ⟨stmtOutV,
     verifier.simulate shared ((Context shared).projectPublic tr)⟩⟩

/-- Mapping the prover-side output of a strategy before execution is equivalent
to executing first and then mapping the prover component of the result.
This is the `Oracle.Spec` analog of
`OracleDecoration.runWithOracleCounterpart_mapOutputWithRoles`. -/
theorem Spec.runWithOracleCounterpart_mapOutputWithRoles
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id) :
    (s : Spec) → (roles : Spec.RoleDeco s) → (od : Spec.OracleDeco s) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) → (accImpl : QueryImpl accSpec Id) →
    {OutputP OutputP' OutputC : Interaction.Spec.Transcript s.toInteractionSpec → Type} →
    (fP : ∀ tr, OutputP tr → OutputP' tr) →
    (strat : Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
      s.toInteractionSpec (s.toSpecRoles roles) OutputP) →
    (cpt : Interaction.Spec.Counterpart.withMonads s.toInteractionSpec (s.toSpecRoles roles)
      (s.toMonadDecoration oSpec OStmtIn roles od accSpec) OutputC) →
    Spec.runWithOracleCounterpart inputImpl s roles od accSpec accImpl
      (Interaction.Spec.Strategy.mapOutputWithRoles fP strat) cpt =
      (fun z => ⟨z.1, fP z.1 z.2.1, z.2.2⟩) <$>
        Spec.runWithOracleCounterpart inputImpl s roles od accSpec accImpl strat cpt := by
  intro s roles od ιₐ accSpec accImpl OutputP OutputP' OutputC fP strat cpt
  sorry
/-
  | .done, _, _, _, _, _, _, _, _, _, output, cOutput => by
      simp [runWithOracleCounterpart, Interaction.Spec.Strategy.mapOutputWithRoles]
  | .«public» _X rest, ⟨.sender, rRest⟩, odRest, _, accSpec, accImpl,
      OutputP, OutputP', OutputC, fP, strat, cptFn => by
      simp only [Interaction.Spec.Strategy.mapOutputWithRoles,
        Interaction.Spec.Counterpart.mapReceiver, runWithOracleCounterpart,
        bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
      refine congrArg (fun k => strat >>= k) ?_
      funext ⟨x, next⟩
      let addPrefix :
          ((tr : Interaction.Spec.Transcript (rest x).toInteractionSpec) ×
            OutputP' ⟨x, tr⟩ × OutputC ⟨x, tr⟩) →
          ((tr : Interaction.Spec.Transcript
            (Oracle.Spec.public _X rest).toInteractionSpec) ×
            OutputP' tr × OutputC tr) :=
        fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
      simpa [bind_assoc, addPrefix] using
        congrArg (fun z => addPrefix <$> z)
          (runWithOracleCounterpart_mapOutputWithRoles inputImpl
            (rest x) (rRest x) (odRest x) accSpec accImpl
            (fun tr => fP ⟨x, tr⟩) next (cptFn x))
  | .«public» _X rest, ⟨.receiver, rRest⟩, odRest, _, accSpec, accImpl,
      OutputP, OutputP', OutputC, fP, strat, cpt => by
      simp only [runWithOracleCounterpart,
        Interaction.Spec.Strategy.mapOutputWithRoles,
        bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
      let routeImpl : QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
        fun
        | .inl (.inl q) => liftM (oSpec.query q)
        | .inl (.inr q) => liftM (inputImpl q)
        | .inr q => liftM (accImpl q)
      refine congrArg (fun k => simulateQ routeImpl cpt >>= k) ?_
      funext ⟨x, cptRest⟩
      refine congrArg (fun k => strat x >>= k) ?_
      funext next
      let addPrefix :
          ((tr : Interaction.Spec.Transcript (rest x).toInteractionSpec) ×
            OutputP' ⟨x, tr⟩ × OutputC ⟨x, tr⟩) →
          ((tr : Interaction.Spec.Transcript (Oracle.Spec.public _X rest).toInteractionSpec) ×
            OutputP' tr × OutputC tr) :=
        fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
      simpa [bind_assoc, addPrefix] using
        congrArg (fun z => addPrefix <$> z)
          (runWithOracleCounterpart_mapOutputWithRoles inputImpl
            (rest x) (rRest x) (odRest x) accSpec accImpl
            (fun tr => fP ⟨x, tr⟩) next cptRest)
  | .oracle _X rest, roles, ⟨oi, odRest⟩, _, accSpec, accImpl,
      OutputP, OutputP', OutputC, fP, strat, cptFn => by
      simp only [Interaction.Spec.Strategy.mapOutputWithRoles,
        Interaction.Spec.Counterpart.mapReceiver, runWithOracleCounterpart,
        bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
      refine congrArg (fun k => strat >>= k) ?_
      funext ⟨x, next⟩
      let addPrefix :
          ((tr : Interaction.Spec.Transcript rest.toInteractionSpec) ×
            OutputP' ⟨x, tr⟩ × OutputC ⟨x, tr⟩) →
          ((tr : Interaction.Spec.Transcript
            (Oracle.Spec.oracle _X rest).toInteractionSpec) ×
            OutputP' tr × OutputC tr) :=
        fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
      simpa [bind_assoc, addPrefix] using
        congrArg (fun z => addPrefix <$> z)
          (runWithOracleCounterpart_mapOutputWithRoles inputImpl
            rest roles odRest
            (accSpec + @OracleInterface.spec _ oi)
            (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run x))
            (fun tr => fP ⟨x, tr⟩) next (cptFn x))
-/

end Oracle

end Interaction
