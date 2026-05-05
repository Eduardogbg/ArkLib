/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Security.Basic

/-!
# Oracle Soundness

Verifier-side soundness definitions for `Interaction.Oracle`.
-/

noncomputable section

open OracleComp
open scoped ENNReal

namespace Interaction
namespace Oracle
namespace Verifier

abbrev InputLanguage
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)] :=
  (shared : SharedIn) →
  StatementIn shared →
  InputImpl OStatementIn shared →
  Prop

abbrev OutputLanguage
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)] :=
  (shared : SharedIn) →
  (inputImpl : InputImpl OStatementIn shared) →
  (pt : Spec.PublicTranscript (Context shared)) →
  StatementOut shared pt →
  OutputImpl (Context := Context) (OracleDeco := OracleDeco)
    OStatementIn OStatementOut shared pt →
  Prop

/-- Soundness for an oracle verifier. The verifier is run against an arbitrary
prover strategy and invalid input behavior, and the probability of producing an
output in the target language is bounded by `ε`. -/
def soundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut)
    (langIn : InputLanguage (StatementIn := StatementIn) (OStatementIn := OStatementIn))
    (langOut :
      OutputLanguage (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut))
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn) (stmt : StatementIn shared)
      (inputImpl : InputImpl OStatementIn shared)
      {OutputP : Interaction.Spec.Transcript
        (Context shared).toInteractionSpec → Type _}
      (prover : Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
        (Context shared).toInteractionSpec
        ((Context shared).toSpecRoles (Roles shared)) OutputP),
      ¬ langIn shared stmt inputImpl →
        Pr[fun z =>
          let pt := (Context shared).projectPublic z.1
          langOut shared inputImpl pt z.2.2.1
            (verifier.simulate shared pt)
          | verifier.run shared stmt inputImpl prover] ≤ ε

end Verifier
end Oracle
end Interaction
