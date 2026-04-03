import ArkLib.Interaction.Boundary.Reification

/-!
# Interaction-Native Boundaries: Compatibility Predicates

This module defines the semantic predicates used to transport completeness and
soundness across plain and oracle boundaries.

The plain layer is stated directly over the projection-first boundary core:

- `Statement.IsSound`
- `Context.IsComplete`

The oracle layer is then reduced to the plain one by flattening oracle-aware
boundaries into ordinary boundaries on `StatementWithOracles`.
-/

namespace Interaction
namespace Boundary

/-- A statement lifting is sound when:

1. invalid outer inputs project to invalid inner inputs, and
2. invalid inner outputs lift to invalid outer outputs, assuming the caller's
   compatibility predicate. -/
class Statement.IsSound
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (boundary : Statement projection InnerStmtOut OuterStmtOut)
    (outerLangIn : Set OuterStmtIn)
    (innerLangIn : Set InnerStmtIn)
    (outerLangOut :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        Set (OuterStmtOut outer tr))
    (innerLangOut :
      (inner : InnerStmtIn) →
        (tr : Spec.Transcript (InnerSpec inner)) →
        Set (InnerStmtOut inner tr))
    (compat :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        InnerStmtOut (projection.proj outer) tr →
        Prop) where
  proj_sound :
    ∀ outer, outer ∉ outerLangIn → projection.proj outer ∉ innerLangIn
  lift_sound :
    ∀ outer tr innerStmtOut,
      compat outer tr innerStmtOut →
      innerStmtOut ∉ innerLangOut (projection.proj outer) tr →
      boundary.lift outer tr innerStmtOut ∉ outerLangOut outer tr

/-- A context lifting is complete when:

1. valid outer inputs project to valid inner inputs, and
2. valid inner outputs lift to valid outer outputs, assuming the caller's
   compatibility predicate. -/
class Context.IsComplete
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (boundary : Context projection
      OuterWitIn InnerWitIn
      InnerStmtOut OuterStmtOut
      InnerWitOut OuterWitOut)
    (outerRelIn : Set (OuterStmtIn × OuterWitIn))
    (innerRelIn : Set (InnerStmtIn × InnerWitIn))
    (outerRelOut :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        OuterStmtOut outer tr →
        OuterWitOut outer tr →
        Prop)
    (innerRelOut :
      (inner : InnerStmtIn) →
        (tr : Spec.Transcript (InnerSpec inner)) →
        InnerStmtOut inner tr →
        InnerWitOut inner tr →
        Prop)
    (compat :
      (outer : OuterStmtIn) →
        OuterWitIn →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        InnerStmtOut (projection.proj outer) tr →
        InnerWitOut (projection.proj outer) tr →
        Prop) where
  proj_complete :
    ∀ outerStmt outerWit,
      (outerStmt, outerWit) ∈ outerRelIn →
      (projection.proj outerStmt,
        boundary.wit.proj outerStmt outerWit) ∈ innerRelIn
  lift_complete :
    ∀ outerStmt outerWit tr innerStmtOut innerWitOut,
      compat outerStmt outerWit tr innerStmtOut innerWitOut →
      (outerStmt, outerWit) ∈ outerRelIn →
      innerRelOut
        (projection.proj outerStmt)
        tr
        innerStmtOut
        innerWitOut →
      let out := boundary.lift outerStmt outerWit tr innerStmtOut innerWitOut
      outerRelOut outerStmt tr out.1 out.2

namespace OracleStatement

variable
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {toStatement : Statement projection InnerStmtOut OuterStmtOut}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
        (tr : Spec.Transcript (InnerSpec s)) →
        Innerιₛₒ s tr →
        Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        Outerιₛₒ outer tr →
        Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]

/-- Flatten an oracle statement boundary into a plain boundary on
`StatementWithOracles`. -/
@[inline] def toConcreteStatement
    (boundary :
      OracleStatement toStatement
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut) :
    Statement
      (StatementProjection.mk
        (OuterStmtIn := StatementWithOracles OuterStmtIn OuterOStmtIn)
        (InnerStmtIn := StatementWithOracles InnerStmtIn InnerOStmtIn)
        (InnerSpec := fun inner => InnerSpec inner.stmt)
        (proj := fun outer =>
          ⟨projection.proj outer.stmt,
            boundary.reification.materializeIn outer.stmt outer.oracleStmt⟩))
      (fun inner tr =>
        StatementWithOracles
          (InnerStmtOut inner.stmt tr)
          (InnerOStmtOut inner.stmt tr))
      (fun outer tr =>
        StatementWithOracles
          (OuterStmtOut outer.stmt tr)
          (OuterOStmtOut outer.stmt tr)) where
  lift := fun outer tr innerOut =>
    ⟨toStatement.lift outer.stmt tr innerOut.stmt,
      boundary.reification.materializeOut
        outer.stmt
        outer.oracleStmt
        tr
        innerOut.oracleStmt⟩

/-- Soundness for an oracle statement boundary is the plain soundness predicate
applied to its flattened concrete view. -/
abbrev IsSound
    (boundary :
      OracleStatement toStatement
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (outerLangIn :
      Set (StatementWithOracles OuterStmtIn OuterOStmtIn))
    (innerLangIn :
      Set (StatementWithOracles InnerStmtIn InnerOStmtIn))
    (outerLangOut :
      (outer : StatementWithOracles OuterStmtIn OuterOStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer.stmt))) →
        Set
          (StatementWithOracles
            (OuterStmtOut outer.stmt tr)
            (OuterOStmtOut outer.stmt tr)))
    (innerLangOut :
      (inner : StatementWithOracles InnerStmtIn InnerOStmtIn) →
        (tr : Spec.Transcript (InnerSpec inner.stmt)) →
        Set
          (StatementWithOracles
            (InnerStmtOut inner.stmt tr)
            (InnerOStmtOut inner.stmt tr)))
    (compat :
      (outer : StatementWithOracles OuterStmtIn OuterOStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer.stmt))) →
        StatementWithOracles
          (InnerStmtOut (projection.proj outer.stmt) tr)
          (InnerOStmtOut (projection.proj outer.stmt) tr) →
        Prop) :=
  Statement.IsSound
    boundary.toConcreteStatement
    outerLangIn
    innerLangIn
    outerLangOut
    innerLangOut
    compat

end OracleStatement

namespace OracleContext

variable
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {toContext : Context projection
      OuterWitIn InnerWitIn
      InnerStmtOut OuterStmtOut
      InnerWitOut OuterWitOut}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
        (tr : Spec.Transcript (InnerSpec s)) →
        Innerιₛₒ s tr →
        Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
        Outerιₛₒ outer tr →
        Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]

/-- Flatten an oracle context boundary into a plain context boundary on
`StatementWithOracles`. -/
@[inline] def toConcreteContext
  (boundary :
      OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut) :
    Context
      (StatementProjection.mk
        (OuterStmtIn := StatementWithOracles OuterStmtIn OuterOStmtIn)
        (InnerStmtIn := StatementWithOracles InnerStmtIn InnerOStmtIn)
        (InnerSpec := fun inner => InnerSpec inner.stmt)
        (proj := fun outer =>
          ⟨projection.proj outer.stmt,
            boundary.reification.materializeIn outer.stmt outer.oracleStmt⟩))
      OuterWitIn
      InnerWitIn
      (fun inner tr =>
        StatementWithOracles
          (InnerStmtOut inner.stmt tr)
          (InnerOStmtOut inner.stmt tr))
      (fun outer tr =>
        StatementWithOracles
          (OuterStmtOut outer.stmt tr)
          (OuterOStmtOut outer.stmt tr))
      (fun inner tr => InnerWitOut inner.stmt tr)
      (fun outer tr => OuterWitOut outer.stmt tr) where
  stmt := {
    lift := fun outer tr innerOut =>
      ⟨toContext.stmt.lift outer.stmt tr innerOut.stmt,
        boundary.reification.materializeOut
          outer.stmt
          outer.oracleStmt
          tr
          innerOut.oracleStmt⟩
  }
  witProj := {
    proj := fun outer outerWit =>
      toContext.wit.proj outer.stmt outerWit
  }
  wit := {
    lift := fun outer outerWit tr innerStmtOut innerWitOut =>
      toContext.wit.lift
        outer.stmt
        outerWit
        tr
        innerStmtOut.stmt
        innerWitOut
  }

/-- Completeness for an oracle context boundary is the plain completeness
predicate applied to its flattened concrete view. -/
abbrev IsComplete
    (boundary :
      OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (outerRelIn :
      Set
        (StatementWithOracles OuterStmtIn OuterOStmtIn × OuterWitIn))
    (innerRelIn :
      Set
        (StatementWithOracles InnerStmtIn InnerOStmtIn × InnerWitIn))
    (outerRelOut :
      (outer : StatementWithOracles OuterStmtIn OuterOStmtIn) →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer.stmt))) →
        StatementWithOracles
          (OuterStmtOut outer.stmt tr)
          (OuterOStmtOut outer.stmt tr) →
        OuterWitOut outer.stmt tr →
        Prop)
    (innerRelOut :
      (inner : StatementWithOracles InnerStmtIn InnerOStmtIn) →
        (tr : Spec.Transcript (InnerSpec inner.stmt)) →
        StatementWithOracles
          (InnerStmtOut inner.stmt tr)
          (InnerOStmtOut inner.stmt tr) →
        InnerWitOut inner.stmt tr →
        Prop)
    (compat :
      (outer : StatementWithOracles OuterStmtIn OuterOStmtIn) →
        OuterWitIn →
        (tr : Spec.Transcript (InnerSpec (projection.proj outer.stmt))) →
        StatementWithOracles
          (InnerStmtOut (projection.proj outer.stmt) tr)
          (InnerOStmtOut (projection.proj outer.stmt) tr) →
        InnerWitOut (projection.proj outer.stmt) tr →
        Prop) :=
  Context.IsComplete
    boundary.toConcreteContext
    outerRelIn
    innerRelIn
    outerRelOut
    innerRelOut
    compat

end OracleContext

end Boundary
end Interaction
