/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Composition

/-!
# N-ary Chain Composition for Oracle.Spec

A `Spec.Chain n` is a self-contained recipe for an `n`-round oracle protocol:
at each level it carries the current round's `Oracle.Spec`, `RoleDeco`, and
`OracleDeco`, with a `PublicTranscript`-indexed continuation to the next level.
The chain is still only protocol shape. Stateful parties are modeled by the
composition combinators, which thread a caller-chosen state family indexed by
the remaining chain.

Converting to an `Oracle.Spec` via `Chain.toSpec` uses only `Oracle.Spec.append`.

## Main definitions

* `Oracle.Spec.Chain` — depth-indexed telescope: oracle spec + decorations +
  continuation.
* `Chain.toSpec` / `Chain.toRoles` / `Chain.toOracleDeco` — flatten a chain to a
  single `Oracle.Spec` with its decorations.
* `Chain.splitPublicTranscript` / `Chain.appendPublicTranscript` —
  `PublicTranscript` operations for the first round vs the rest.
* `Chain.outputFamily` — lift a family on remaining chains to a family on the
  flattened `PublicTranscript`.
* `Chain.Prover.comp` / `Chain.Verifier.comp` — compose per-round prover
  strategies / verifier counterparts along the chain.
* `Oracle.Reduction.ofChain` — compose per-round steps into a full
  `Oracle.Reduction`.

## Design notes

This mirrors the non-oracle `Spec.Chain` (in VCVio) and `Reduction.ofChain`
(in `Interaction/Reduction.lean`), but uses `Oracle.Spec` throughout:

- Continuation depends on `PublicTranscript` (not full `Transcript`).
- Uses `Prover.compAux` / `Verifier.compAux` / `Counterpart.liftAcc` from
  `Oracle/Composition.lean` as the binary step.
- Per-round steps may produce the next state for the remaining chain.
- Final output types are computed from the full `PublicTranscript` via
  `Chain.outputFamily`.

## Three composition mechanisms

| Mechanism | State? | Transcript-dependent? | Use when |
|---|---|---|---|
| `Oracle.Spec.append` + `Reduction.comp` | No | Yes | Binary composition |
| `Oracle.Spec.Chain.Prover.comp` | Yes | Yes | N-ary prover composition |
| `Oracle.Spec.Chain.Verifier.comp` | Yes | Yes | N-ary verifier composition |
-/

open OracleComp OracleSpec

namespace Interaction.Oracle

namespace Spec

/-! ## Chain type -/

/-- A self-contained recipe for an `n`-round oracle protocol. At each level,
carries the current round's `Oracle.Spec`, `RoleDeco`, `OracleDeco`, and a
`PublicTranscript`-indexed continuation to the remaining rounds. -/
def Chain : Nat → Type 1
  | 0 => PUnit
  | n + 1 => (spec : Oracle.Spec) × (_ : RoleDeco spec) ×
             (_ : OracleDeco spec) × (PublicTranscript spec → Chain n)

namespace Chain

/-! ## Flattening -/

/-- Flatten a chain into a concrete `Oracle.Spec` via iterated `append`. -/
def toSpec : (n : Nat) → Chain n → Oracle.Spec
  | 0, _ => .done
  | n + 1, ⟨spec, _, _, cont⟩ => spec.append (fun pt => toSpec n (cont pt))

/-- Flatten the role decorations along a chain. -/
def toRoles : (n : Nat) → (c : Chain n) → RoleDeco (toSpec n c)
  | 0, _ => ⟨⟩
  | n + 1, ⟨spec, roles, _, cont⟩ =>
      RoleDeco.append spec (fun pt => toSpec n (cont pt))
        roles (fun pt => toRoles n (cont pt))

/-- Flatten the oracle decorations along a chain. -/
def toOracleDeco : (n : Nat) → (c : Chain n) → OracleDeco (toSpec n c)
  | 0, _ => ⟨⟩
  | n + 1, ⟨spec, _, od, cont⟩ =>
      OracleDeco.append spec (fun pt => toSpec n (cont pt))
        od (fun pt => toOracleDeco n (cont pt))

@[simp] theorem toSpec_zero (c : Chain 0) : toSpec 0 c = .done := rfl

theorem toSpec_succ {n : Nat} (spec : Oracle.Spec)
    (roles : RoleDeco spec) (od : OracleDeco spec)
    (cont : PublicTranscript spec → Chain n) :
    toSpec (n + 1) ⟨spec, roles, od, cont⟩ =
      spec.append (fun pt => toSpec n (cont pt)) := rfl

/-! ## PublicTranscript operations -/

/-- Split a `PublicTranscript` of a flattened `(n+1)`-round chain into the first
round's public transcript and the remainder. -/
def splitPublicTranscript (n : Nat) (c : Chain (n + 1)) :
    PublicTranscript (toSpec (n + 1) c) →
    (pt₁ : PublicTranscript c.1) × PublicTranscript (toSpec n (c.2.2.2 pt₁)) :=
  PublicTranscript.split c.1 (fun pt => toSpec n (c.2.2.2 pt))

/-- Combine a first-round public transcript with a remainder. -/
def appendPublicTranscript (n : Nat) (c : Chain (n + 1))
    (pt₁ : PublicTranscript c.1) (pt₂ : PublicTranscript (toSpec n (c.2.2.2 pt₁))) :
    PublicTranscript (toSpec (n + 1) c) :=
  PublicTranscript.append c.1 (fun pt => toSpec n (c.2.2.2 pt)) pt₁ pt₂

@[simp]
theorem splitPublicTranscript_appendPublicTranscript (n : Nat) (c : Chain (n + 1))
    (pt₁ : PublicTranscript c.1) (pt₂ : PublicTranscript (toSpec n (c.2.2.2 pt₁))) :
    splitPublicTranscript n c (appendPublicTranscript n c pt₁ pt₂) = ⟨pt₁, pt₂⟩ :=
  PublicTranscript.split_append _ _ _ _

/-! ## Output family -/

/-- Lift a family on remaining chains to a family on `PublicTranscript` of the
flattened `Oracle.Spec`. At `Chain 0`, returns `Family ⟨⟩`. At `Chain (n + 1)`,
splits the flattened public transcript into the current round and remainder,
then recurses on the selected continuation. -/
def outputFamily
    (Family : {n : Nat} → Chain n → Type) :
    (n : Nat) → (c : Chain n) → PublicTranscript (toSpec n c) → Type
  | 0, c, _ => Family c
  | n + 1, ⟨spec, _, _, cont⟩, pt =>
      let split := PublicTranscript.split spec (fun pt₁ => toSpec n (cont pt₁)) pt
      outputFamily Family n (cont split.1) split.2

/-! ## Prover composition -/

namespace Prover

/-- Compose per-round prover strategies into a full strategy over the flattened
chain.

`State rem` is the private state available before running `rem`. A round step
consumes `State rem` and returns a strategy for the current round whose output
is the state for the public-transcript-selected remaining chain. After all
rounds, the strategy output is `outputFamily State`, i.e. the state associated
with the terminal chain selected by the full public transcript.

The monad is arbitrary; use `StateT σ m` when state should live in the party
action monad rather than in the round output. -/
def comp
    {m : Type → Type} [Monad m]
    (State : {k : Nat} → Chain k → Type)
    (step : {k : Nat} → (rem : Chain (k + 1)) → State rem →
      m
        (Interaction.Spec.Strategy.withRoles m
          rem.1.toInteractionSpec (rem.1.toSpecRoles rem.2.1)
          (fun tr => State (rem.2.2.2 (rem.1.projectPublic tr))))) :
    (n : Nat) → (c : Chain n) → State c →
    m
      (Interaction.Spec.Strategy.withRoles m
        (toSpec n c).toInteractionSpec
        ((toSpec n c).toSpecRoles (toRoles n c))
        (fun tr => outputFamily State n c ((toSpec n c).projectPublic tr)))
  | 0, _, state => pure state
  | n + 1, ⟨spec, roles, od, cont⟩, state => do
      let strat ← step ⟨spec, roles, od, cont⟩ state
      Prover.compAux spec (fun pt => toSpec n (cont pt))
        roles (fun pt => toRoles n (cont pt))
        (Mid := fun tr₁ => State (cont (spec.projectPublic tr₁)))
        (OutType := fun pt₁ pt₂ => outputFamily State n (cont pt₁) pt₂)
        strat
        (fun tr₁ state' => comp State step n (cont (spec.projectPublic tr₁)) state')

end Prover

/-! ## Verifier composition -/

namespace Verifier

/-- Compose per-round verifier counterparts into a full counterpart over the
flattened chain. `State` has the same meaning as in `Prover.comp`: a round
counterpart consumes the current state and returns the state for the remaining
chain selected by that round's public transcript.

The step function is universally quantified over `accSpec` because
`Verifier.compAux` accumulates oracle access through `.oracle` nodes. -/
def comp
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (State : {k : Nat} → Chain k → Type)
    (step : {k : Nat} → (rem : Chain (k + 1)) → State rem →
      Interaction.Spec.Counterpart.withMonads
        rem.1.toInteractionSpec (rem.1.toSpecRoles rem.2.1)
        (rem.1.toMonadDecoration oSpec OStmtIn rem.2.1 rem.2.2.1 []ₒ)
        (fun tr => State (rem.2.2.2 (rem.1.projectPublic tr)))) :
    (n : Nat) → (c : Chain n) → State c →
    Interaction.Spec.Counterpart.withMonads
      (toSpec n c).toInteractionSpec
      ((toSpec n c).toSpecRoles (toRoles n c))
      ((toSpec n c).toMonadDecoration oSpec OStmtIn (toRoles n c) (toOracleDeco n c) []ₒ)
      (fun tr => outputFamily State n c ((toSpec n c).projectPublic tr))
  | 0, _, state => state
  | n + 1, ⟨spec, roles, od, cont⟩, state =>
      Verifier.compAux (OStmtIn := OStmtIn)
        spec (fun pt => toSpec n (cont pt))
        roles (fun pt => toRoles n (cont pt))
        od (fun pt => toOracleDeco n (cont pt))
        []ₒ
        (OutType := fun pt₁ pt₂ => outputFamily State n (cont pt₁) pt₂)
        (step ⟨spec, roles, od, cont⟩ state)
        (fun accSpec' tr₁ state' =>
          let pt₁ := spec.projectPublic tr₁
          Counterpart.liftAcc
            (toSpec n (cont pt₁)) (toRoles n (cont pt₁)) (toOracleDeco n (cont pt₁))
            []ₒ accSpec' (fun q => q.elim)
            (comp State step n (cont pt₁) state'))

end Verifier

end Chain

end Spec

/-! ## Reduction.ofChain -/

/-- Compose per-round prover and verifier steps into a full `Oracle.Reduction`
over an `n`-round `Chain`. No state flows between rounds: per-round steps
produce `PUnit`. Final output types are computed from the full
`PublicTranscript` via user-provided result functions. -/
def Reduction.ofChain
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {WitnessIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {n : Nat}
    {c : SharedIn → Spec.Chain n}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Spec.Chain.toSpec n (c shared)) → Type}
    {ιₛₒ : (shared : SharedIn) →
      Spec.PublicTranscript (Spec.Chain.toSpec n (c shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) →
        (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
          ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Spec.Chain.toSpec n (c shared)) → Type}
    (proverRound : (shared : SharedIn) → WitnessIn shared →
      {k : Nat} → (rem : Spec.Chain (k + 1)) →
        OracleComp oSpec
          (Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
            rem.1.toInteractionSpec (rem.1.toSpecRoles rem.2.1)
            (fun _ => PUnit)))
    (verifierRound : (shared : SharedIn) →
      {k : Nat} → (rem : Spec.Chain (k + 1)) →
        Interaction.Spec.Counterpart.withMonads
          rem.1.toInteractionSpec (rem.1.toSpecRoles rem.2.1)
          (rem.1.toMonadDecoration oSpec (OStatementIn shared) rem.2.1 rem.2.2.1 []ₒ)
          (fun _ => PUnit))
    (stmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        StatementOut shared pt)
    (oStmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        ∀ i, OStatementOut shared pt i)
    (witResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        WitnessOut shared pt)
    (simulate : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        QueryImpl [OStatementOut shared pt]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Spec.Chain.toSpec n (c shared)).toOracleSpec
                (Spec.Chain.toOracleDeco n (c shared)) pt))) :
    Reduction oSpec SharedIn
      (fun shared => Spec.Chain.toSpec n (c shared))
      (fun shared => Spec.Chain.toRoles n (c shared))
      (fun shared => Spec.Chain.toOracleDeco n (c shared))
      (fun _ => PUnit) OStatementIn WitnessIn
      StatementOut OStatementOut WitnessOut where
  prover shared _sWithOracles w := do
    let strat ← Spec.Chain.Prover.comp (fun {_} _ => PUnit)
      (fun rem _ => proverRound shared w rem) n (c shared) PUnit.unit
    pure <| Interaction.Spec.Strategy.mapOutputWithRoles
      (fun tr _ =>
        let pt := (Spec.Chain.toSpec n (c shared)).projectPublic tr
        (⟨⟨stmtResult shared pt, oStmtResult shared pt⟩, witResult shared pt⟩ :
          HonestProverOutput
            (StatementWithOracles
              (fun _ => StatementOut shared pt)
              (fun _ => OStatementOut shared pt) shared)
            (WitnessOut shared pt)))
      strat
  verifier := {
    toFun := fun shared _stmtIn =>
      Interaction.Spec.Counterpart.withMonads.mapOutput
        (Spec.Chain.toSpec n (c shared)).toInteractionSpec
        ((Spec.Chain.toSpec n (c shared)).toSpecRoles (Spec.Chain.toRoles n (c shared)))
        ((Spec.Chain.toSpec n (c shared)).toMonadDecoration oSpec (OStatementIn shared)
          (Spec.Chain.toRoles n (c shared)) (Spec.Chain.toOracleDeco n (c shared)) []ₒ)
        (fun tr _ =>
          stmtResult shared ((Spec.Chain.toSpec n (c shared)).projectPublic tr))
        (Spec.Chain.Verifier.comp (fun {_} _ => PUnit)
          (fun rem _ => verifierRound shared rem) n (c shared) PUnit.unit)
    simulate := simulate
  }

end Interaction.Oracle
