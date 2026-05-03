/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec
import VCVio.Interaction.Basic.Chain
import VCVio.Interaction.TwoParty.Compose

/-!
# Provers, Verifiers, and Reductions

Interactive protocol participants and their composition, built on `Spec` with
a `RoleDecoration`. This module replaces the old `OracleReduction/Basic.lean`
flat-list model with one natively built on the W-type interaction tree.

## Type architecture

The canonical interaction object is indexed by:

- `SharedIn` — ambient input fixing the protocol context
- `StatementIn : SharedIn → Type` — carried local statement/state interpreted inside
  the protocol fixed by `SharedIn`
- `WitnessIn : SharedIn → Type` — carried prover-local witness/state
- `Context : SharedIn → Spec` — protocol spec depends on the ambient input
- `Roles : (i : SharedIn) → RoleDecoration (Context i)` — roles per input
- `StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type`
- `WitnessOut : (i : SharedIn) → Spec.Transcript (Context i) → Type`

This unifies both top-level protocols and suffix/continuation protocols.
Ordinary top-level protocols are the special case `StatementIn := fun _ => PUnit`;
mid-protocol suffixes use `SharedIn` for ambient setup or prefix transcript data
and `StatementIn` for the carried local state inside that fixed protocol.

SharedIn and output are represented as:
- **SharedIn**: `Σ i, StatementIn i × WitnessIn i`
- **Honest prover output**: `HonestProverOutput (StatementOut i tr) (WitnessOut i tr)`

## Participants

- **Prover**: monadic setup producing a role-dependent `Strategy` whose output is
  `HonestProverOutput StatementOut WitnessOut`.
- **Verifier**: an `SharedIn`-indexed, `StatementIn`-parameterized `Counterpart`
  with `StatementOut` at `.done`. No `OptionT` — acceptance semantics (if
  needed) are chosen by the caller through the `StatementOut` type
  (e.g., `StatementOut = fun _ _ => Option Bool`).
- **PublicCoinVerifier**: a stronger verifier surface whose receiver nodes are
  replayable public-coin continuations (`Spec.PublicCoinCounterpart`), used by
  the interaction-native Fiat-Shamir transform.
- **Reduction**: pairs a prover with a verifier for the same protocol spec.
- **PublicCoinReduction**: pairs a prover with a public-coin verifier; forgetting
  the extra verifier structure recovers an ordinary `Reduction`.

Both `Prover` and `Verifier` are `abbrev`s (transparent type aliases) for
the underlying function types.

## Composition

Sequential composition is phrased directly at the canonical `Reduction` shape:
the second protocol is indexed by `(input, tr₁)`, where `tr₁` is the realized
prefix transcript. This subsumes the old continuation surface without requiring
a separate foundational object.

## Running a reduction

`Reduction.execute` runs the prover's strategy against the verifier (via
`Strategy.runWithRoles`), returning the transcript plus both outputs.

See `Security.lean` for completeness, soundness, and knowledge soundness
definitions built on this execution model.
-/

universe u v w

namespace Interaction

/-! ## Monad decorations -/

namespace Spec
namespace MonadDecoration

/-- Constant monad decoration: every node in the interaction tree uses the same
bundled monad. This recovers the ordinary single-monad strategy layer as a
special case of `Strategy.withRolesAndMonads`. -/
def constant (bm : BundledMonad.{u, u}) :
    (spec : Spec.{u}) → MonadDecoration.{u, u, u} spec
  | .done => PUnit.unit
  | .node _ rest => ⟨bm, fun x => constant bm (rest x)⟩

/-- Nodewise monad homomorphism between two `MonadDecoration`s on the same
specification. This is the generic lifting datum needed to retarget
`Counterpart.withMonads` from one ambient effect layer to another. -/
def Hom :
    (spec : Spec.{u}) → MonadDecoration.{u, u, u} spec →
      MonadDecoration.{u, u, u} spec → Type (u + 1)
  | .done, _, _ => PUnit
  | .node X rest, ⟨m₁, md₁⟩, ⟨m₂, md₂⟩ =>
      (∀ {α : Type u}, m₁.M α → m₂.M α) ×
        ((x : X) → Hom (rest x) (md₁ x) (md₂ x))

end MonadDecoration

namespace Strategy
namespace withRolesAndMonads

/-- Map the transcript-indexed output of a monadic strategy. -/
def mapOutput
    (spec : Spec.{u}) (roles : RoleDecoration spec) (md : Spec.MonadDecoration spec)
    {Output₁ Output₂ : Spec.Transcript spec → Type u}
    (f : ∀ tr, Output₁ tr → Output₂ tr) :
    Strategy.withRolesAndMonads spec roles md Output₁ →
    Strategy.withRolesAndMonads spec roles md Output₂ :=
  match spec, roles, md with
  | .done, _, _ => fun strat => f ⟨⟩ strat
  | .node _ rest, ⟨.sender, rRest⟩, ⟨_, mdRest⟩ =>
      fun strat =>
        Functor.map
          (fun msgAndRest =>
            ⟨msgAndRest.1,
              mapOutput (rest msgAndRest.1) (rRest msgAndRest.1) (mdRest msgAndRest.1)
                (fun tr => f ⟨msgAndRest.1, tr⟩) msgAndRest.2⟩)
          strat
  | .node _ rest, ⟨.receiver, rRest⟩, ⟨_, mdRest⟩ =>
      fun strat x =>
        Functor.map
          (mapOutput (rest x) (rRest x) (mdRest x) (fun tr => f ⟨x, tr⟩))
          (strat x)

/-- Retarget a monadic strategy along a nodewise monad homomorphism.

This is the prover-side analog of `Counterpart.withMonads.mapDecoration`.
It keeps the protocol tree and output family fixed while changing the ambient
effect layer attached to each node. -/
def mapDecoration
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {md₁ md₂ : Spec.MonadDecoration spec}
    (hom : Spec.MonadDecoration.Hom spec md₁ md₂)
    {Output : Spec.Transcript spec → Type u} :
    Strategy.withRolesAndMonads spec roles md₁ Output →
    Strategy.withRolesAndMonads spec roles md₂ Output :=
  match spec, roles, md₁, md₂, hom with
  | .done, _, _, _, _ => fun strat => strat
  | .node _ rest, ⟨.sender, rRest⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨lift, homRest⟩ =>
      fun strat =>
        lift <| Functor.map
          (fun msgAndRest =>
            ⟨msgAndRest.1,
              mapDecoration (rest msgAndRest.1) (rRest msgAndRest.1)
                (homRest msgAndRest.1) msgAndRest.2⟩)
          strat
  | .node _ rest, ⟨.receiver, rRest⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨lift, homRest⟩ =>
      fun strat x =>
        lift <| Functor.map
          (mapDecoration (rest x) (rRest x) (homRest x)) (strat x)

/-- View a strategy over a constant monad decoration as an ordinary
single-monad role strategy. -/
def toWithRolesConstant {m : Type u → Type u} [Monad m]
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {Output : Spec.Transcript spec → Type u} :
    Strategy.withRolesAndMonads spec roles
      (Spec.MonadDecoration.constant ⟨m, inferInstance⟩ spec) Output →
    Strategy.withRoles m spec roles Output :=
  match spec, roles with
  | .done, _ => fun strat => strat
  | .node _ rest, ⟨.sender, rRest⟩ =>
      fun strat =>
        Functor.map
          (fun msgAndRest =>
            ⟨msgAndRest.1,
              toWithRolesConstant (rest msgAndRest.1) (rRest msgAndRest.1) msgAndRest.2⟩)
          strat
  | .node _ rest, ⟨.receiver, rRest⟩ =>
      fun strat x =>
        Functor.map (toWithRolesConstant (rest x) (rRest x)) (strat x)

/-- View an ordinary single-monad role strategy as a strategy over a constant
monad decoration. -/
def ofWithRolesConstant {m : Type u → Type u} [Monad m]
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {Output : Spec.Transcript spec → Type u} :
    Strategy.withRoles m spec roles Output →
    Strategy.withRolesAndMonads spec roles
      (Spec.MonadDecoration.constant ⟨m, inferInstance⟩ spec) Output :=
  match spec, roles with
  | .done, _ => fun strat => strat
  | .node _ rest, ⟨.sender, rRest⟩ =>
      fun strat =>
        Functor.map
          (fun msgAndRest =>
            ⟨msgAndRest.1,
              ofWithRolesConstant (rest msgAndRest.1) (rRest msgAndRest.1) msgAndRest.2⟩)
          strat
  | .node _ rest, ⟨.receiver, rRest⟩ =>
      fun strat x =>
        Functor.map (ofWithRolesConstant (rest x) (rRest x)) (strat x)

end withRolesAndMonads
end Strategy

namespace Counterpart
namespace withMonads

/-- Retarget a monadic counterpart along a nodewise monad homomorphism.

This is independent of oracle semantics: callers provide the per-node lifts,
and the counterpart tree is traversed structurally. Oracle-specific rewiring
can then be expressed by constructing an appropriate homomorphism, while other
ambient effect layers can use the same traversal. -/
def mapDecoration
    (spec : Spec.{u}) (roles : RoleDecoration spec)
    {md₁ md₂ : Spec.MonadDecoration spec}
    (hom : Spec.MonadDecoration.Hom spec md₁ md₂)
    {Output : Spec.Transcript spec → Type u} :
    Counterpart.withMonads spec roles md₁ Output →
    Counterpart.withMonads spec roles md₂ Output :=
  match spec, roles, md₁, md₂, hom with
  | .done, _, _, _, _ => fun cpt => cpt
  | .node _ rest, ⟨.sender, rRest⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨lift, homRest⟩ =>
      fun cpt x =>
        lift <| Functor.map
          (mapDecoration (rest x) (rRest x) (homRest x)) (cpt x)
  | .node _ rest, ⟨.receiver, rRest⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨lift, homRest⟩ =>
      fun cpt =>
        lift <| Functor.map
          (fun msgAndRest =>
            ⟨msgAndRest.1,
              mapDecoration (rest msgAndRest.1) (rRest msgAndRest.1)
                (homRest msgAndRest.1) msgAndRest.2⟩)
          cpt

end withMonads
end Counterpart
end Spec

/-! ## Protocol participants -/

/-- Output produced by an honest prover: the next statement together with the
next witness to be forwarded by composition. -/
abbrev HonestProverOutput (StatementOut : Type u) (WitnessOut : Type v) :=
  StatementOut × WitnessOut

namespace HonestProverOutput

/-- Statement component of an honest prover output. -/
abbrev stmt {StatementOut : Type u} {WitnessOut : Type v}
    (out : HonestProverOutput StatementOut WitnessOut) : StatementOut :=
  out.1

/-- Witness component of an honest prover output. -/
abbrev wit {StatementOut : Type u} {WitnessOut : Type v}
    (out : HonestProverOutput StatementOut WitnessOut) : WitnessOut :=
  out.2

end HonestProverOutput

/-- A prover: given ambient input `i`, local statement `stmt`, and local witness
`wit`, performs monadic setup and produces a role-dependent strategy whose
output is `HonestProverOutput (StatementOut i tr) (WitnessOut i tr)`. -/
abbrev Prover (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn WitnessIn : SharedIn → Type w)
    (StatementOut WitnessOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) :=
  (i : SharedIn) → StatementIn i → WitnessIn i →
    m (Spec.Strategy.withRoles m (Context i) (Roles i)
      (fun tr => HonestProverOutput (StatementOut i tr) (WitnessOut i tr)))

/-- A verifier: given ambient input `i` and local statement `stmt`, provides a
`Counterpart` with `StatementOut i tr` at `.done`. No `OptionT` wrapping — the
caller chooses whether `StatementOut` includes `Option` for accept/reject
semantics. -/
abbrev Verifier (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn : SharedIn → Type w)
    (StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) :=
  (i : SharedIn) → StatementIn i →
    Spec.Counterpart m (Context i) (Roles i) (fun tr => StatementOut i tr)

/-- A verifier whose receiver nodes are public-coin in the strong replayable
sense captured by `Spec.PublicCoinCounterpart`.

An ordinary `Verifier` is enough to execute a protocol, but not enough to
replay a prescribed receiver transcript: at a verifier node, the continuation
is hidden inside an opaque monadic sample. `PublicCoinVerifier` keeps the same
overall interface while strengthening receiver nodes so they expose both a
challenge sampler and a challenge-indexed continuation family. Forgetting this
extra structure recovers an ordinary `Verifier`. -/
abbrev PublicCoinVerifier (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn : SharedIn → Type w)
    (StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) :=
  (i : SharedIn) → StatementIn i →
    Spec.PublicCoinCounterpart m (Context i) (Roles i)
      (fun tr => StatementOut i tr)

namespace PublicCoinVerifier

/-- Forget that a verifier is public-coin and view it as an ordinary verifier. -/
def toVerifier {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn : SharedIn → Type w}
    {StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
    (verifier : PublicCoinVerifier m SharedIn Context Roles StatementIn StatementOut) :
    Verifier m SharedIn Context Roles StatementIn StatementOut :=
  fun i stmt => (verifier i stmt).toCounterpart

/-- Replay a full transcript through a public-coin verifier. -/
def replay {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn : SharedIn → Type w}
    {StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
    (verifier : PublicCoinVerifier m SharedIn Context Roles StatementIn StatementOut)
    (i : SharedIn) (stmt : StatementIn i) (tr : Spec.Transcript (Context i)) :
    m (StatementOut i tr) :=
  Spec.PublicCoinCounterpart.replay (verifier i stmt) tr

end PublicCoinVerifier

/-- A reduction pairs a prover with a verifier for the same protocol. -/
structure Reduction (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn WitnessIn : SharedIn → Type w)
    (StatementOut WitnessOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) where
  prover : Prover m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut
  verifier : Verifier m SharedIn Context Roles StatementIn StatementOut

/-- A reduction whose verifier is public-coin in the replayable sense of
`PublicCoinVerifier`. The prover is unchanged; only the verifier carries the
extra structure needed by verifier-side Fiat-Shamir. -/
structure PublicCoinReduction (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn WitnessIn : SharedIn → Type w)
    (StatementOut WitnessOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) where
  prover : Prover m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut
  verifier : PublicCoinVerifier m SharedIn Context Roles StatementIn StatementOut

namespace PublicCoinReduction

/-- Forget that a reduction is public-coin and recover the underlying ordinary
interactive reduction. -/
def toReduction {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
    {WitnessOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
    (reduction :
      PublicCoinReduction m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut) :
    Reduction m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut where
  prover := reduction.prover
  verifier := reduction.verifier.toVerifier

end PublicCoinReduction

/-- A proof system is a reduction where the prover does not forward any
witness to the next stage (`WitnessOut = PUnit`). Accept/reject semantics
are not fixed here — they are determined by the choice of `StatementOut`
(e.g., `Bool`, `Option _`) and the security definitions. Its honest prover
output is `HonestProverOutput StatementOut PUnit`. -/
abbrev Proof (m : Type u → Type u)
    (SharedIn : Type v)
    (Context : SharedIn → Spec)
    (Roles : (i : SharedIn) → RoleDecoration (Context i))
    (StatementIn WitnessIn : SharedIn → Type w)
    (StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) :=
  Reduction m SharedIn Context Roles StatementIn WitnessIn StatementOut (fun _ _ => PUnit)

/-! ## Execution -/

/-- Execute a reduction: run the prover's strategy against the verifier's
counterpart (via `Strategy.runWithRoles`). Returns the transcript, the
 prover's output (`HonestProverOutput StatementOut WitnessOut`), and the verifier's output
 (`StatementOut`). -/
def Reduction.execute {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
    (reduction : Reduction m SharedIn Context Roles StatementIn WitnessIn StatementOut WitnessOut)
    (i : SharedIn) (stmt : StatementIn i) (wit : WitnessIn i) :
    m ((tr : Spec.Transcript (Context i)) ×
       HonestProverOutput (StatementOut i tr) (WitnessOut i tr) ×
         StatementOut i tr) := do
  let strategy ← reduction.prover i stmt wit
  Spec.Strategy.runWithRoles (Context i) (Roles i) strategy (reduction.verifier i stmt)

/-- Run a prover strategy against a verifier. Convenience wrapper around
`Spec.Strategy.runWithRoles` that applies the input-indexed verifier. -/
def Verifier.run {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (i : SharedIn) → RoleDecoration (Context i)}
    {StatementIn : SharedIn → Type w}
    {StatementOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}
    (v : Verifier m SharedIn Context Roles StatementIn StatementOut)
    (i : SharedIn)
    (stmt : StatementIn i)
    {OutputP : Spec.Transcript (Context i) → Type u}
    (prover : Spec.Strategy.withRoles m (Context i) (Roles i) OutputP) :
    m ((tr : Spec.Transcript (Context i)) × OutputP tr × StatementOut i tr) :=
  Spec.Strategy.runWithRoles (Context i) (Roles i) prover (v i stmt)

/-! ## Sequential composition -/

/-- Compose a reduction with a transcript-indexed continuation reduction.
The first reduction runs over `ctx₁`, producing intermediate outputs `StmtMid` and
`WitMid`. These feed into `reduction2`, whose protocol `ctx₂` may depend on the
first transcript. The composed output types are factored two-argument families,
lifted through `Transcript.liftAppend`. -/
def Reduction.comp {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type w}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (i : SharedIn) → RoleDecoration (ctx₁ i)}
    {StmtMid WitMid : (i : SharedIn) → Spec.Transcript (ctx₁ i) → Type u}
    {ctx₂ : (i : SharedIn) → Spec.Transcript (ctx₁ i) → Spec}
    {roles₂ : (i : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ i)) →
      RoleDecoration (ctx₂ i tr₁)}
    {StmtOut WitOut : (i : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ i)) →
      Spec.Transcript (ctx₂ i tr₁) → Type u}
    (reduction1 : Reduction m SharedIn ctx₁ roles₁ StatementIn WitnessIn StmtMid WitMid)
    (reduction2 : Reduction m
      ((i : SharedIn) × StatementIn i × Spec.Transcript (ctx₁ i))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared => WitMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2.2 tr₂)) :
    Reduction m SharedIn
      (fun i => (ctx₁ i).append (ctx₂ i))
      (fun i => (roles₁ i).append (roles₂ i))
      StatementIn
      WitnessIn
      (fun i => Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i))
      (fun i => Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (WitOut i)) where
  prover i stmt w := do
    let strat₁ ← reduction1.prover i stmt w
    let strat ← Spec.Strategy.compWithRoles strat₁ (fun tr₁ midOut =>
      reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr out =>
        Spec.Transcript.liftAppendProd (ctx₁ i) (ctx₂ i) (StmtOut i) (WitOut i) tr out)
      strat
  verifier i stmt :=
    Spec.Counterpart.append (reduction1.verifier i stmt) (fun tr₁ sMid =>
      reduction2.verifier ⟨i, stmt, tr₁⟩ sMid)

/-- Executing a sequentially composed reduction factors into first executing the
prefix reduction and then the suffix interaction induced by its outputs. -/
theorem Reduction.execute_comp
    {m : Type u → Type u} [Monad m] [Spec.LawfulCommMonad m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type w}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (i : SharedIn) → RoleDecoration (ctx₁ i)}
    {StmtMid WitMid : (i : SharedIn) → Spec.Transcript (ctx₁ i) → Type u}
    {ctx₂ : (i : SharedIn) → Spec.Transcript (ctx₁ i) → Spec}
    {roles₂ : (i : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ i)) →
      RoleDecoration (ctx₂ i tr₁)}
    {StmtOut WitOut : (i : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ i)) →
      Spec.Transcript (ctx₂ i tr₁) → Type u}
    (reduction1 : Reduction m SharedIn ctx₁ roles₁ StatementIn WitnessIn StmtMid WitMid)
    (reduction2 : Reduction m
      ((i : SharedIn) × StatementIn i × Spec.Transcript (ctx₁ i))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared => WitMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2.2 tr₂))
    (i : SharedIn) (stmt : StatementIn i) (w : WitnessIn i) :
    (Reduction.comp reduction1 reduction2).execute i stmt w =
      (do
        let ⟨tr₁, midOut, sMid⟩ ← reduction1.execute i stmt w
        let strat₂ ← reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit
        let ⟨tr₂, out, sOut⟩ ←
          Spec.Strategy.runWithRoles (ctx₂ i tr₁) (roles₂ i tr₁) strat₂
            (reduction2.verifier ⟨i, stmt, tr₁⟩ sMid)
        pure ⟨Spec.Transcript.append (ctx₁ i) (ctx₂ i) tr₁ tr₂,
          ⟨Spec.Transcript.packAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr₁ tr₂ out.stmt,
            Spec.Transcript.packAppend (ctx₁ i) (ctx₂ i) (WitOut i) tr₁ tr₂ out.wit⟩,
          Spec.Transcript.packAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr₁ tr₂ sOut⟩) := by
  simp only [execute, comp, bind_assoc, pure_bind]
  refine congrArg (fun k => reduction1.prover i stmt w >>= k) ?_
  funext strat₁
  let mapOut :
      (tr : Spec.Transcript ((ctx₁ i).append (ctx₂ i))) →
      Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i)
        (fun tr₁ tr₂ => HonestProverOutput (StmtOut i tr₁ tr₂) (WitOut i tr₁ tr₂)) tr →
      HonestProverOutput
        (Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr)
        (Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (WitOut i) tr) :=
    fun tr out =>
      Spec.Transcript.liftAppendProd (ctx₁ i) (ctx₂ i) (StmtOut i) (WitOut i) tr out
  let mapTriple :
      ((tr : Spec.Transcript ((ctx₁ i).append (ctx₂ i))) ×
        Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i)
          (fun tr₁ tr₂ => HonestProverOutput (StmtOut i tr₁ tr₂) (WitOut i tr₁ tr₂)) tr ×
        Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr) →
      ((tr : Spec.Transcript ((ctx₁ i).append (ctx₂ i))) ×
        HonestProverOutput
          (Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr)
          (Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (WitOut i) tr) ×
        Spec.Transcript.liftAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr) :=
    fun z => ⟨z.1, mapOut z.1 z.2.1, z.2.2⟩
  have hmap :
      (do
        let strat ← Spec.Strategy.compWithRoles strat₁
          (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
        Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
          (Spec.Strategy.mapOutputWithRoles mapOut strat)
          (Spec.Counterpart.append (reduction1.verifier i stmt)
            (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) =
        mapTriple <$>
          (do
            let strat ← Spec.Strategy.compWithRoles strat₁
              (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
            Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
              strat
                (Spec.Counterpart.append (reduction1.verifier i stmt)
                  (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) := by
    have hraw :
        (do
          let strat ← Spec.Strategy.compWithRoles strat₁
            (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
          Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
            (Spec.Strategy.mapOutputWithRoles mapOut strat)
            (Spec.Counterpart.append (reduction1.verifier i stmt)
              (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) =
          (do
            let strat ← Spec.Strategy.compWithRoles strat₁
              (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
            mapTriple <$>
              Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
                strat
                (Spec.Counterpart.append (reduction1.verifier i stmt)
                  (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) := by
      refine congrArg
        (fun k =>
          Spec.Strategy.compWithRoles strat₁
            (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit) >>= k) ?_
      funext strat
      simpa [mapTriple, mapOut, Spec.Counterpart.mapOutput_id] using
        (Spec.Strategy.runWithRoles_mapOutputWithRoles_mapOutput
          (fP := mapOut) (fC := fun _ x => x) strat
          (Spec.Counterpart.append (reduction1.verifier i stmt)
            (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid)))
    calc
      (do
        let strat ← Spec.Strategy.compWithRoles strat₁
          (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
        Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
          (Spec.Strategy.mapOutputWithRoles mapOut strat)
          (Spec.Counterpart.append (reduction1.verifier i stmt)
            (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) =
          (do
            let strat ← Spec.Strategy.compWithRoles strat₁
              (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
            mapTriple <$>
              Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
                strat
                (Spec.Counterpart.append (reduction1.verifier i stmt)
                  (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) := hraw
      _ = mapTriple <$>
            (do
              let strat ← Spec.Strategy.compWithRoles strat₁
                (fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
              Spec.Strategy.runWithRoles ((ctx₁ i).append (ctx₂ i)) ((roles₁ i).append (roles₂ i))
                strat
                (Spec.Counterpart.append (reduction1.verifier i stmt)
                  (fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))) := by
        simp
  rw [hmap]
  simpa [mapTriple, mapOut, bind_assoc] using
    congrArg (fun mx => mapTriple <$> mx)
      (Spec.Strategy.runWithRoles_compWithRoles_append
        (strat₁ := strat₁)
        (f := fun tr₁ midOut => reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit)
        (cpt₁ := reduction1.verifier i stmt)
        (cpt₂ := fun tr₁ sMid => reduction2.verifier ⟨i, stmt, tr₁⟩ sMid))

/-- Compose per-stage prover and verifier step functions into a reduction over
a chained protocol `Spec.stateChain Stage spec advance n`.

The prover and verifier each carry evolving state through the state chain:
- `ProverState i st` is the prover's state at stage `i` with state chain state `st`.
  Initialized from the witness via `proverInit`, then transformed at each stage
  by `proverStep`. The terminal prover state becomes `WitnessOut`.
- `VerifierState i st` is the verifier's state at stage `i`.
  Initialized from the statement via `verifierInit`, then transformed by
  `verifierStep`. The terminal verifier state becomes `StatementOut`.

Both output types are computed as `Transcript.stateChainFamily` of the respective
state families. -/
def Reduction.stateChainComp {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {StatementIn WitnessIn : SharedIn → Type w}
    {Stage : Nat → Type u}
    {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    {roles : (i : Nat) → (s : Stage i) → RoleDecoration (spec i s)}
    {ProverState VerifierState : (i : Nat) → Stage i → Type u}
    (n : Nat)
    (initStage : SharedIn → Stage 0)
    (proverInit : (i : SharedIn) → StatementIn i → WitnessIn i →
      m (ProverState 0 (initStage i)))
    (proverStep : (j : Nat) → (st : Stage j) → ProverState j st →
      m (Spec.Strategy.withRoles m (spec j st) (roles j st)
        (fun tr => ProverState (j + 1) (advance j st tr))))
    (stmtResult : (i : SharedIn) → StatementIn i →
      (tr : Spec.Transcript (Spec.stateChain Stage spec advance n 0 (initStage i))) →
      Spec.Transcript.stateChainFamily VerifierState n 0 (initStage i) tr)
    (verifierInit : (i : SharedIn) → StatementIn i → VerifierState 0 (initStage i))
    (verifierStep : (j : Nat) → (st : Stage j) → VerifierState j st →
      Spec.Counterpart m (spec j st) (roles j st)
        (fun tr => VerifierState (j + 1) (advance j st tr))) :
    Reduction m SharedIn
      (fun i => Spec.stateChain Stage spec advance n 0 (initStage i))
      (fun i => Spec.Decoration.stateChain roles n 0 (initStage i))
      StatementIn
      WitnessIn
      (fun i => Spec.Transcript.stateChainFamily VerifierState n 0 (initStage i))
      (fun i => Spec.Transcript.stateChainFamily ProverState n 0 (initStage i)) where
  prover i stmt w := do
    let a ← proverInit i stmt w
    let strat ← Spec.Strategy.stateChainCompWithRoles proverStep n 0 (initStage i) a
    pure <| Spec.Strategy.mapOutputWithRoles (fun tr pOut => ⟨stmtResult i stmt tr, pOut⟩) strat
  verifier i stmt :=
    Spec.Counterpart.stateChainComp verifierStep n 0 (initStage i) (verifierInit i stmt)

/-! ## Chain-based reduction composition

Reduction composition over an `n`-round protocol described by `Spec.Chain`,
where participant state is a family indexed by the remaining chain. The
remaining chain still encodes transcript-dependent protocol shape; the state
families carry participant data that is not part of the protocol shape. -/

namespace Spec

/-- Build a `Decoration S` for `Chain.toSpec n c` from per-round decorators.
At each level, the decorator receives the remaining `Chain` and
produces the decoration for the current round's spec. -/
def Decoration.ofChain {S : Type u → Type v}
    (decoAt : {k : Nat} → (rem : Chain.{u} (k + 1)) → Decoration S rem.1) :
    (n : Nat) → (c : Chain.{u} n) → Decoration S (Chain.toSpec n c)
  | 0, _ => ⟨⟩
  | n + 1, ⟨spec, cont⟩ =>
      Decoration.append (decoAt ⟨spec, cont⟩)
        (fun tr => Decoration.ofChain decoAt n (cont tr))

namespace Chain

/-- Build a `RoleDecoration` for the full spec from per-round role
assignments. Specializes `Decoration.ofChain` to `fun _ => Role`. -/
abbrev roles
    (rolesAt : {k : Nat} → (rem : Chain.{u} (k + 1)) → RoleDecoration rem.1) :
    (n : Nat) → (c : Chain.{u} n) → RoleDecoration (Chain.toSpec n c) :=
  Decoration.ofChain rolesAt

end Chain

/-- Compose per-round prover strategies into a full strategy over the
chain. `State rem` is the state available before the remaining chain `rem`;
each round step returns the state for the transcript-selected continuation. -/
def Strategy.ofChain {m : Type u → Type u} [Monad m]
    {rolesAt : {k : Nat} → (rem : Chain.{u} (k + 1)) → RoleDecoration rem.1}
    (State : {k : Nat} → Chain.{u} k → Type u)
    (step : {k : Nat} → (rem : Chain.{u} (k + 1)) → State rem →
      m (Strategy.withRoles m rem.1 (rolesAt rem)
        (fun tr => State (rem.2 tr)))) :
    (n : Nat) → (c : Chain.{u} n) → State c →
    m (Strategy.withRoles m (Chain.toSpec n c)
      (Decoration.ofChain rolesAt n c)
      (fun tr => Chain.outputFamily State n c tr))
  | 0, _, state => pure state
  | n + 1, ⟨spec, cont⟩, state => do
    let strat ← step ⟨spec, cont⟩ state
    @Strategy.compWithRoles m _ spec (fun tr => Chain.toSpec n (cont tr))
      (rolesAt ⟨spec, cont⟩) (fun tr => Decoration.ofChain rolesAt n (cont tr))
      (fun tr => State (cont tr))
      (fun tr₁ tr₂ => Chain.outputFamily State n (cont tr₁) tr₂)
      strat (fun tr state' => Strategy.ofChain (rolesAt := rolesAt) State step n (cont tr) state')

/-- Compose per-round verifier counterparts into a full counterpart over
the chain, threading a caller-chosen state family indexed by the remaining
chain. -/
def Counterpart.ofChain {m : Type u → Type u} [Monad m]
    {rolesAt : {k : Nat} → (rem : Chain.{u} (k + 1)) → RoleDecoration rem.1}
    (State : {k : Nat} → Chain.{u} k → Type u)
    (step : {k : Nat} → (rem : Chain.{u} (k + 1)) → State rem →
      Counterpart m rem.1 (rolesAt rem) (fun tr => State (rem.2 tr))) :
    (n : Nat) → (c : Chain.{u} n) → State c →
    Counterpart m (Chain.toSpec n c)
      (Decoration.ofChain rolesAt n c) (fun tr => Chain.outputFamily State n c tr)
  | 0, _, state => state
  | n + 1, ⟨spec, cont⟩, state =>
    @Counterpart.append m _ spec (fun tr => Chain.toSpec n (cont tr))
      (rolesAt ⟨spec, cont⟩) (fun tr => Decoration.ofChain rolesAt n (cont tr))
      (fun tr => State (cont tr))
      (fun tr₁ tr₂ => Chain.outputFamily State n (cont tr₁) tr₂)
      (step ⟨spec, cont⟩ state)
      (fun tr state' => Counterpart.ofChain (rolesAt := rolesAt) State step n (cont tr) state')

end Spec

/-- Compose per-round prover and verifier steps into a full `Reduction`
over an `n`-round `Chain`, threading separate prover and verifier state
families indexed by the remaining chain. -/
def Reduction.ofChain {m : Type u → Type u} [Monad m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type w}
    {n : Nat}
    {c : SharedIn → Spec.Chain.{u} n}
    {rolesAt : {k : Nat} → (rem : Spec.Chain.{u} (k + 1)) → RoleDecoration rem.1}
    {StatementOut WitnessOut : (i : SharedIn) →
      Spec.Transcript (Spec.Chain.toSpec n (c i)) → Type u}
    (ProverState : (i : SharedIn) → {k : Nat} → Spec.Chain.{u} k → Type u)
    (VerifierState : (i : SharedIn) → {k : Nat} → Spec.Chain.{u} k → Type u)
    (proverInit : (i : SharedIn) → StatementIn i → WitnessIn i → ProverState i (c i))
    (verifierInit : (i : SharedIn) → StatementIn i → VerifierState i (c i))
    (proverRound : (i : SharedIn) →
      {k : Nat} → (rem : Spec.Chain.{u} (k + 1)) → ProverState i rem →
        m (Spec.Strategy.withRoles m rem.1 (rolesAt rem)
          (fun tr => ProverState i (rem.2 tr))))
    (verifierRound : (i : SharedIn) →
      {k : Nat} → (rem : Spec.Chain.{u} (k + 1)) → VerifierState i rem →
        Spec.Counterpart m rem.1 (rolesAt rem) (fun tr => VerifierState i (rem.2 tr)))
    (proverStmtResult : (i : SharedIn) →
      (tr : Spec.Transcript (Spec.Chain.toSpec n (c i))) →
        Spec.Chain.outputFamily (ProverState i) n (c i) tr → StatementOut i tr)
    (verifierStmtResult : (i : SharedIn) →
      (tr : Spec.Transcript (Spec.Chain.toSpec n (c i))) →
        Spec.Chain.outputFamily (VerifierState i) n (c i) tr → StatementOut i tr)
    (witResult : (i : SharedIn) →
      (tr : Spec.Transcript (Spec.Chain.toSpec n (c i))) →
        Spec.Chain.outputFamily (ProverState i) n (c i) tr → WitnessOut i tr) :
    Reduction m SharedIn
      (fun i => Spec.Chain.toSpec n (c i))
      (fun i => Spec.Decoration.ofChain rolesAt n (c i))
      StatementIn
      WitnessIn
      StatementOut WitnessOut where
  prover i stmt w := do
    let strat ← Spec.Strategy.ofChain (rolesAt := rolesAt)
      (ProverState i) (proverRound i) n (c i) (proverInit i stmt w)
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr state => ⟨proverStmtResult i tr state, witResult i tr state⟩) strat
  verifier i stmt :=
    Spec.Counterpart.mapOutput (fun tr state => verifierStmtResult i tr state)
      (Spec.Counterpart.ofChain (rolesAt := rolesAt)
        (VerifierState i) (verifierRound i) n (c i) (verifierInit i stmt))

end Interaction
