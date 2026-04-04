/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Process

/-!
# State-indexed concurrent machines

This file adds a flat state-indexed frontend to the dynamic concurrent process
layer.

The foundational `Concurrent.Process` API is continuation-based: a residual
process state exposes one sequential `Step`, and completing that step yields
the next residual state.

Many users, however, naturally think in terms of enabled transitions over an
explicit state space. This file packages that presentation:

* `Machine` is the minimal state-indexed dynamics:
  * a state type `State`,
  * a type `Enabled σ` of enabled events in each state, and
  * a step function `step`.
* `Machine.toProcess` compiles such a machine into the continuation-based
  `Concurrent.Process` core by turning each enabled event set into a one-node
  sequential interaction step.
* `Machine.Labeled`, `Machine.Ticketed`, and `Machine.System` add the standard
  orthogonal enrichments without bloating the minimal core.

This is the frontend where Veil-style transition-system semantics should land.
-/

universe u v

namespace Interaction
namespace Concurrent

/--
`Machine` is the minimal state-indexed dynamics for a concurrent system.

Fields:
* `State` is the type of residual states;
* `Enabled σ` is the type of currently enabled events in state `σ`;
* `step σ e` is the residual state after performing enabled event `e`.

This record intentionally contains only the dynamics.
Labels, fairness tickets, controller ownership, local views, and safety
predicates are all layered on top separately.
-/
structure Machine where
  State : Type v
  Enabled : State → Type u
  step : (σ : State) → Enabled σ → State

namespace Machine

/-- Stable external event labels for enabled machine events. -/
abbrev EventMap (machine : Machine) (Event : Type u) :=
  (σ : machine.State) → machine.Enabled σ → Event

/-- Stable tickets for enabled machine events. These are the intended handles
for later fairness and liveness layers. -/
abbrev Tickets (machine : Machine) (Ticket : Type u) :=
  (σ : machine.State) → machine.Enabled σ → Ticket

/--
`Machine.Labeled` is a machine equipped with a stable external event label for
each enabled event.
-/
structure Labeled where
  toMachine : Machine
  Event : Type u
  event : toMachine.EventMap Event

/--
`Machine.Ticketed` is a machine equipped with a stable ticket for each enabled
event.
-/
structure Ticketed where
  toMachine : Machine
  Ticket : Type u
  ticket : toMachine.Tickets Ticket

/--
`Machine.System` augments a machine by the standard verification predicates
used throughout ArkLib and in transition-system frameworks such as Veil.
-/
structure System extends Machine where
  init : State → Prop
  assumptions : State → Prop := fun _ => True
  safe : State → Prop := fun _ => True
  inv : State → Prop := fun _ => True

/--
Compile a flat state-indexed machine into the continuation-based
`Concurrent.Process` core.

The parameter `semantics` supplies the root `NodeSemantics` for the one-node
sequential step representing the enabled event set of each state.
So `Machine.toProcess` is the exact bridge from state-indexed transition systems
to the more general interaction-centered process semantics.
-/
def toProcess {Party : Type u} (machine : Machine)
    (semantics : (σ : machine.State) → NodeSemantics Party (machine.Enabled σ)) :
    Process Party where
  Proc := machine.State
  step σ :=
    { spec := .node (machine.Enabled σ) (fun _ => .done)
      semantics := ⟨semantics σ, fun _ => PUnit.unit⟩
      next := fun
        | ⟨event, _⟩ => machine.step σ event }

/--
Compile a machine system into the corresponding process system.
-/
def System.toProcess {Party : Type u} (system : Machine.System)
    (semantics : (σ : system.State) → NodeSemantics Party (system.Enabled σ)) :
    Process.System Party where
  toProcess := system.toMachine.toProcess semantics
  init := system.init
  assumptions := system.assumptions
  safe := system.safe
  inv := system.inv

end Machine
end Concurrent
end Interaction
