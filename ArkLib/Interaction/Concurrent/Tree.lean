/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Current
import ArkLib.Interaction.Concurrent.Process

/-!
# Structural-tree frontend for dynamic processes

This file turns the existing structural concurrent syntax into a frontend for
the new dynamic `Concurrent.Process` core.

The current structural tree layer provides:

* `Concurrent.Spec` — a finite syntax of atomic nodes and binary `par`;
* `Front` / `residual` — the current frontier view of enabled events;
* `Control` — structural control ownership over current frontier choices;
* `Profile` — structural per-party local views of frontier events;
* `Current` — the combined current controller and local view of the next
  frontier event.

This frontend compiles such a structural residual state into a one-step process:
one process step corresponds to one scheduled frontier event of the current
structural spec.

So the structural tree language remains an important source language, but it is
no longer the semantic center of the concurrent layer.
-/

universe u

namespace Interaction
namespace Concurrent
namespace Tree

private def liftView {X : Type (u + 1)} :
    Multiparty.LocalView X → Multiparty.LocalView (ULift.{0, u + 1} X)
  | .active => .active
  | .observe => .observe
  | .hidden => .hidden
  | .quotient Obs toObs => .quotient Obs (fun x => toObs x.down)

/--
`State Party` is one structural concurrent residual state packaged together
with its control tree and observation profile.

This is the exact data needed to view the current structural tree as one state
of a dynamic `Concurrent.Process`.
-/
structure State (Party : Type u) where
  spec : Concurrent.Spec
  control : Control Party spec
  profile : Profile Party spec

namespace State

/--
`currentStep st` is the one-step process view of the structural residual state
`st`.

Its sequential interaction shape is a single node whose move type is the
current frontier `Front st.spec`. The node semantics are exactly the current
controller and current per-party local views computed by `Concurrent.Current`.
Completing that one-node step advances to the residual structural state after
the chosen frontier event.
-/
def currentStep {Party : Type u} [DecidableEq Party] (st : State Party) :
    Step Party (State Party) :=
  { spec := .node (ULift.{0, u + 1} (Front st.spec)) (fun _ => .done)
    semantics :=
      ⟨{ controller? := Current.controller? st.control
         views := fun me => liftView (Current.view me st.control st.profile) },
        fun _ => PUnit.unit⟩
    next := fun
      | ⟨event, _⟩ =>
          { spec := residual event.down
            control := Control.residual st.control event.down
            profile := Profile.residual st.profile event.down } }

end State

/--
`toProcess` compiles the structural concurrent-tree frontend into the dynamic
`Concurrent.Process` core.

Each process state is one packaged structural residual state, and each process
step is the current one-node frontier interaction produced by `State.currentStep`.
-/
def toProcess {Party : Type u} [DecidableEq Party] : Process Party where
  Proc := State Party
  step := State.currentStep

/-- Package one structural residual state as the initial state of the tree
frontend process. -/
def init {Party : Type u} {spec : Concurrent.Spec}
    (control : Control Party spec) (profile : Profile Party spec) : State Party :=
  { spec := spec, control := control, profile := profile }

end Tree
end Concurrent
end Interaction
