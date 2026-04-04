/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Concurrent interfaces and open boundaries

This file introduces the smallest structural layer for open concurrent systems.

The current concurrent semantic center, `ProcessOver`, describes closed
residual processes whose step protocols already live inside the system. For
UC-style openness, contextual plugging, and general interaction with an
environment, we also need a typed notion of:

* what traffic may enter a component,
* what traffic may leave it, and
* how such open boundaries compose.

The design here is intentionally minimal and purely structural.

* `Interface` is just `PFunctor`, reused under a name that matches the
  interaction setting.
* `Interface.Packet Σ` is one concrete boundary message on interface `Σ`.
* `Interface.Hom Σ Τ` is a structure-preserving translation of packets from
  `Σ` to `Τ`.
* `PortBoundary` is a directed pair of input and output interfaces.
* `PortBoundary.swap`, `tensor`, `empty`, and `PortBoundary.Hom` are the basic
  operations needed to talk about open composition.

This file does **not** yet define open worlds, plugging, or runtime semantics.
Those later layers should build on these typed boundary primitives rather than
re-introducing their own packet/interface vocabulary.
-/

universe uA uB vA vB wA wB

namespace Interaction
namespace Concurrent

/--
`Interface` is the interaction-facing name for `PFunctor`.

An interface packages:

* a type of ports `A`, and
* for each port `a : A`, a type of messages `B a`.

This is the same dependent-container structure already used throughout the
existing `PFunctor` world. The point of the new name is only to reflect the
intended reading: these are typed communication interfaces.
-/
abbrev Interface := PFunctor

namespace Interface

/--
`Packet I` is one concrete message on interface `I`.

It consists of:

* a chosen port `a : I.A`, and
* a message `m : I.B a` carried on that port.

This is exactly `PFunctor.Idx I`, reused under a boundary-oriented name.
-/
abbrev Packet (I : PFunctor.{uA, uB}) : Type (max uA uB) :=
  PFunctor.Idx I

/--
`Query I α` is the continuation-bearing one-step query shape induced by the
interface `I`.

Unlike `Packet I`, which is just a concrete boundary message, `Query I α`
already stores a continuation returning values of type `α`.
So `Query` is the right bridge back to the existing `PFunctor` / oracle world,
while `Packet` is the right notion for plain boundary traffic.
-/
abbrev Query (I : PFunctor.{uA, uB}) (α : Type vA) :
    Type (max uA uB vA) :=
  PFunctor.Obj I α

/--
`Hom I J` is a structure-preserving translation from packets on interface `I`
to packets on interface `J`.

It consists of:

* a port translation `onPort`, and
* for each source port, a message translation into the corresponding target
  message type.

This is the basic structural notion of interface adaptation used later by
open boundaries. It deliberately translates packets only; richer
continuation-preserving interface maps can be introduced later if needed.
-/
structure Hom (I : PFunctor.{uA, uB}) (J : PFunctor.{vA, vB}) where
  onPort : I.A → J.A
  onMsg : {a : I.A} → I.B a → J.B (onPort a)

namespace Hom

/-- The identity interface translation. -/
def id (I : PFunctor.{uA, uB}) : Hom I I where
  onPort := fun a => a
  onMsg := fun m => m

/--
Compose two interface translations.

`comp g f` first translates packets along `f`, then along `g`.
-/
def comp
    {I : PFunctor.{uA, uB}}
    {J : PFunctor.{vA, vB}}
    {K : PFunctor.{wA, wB}}
    (g : Hom J K) (f : Hom I J) : Hom I K where
  onPort := g.onPort ∘ f.onPort
  onMsg := fun m => g.onMsg (f.onMsg m)

/--
Translate one concrete packet along an interface morphism.
-/
def mapPacket
    {I : PFunctor.{uA, uB}}
    {J : PFunctor.{vA, vB}}
    (f : Hom I J) : Packet I → Packet J
  | ⟨a, m⟩ => ⟨f.onPort a, f.onMsg m⟩

end Hom

/--
The empty interface with no ports and therefore no packets.
-/
def empty : PFunctor :=
  ⟨PEmpty, fun a => PEmpty.elim a⟩

/--
Disjoint sum of interfaces.

A packet on `sum Σ Τ` is either:

* a packet on `Σ`, tagged by `Sum.inl`, or
* a packet on `Τ`, tagged by `Sum.inr`.

This is the structural operation used later for side-by-side composition of
open boundaries.

The branch-specific message families are placed in a common universe using
`ULift`, so `sum` remains fully universe-polymorphic.
-/
def sum (I : PFunctor.{uA, uB}) (J : PFunctor.{vA, vB}) :
    PFunctor.{max uA vA, max uB vB} where
  A := Sum I.A J.A
  B
    | .inl a => ULift (I.B a)
    | .inr b => ULift (J.B b)

end Interface

/--
`PortBoundary` is a directed open boundary for a component or world.

* `In` is the interface of packets accepted from the outside.
* `Out` is the interface of packets emitted to the outside.

The direction matters: later plugging and contextual composition should not
identify incoming and outgoing traffic.
-/
structure PortBoundary where
  In : Interface
  Out : Interface

namespace PortBoundary

/--
The empty open boundary: no inputs and no outputs.
-/
def empty : PortBoundary :=
  ⟨Interface.empty, Interface.empty⟩

/--
Swap the direction of a boundary.

This is the structural operation underlying plugging:
the outputs expected by one side become inputs for the other, and vice versa.
-/
def swap (Δ : PortBoundary) : PortBoundary :=
  ⟨Δ.Out, Δ.In⟩

/--
Side-by-side composition of open boundaries.

Inputs and outputs are combined by disjoint sum, so the resulting boundary
exposes both components in parallel.
-/
def tensor (Δ₁ Δ₂ : PortBoundary) : PortBoundary :=
  ⟨Interface.sum Δ₁.In Δ₂.In, Interface.sum Δ₁.Out Δ₂.Out⟩

/--
`PortBoundary.Hom Δ₁ Δ₂` is a structural adaptation from boundary `Δ₁`
to boundary `Δ₂`.

The variance matches the operational reading:

* inputs are **contravariant**: a consumer of `Δ₂.In` can be fed by packets
  from `Δ₁.In` only if we know how to translate `Δ₂`-inputs back into
  `Δ₁`-inputs;
* outputs are **covariant**: packets produced on `Δ₁.Out` are translated
  forward into `Δ₂.Out`.

This is the boundary-level notion later used for interface adaptation and
structural plugging.
-/
structure Hom (Δ₁ Δ₂ : PortBoundary) where
  onIn : Interface.Hom Δ₂.In Δ₁.In
  onOut : Interface.Hom Δ₁.Out Δ₂.Out

namespace Hom

/-- The identity boundary adaptation. -/
def id (Δ : PortBoundary) : Hom Δ Δ where
  onIn := Interface.Hom.id Δ.In
  onOut := Interface.Hom.id Δ.Out

/--
Compose two boundary adaptations.

`comp g f` first adapts `Δ₁` to `Δ₂`, then adapts `Δ₂` to `Δ₃`.
-/
def comp
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (g : Hom Δ₂ Δ₃) (f : Hom Δ₁ Δ₂) : Hom Δ₁ Δ₃ where
  onIn := Interface.Hom.comp f.onIn g.onIn
  onOut := Interface.Hom.comp g.onOut f.onOut

end Hom

@[simp]
theorem swap_swap (Δ : PortBoundary) : Δ.swap.swap = Δ := by
  cases Δ
  rfl

end PortBoundary

end Concurrent
end Interaction
