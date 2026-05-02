/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.Basic
import ArkLib.Interaction.Reduction

/-!
# Schnorr's Σ-Protocol — Two Views

A 3-round public-coin proof of knowledge of discrete logarithm, written twice against ArkLib's
two interactive frameworks:

1. `State.*` — ArkLib's flat `Prover` / `Verifier` / `Reduction` schema (in
   `ArkLib/OracleReduction/Basic.lean`) with an explicit `PrvState : Fin (n + 1) → Type`
   family and case-splits on round indices.
2. `Interactive.*` — ArkLib's `Interaction.Prover` / `Interaction.Verifier` /
   `Interaction.Reduction` wrappers (in `ArkLib/Interaction/Reduction.lean`) over VCVio's
   `Spec.Strategy.withRoles` / `Spec.Counterpart`. The protocol is a `Spec` (free monad over
   `Spec.basePFunctor`); the prover/verifier inhabit `Strategy.withRoles` / `Counterpart`,
   which definitionally unfold to iterated-monad forms. State threads through via lexical
   scope; no `PrvState` family, no case-split on round indices.

Both target the same Σ-protocol:

  Round 0  (P → V) : `R = r • g`     where `r ← $ᵗ F`     (commitment)
  Round 1  (V → P) : `c ← $ᵗ F`                            (random challenge)
  Round 2  (P → V) : `z = r + c · sk`                      (response)
  Verifier accepts iff `z • g = R + c • pk`.

## Setup

- `F` : scalar field (sampleable, decidable equality)
- `G` : additive group acted on by `F` via `Module F G`
- `g : G` : public generator
- Statement `pk : G`, witness `sk : F`, relation `sk • g = pk`
-/

namespace Schnorr

variable (F : Type) [Field F] [Sampleable F]
variable (G : Type) [AddCommGroup G] [Module F G] [DecidableEq G]
variable (g : G)

/-- The discrete-log relation: `sk` is the discrete log of `pk` w.r.t. generator `g`. -/
@[reducible, simp]
def relIn : Set (G × F) := { ⟨pk, sk⟩ | sk • g = pk }

/-- Trivial output relation (acceptance is encoded via the verifier returning `pure ()`). -/
@[reducible, simp]
def relOut : Set (Unit × Unit) := Set.univ

/-! ## State-based view: ArkLib's flat `Prover` / `Verifier` / `Reduction` schema. -/

namespace State

open OracleComp OracleSpec ProtocolSpec

/-- The 3-round Schnorr protocol specification:
    `(P → V : G), (V → P : F), (P → V : F)`. -/
@[reducible]
def pSpec : ProtocolSpec 3 :=
  ⟨!v[.P_to_V, .V_to_P, .P_to_V], !v[G, F, F]⟩

instance : ∀ i, SampleableType ((pSpec F G).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => inferInstanceAs (SampleableType F)
  | ⟨2, h⟩ => nomatch h

instance : ∀ i, VCVCompatible ((pSpec F G).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => inferInstanceAs (VCVCompatible F)
  | ⟨2, h⟩ => nomatch h

/-- The honest Schnorr prover, state-based.

  - State 0 : `(pk, sk)`         — input context
  - State 1 : `(sk, r)`          — secret + sampled randomness
  - State 2 : `z`                — fully-formed response
  - State 3 : `Unit`

  Sampling happens in round 0 via `$ᵗ F`; everything else is pure. -/
@[inline, specialize]
def prover : Prover unifSpec G F Unit Unit (pSpec F G) where
  PrvState
  | 0 => G × F
  | 1 => F × F
  | 2 => F
  | 3 => Unit
  input := id
  sendMessage
  | ⟨0, _⟩ => fun (_pk, sk) => do
      let r ← $ᵗ F
      pure (r • g, (sk, r))
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun z => pure (z, ())
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun (sk, r) => pure (fun (c : F) => r + c * sk)
  | ⟨2, h⟩ => nomatch h
  output := fun () => pure ((), ())

/-- The honest Schnorr verifier, state-based.

  Pure algebraic check `z • g = R + c • pk`; no oracle queries needed. The result lives in
  `OptionT (OracleComp unifSpec) Unit`, so rejection is `failure`. -/
@[inline, specialize]
def verifier : Verifier unifSpec G Unit (pSpec F G) where
  verify := fun pk tr =>
    let R : G := tr 0
    let c : F := tr 1
    let z : F := tr 2
    if z • g = R + c • pk then pure () else failure

/-- Schnorr's Σ-protocol packaged as an ArkLib `Reduction`. -/
@[inline, specialize]
def reduction : Reduction unifSpec G F Unit Unit (pSpec F G) where
  prover := prover F G g
  verifier := verifier F G g

end State

/-! ## Interactive view: ArkLib's `Interaction.Prover` / `Interaction.Verifier` /
  `Interaction.Reduction` wrappers over `Spec.Strategy.withRoles` / `Spec.Counterpart`.

  The protocol shape is a real W-type (free monad over `Spec.basePFunctor`); the prover and
  verifier inhabit the actual `Strategy.withRoles` and `Counterpart` types — wrapped, by ArkLib's
  `Interaction.Prover`/`Verifier` abbrevs, with the standard `(SharedIn, StatementIn, WitnessIn,
  StatementOut, WitnessOut)` indexing. -/

namespace Interactive

open Interaction OracleComp OracleSpec

/-- Schnorr's 3-round interaction tree, as a `Spec`:
    `node G (fun _ => node F (fun _ => node F (fun _ => done)))`. -/
def spec : Spec :=
  .node G fun _ => .node F fun _ => .node F fun _ => .done

/-- Per-node sender / receiver assignment from the prover's perspective:
    sender, receiver, sender. -/
def proverRoles : RoleDecoration (spec F G) :=
  ⟨.sender, fun _ => ⟨.receiver, fun _ => ⟨.sender, fun _ => ⟨⟩⟩⟩⟩

/-- The honest Schnorr prover as an `Interaction.Prover` over `OracleComp unifSpec`.

  Indexing follows the top-level convention from `ArkLib/Interaction/Reduction.lean`:
  `SharedIn := G` carries the public key, `StatementIn := PUnit`, `WitnessIn := F` the secret key.
  The output type at `.done` is `HonestProverOutput (Option Unit) PUnit`.

  After unfolding `Strategy.withRoles` on the role decoration, the underlying strategy has type
  `m ((R : G) × ((c : F) → m (m ((z : F) × (Option Unit × PUnit)))))` for
  `m = OracleComp unifSpec`. -/
@[inline, specialize]
def prover :
    Prover (OracleComp unifSpec) G
      (fun _ => spec F G) (fun _ => proverRoles F G)
      (fun _ => PUnit) (fun _ => F)
      (fun _ _ => Option Unit) (fun _ _ => PUnit) :=
  fun _pk _ sk => pure (do
    let r ← $ᵗ F
    pure ⟨r • g, fun c => pure (pure ⟨r + c * sk, (some (), PUnit.unit)⟩)⟩)

/-- The honest Schnorr verifier as an `Interaction.Verifier` over `OracleComp unifSpec`.

  `StatementOut := Option Unit` carries the accept / reject decision (`some ()` accepts,
  `none` rejects). After unfolding `Counterpart`, the underlying counterpart has type
  `(R : G) → m (m ((c : F) × ((z : F) → m (Option Unit))))` for `m = OracleComp unifSpec`. -/
@[inline, specialize]
def verifier :
    Verifier (OracleComp unifSpec) G
      (fun _ => spec F G) (fun _ => proverRoles F G)
      (fun _ => PUnit) (fun _ _ => Option Unit) :=
  fun pk _ R => pure (do
    let c ← $ᵗ F
    pure ⟨c, fun (z : F) =>
      pure (if z • g = R + c • pk then some () else none)⟩)

/-- Schnorr's Σ-protocol packaged as an `Interaction.Reduction`. -/
@[inline, specialize]
def reduction :
    Reduction (OracleComp unifSpec) G
      (fun _ => spec F G) (fun _ => proverRoles F G)
      (fun _ => PUnit) (fun _ => F)
      (fun _ _ => Option Unit) (fun _ _ => PUnit) where
  prover := prover F G g
  verifier := verifier F G g

/-! ### Type-unfolding checks

Both `Strategy.withRoles` and `Counterpart` are abbrevs whose unfolding on a concrete role
decoration is proved by `rfl`. The two `example`s below pin down exactly the iterated-monad
shapes asserted in the docstrings of `prover` and `verifier`. -/

example :
    Spec.Strategy.withRoles (OracleComp unifSpec) (spec F G) (proverRoles F G)
      (fun _ => HonestProverOutput (Option Unit) PUnit) =
      OracleComp unifSpec ((_ : G) ×
        ((_ : F) → OracleComp unifSpec (OracleComp unifSpec
          ((_ : F) × (Option Unit × PUnit))))) := rfl

example :
    Spec.Counterpart (OracleComp unifSpec) (spec F G) (proverRoles F G)
      (fun _ => Option Unit) =
      ((_ : G) → OracleComp unifSpec (OracleComp unifSpec ((_ : F) ×
        ((_ : F) → OracleComp unifSpec (Option Unit))))) := rfl

end Interactive

end Schnorr
