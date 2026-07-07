/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Ring-Switching Profile

The `RingSwitchingProfile` abstraction captures the packing-layer data that every ring-switching
reduction needs, so that the protocol skeleton can be written once and instantiated by Binius
(DP24), Hachi (NOZ26 / ePrint 2026/156), and future small-ring/large-ring PCS work.

It is a `structure` passed **explicitly** (not a `class`): distinct profiles may share the same
carriers `(B, L, κ)` (e.g. with different bases), so instance resolution would be ambiguous.

It is stated over `CommRing` (not `Field`): Hachi's carrier `L = R_q` is not a field. The
`Field`-only steps (Schwartz–Zippel over `|L|`) stay at the soundness use-sites in the
ring-switching files, not here.

This file holds only the abstract structure (no Binius dependency), so `Prelude.lean` can import it
and parameterize the protocol over it; the Binius instance `binaryTowerProfile` lives in
`Prelude.lean`, after the tensor-algebra definitions it is built from.

## Fields and their two instantiations

| field | Binius (DP24) | Hachi (ePrint 2026/156) |
|---|---|---|
| `B`, `L` | small field `K`, tower field `L` | `R_q^H ≅ F_{q^k}`, `R_q` |
| `basis` | binary `K`-basis of `L`, rank `2^κ` | `ψ`; ArkLib `κ = log₂(d/k)` |
| `A` | tensor algebra `L ⊗[K] L` | `R_q` itself (`= L`) |
| `φ₀`, `φ₁` | `α ↦ α ⊗ 1`, `α ↦ 1 ⊗ α` | `id`, the automorphism `σ₋₁` |
| `decomposeRows`/`Columns` | `L`-coords of `ŝ` in `L ⊗_K L` | coords of `Y ∈ R_q` via `ψ` |

The only structural difference — Hachi has no separate tensor object (`A = L`, `φ₀ = id`,
`φ₁ = σ₋₁`) while Binius has `A = L ⊗_K L` — is absorbed by making `A`, `φ₀`,
and `φ₁` explicit fields.
The two `Prop`-valued fields `decomposeRows_spec` / `decomposeColumns_spec` are the base
coordinate-reconstruction laws tying `decomposeRows`/`decomposeColumns` to `φ₀`/`φ₁`/`basis`.
They rule out law-free coordinate maps, but they are not a standalone generic soundness theorem:
the batching and sumcheck proofs still have to connect these coordinates to `packMLE`,
`embedded_MLP_eval`, `compute_A_func`, and the instance-specific eq̃/trace identities. Each
instance discharges those protocol-level obligations from its own algebra (Binius: tensor
`Basis.sum_repr`; Hachi: Theorem 2 plus its CWSS soundness argument).

See also: the KB concept page `docs/kb/concepts/ring-switching.md` and the blueprint section
`blueprint/src/proof_systems/ring_switching.tex` for the protocol, phases, and security statements.
-/

namespace RingSwitching

open Module

/-- The packing-layer data a ring-switching reduction abstracts over. `L` is free of rank `2^κ`
over the small ring `B` (via `basis`); `A` is the pack/trace carrier where the folded element `ŝ`
lives (and which the batching phase sends on the wire). See the module docstring for the Binius and
Hachi instantiations of each field. -/
structure RingSwitchingProfile (B L : Type*) (κ : ℕ)
    [CommRing B] [CommRing L] [Algebra B L] where
  /-- rank-`2^κ` `B`-basis of `L`. -/
  basis : Basis (Fin κ → Fin 2) B L
  /-- pack/trace carrier; Binius `L ⊗[K] L`, Hachi `R_q` (`= L`). The batching wire type. -/
  A : Type*
  [commRingA : CommRing A]
  [algLA : Algebra L A]
  /-- column embedding `L → A`; Binius `α ↦ α ⊗ 1`, Hachi `id`. -/
  φ₀ : L →+* A
  /-- row embedding `L → A`; Binius `α ↦ 1 ⊗ α`, Hachi the automorphism `σ₋₁`. -/
  φ₁ : L →+* A
  /-- The `2^κ` `L`-valued "row" coordinates of an `A`-element (Binius: `β.baseChange L`-coords of
  `ŝ ∈ L ⊗_K L`; used in step 5 / `compute_s0`). Protocol-level identities relating these
  coordinates to `packMLE`/`compute_A_func` are discharged by the batching proofs, not by this
  data field alone. -/
  decomposeRows : A → (Fin κ → Fin 2) → L
  /-- The `2^κ` `L`-valued "column" coordinates of an `A`-element (Binius:
  `baseChangeRight`-coords; used in step 2 / `performCheckOriginalEvaluation`). NOTE: in the
  Binius instance this uses the *right* `L`-module structure on `A`, distinct from `algLA`
  (the left/`φ₀` action). -/
  decomposeColumns : A → (Fin κ → Fin 2) → L
  /-- **Row reconstruction law** (the base coordinate identity from DP24 §2.5 / Hachi Theorem 2):
  every `A`-element is recovered from its row coordinates via the `φ₀`-image of those coordinates
  weighted by the `φ₁`-image of the basis. This is the algebraic law tying `decomposeRows` to
  `φ₀`/`φ₁`/`basis` and rules out law-free profiles (e.g. `decomposeRows ≡ 0`). For Binius
  (`A = L ⊗_K L`) it is `Basis.sum_repr` for `β.baseChange L`; for Hachi it is supplied by
  Theorem 2 together with the profile-specific trace/coordinate interpretation. -/
  decomposeRows_spec : ∀ z : A, z = ∑ u, φ₀ (decomposeRows z u) * φ₁ (basis u)
  /-- **Column reconstruction law**: the right/`φ₁`-action dual of `decomposeRows_spec`. -/
  decomposeColumns_spec : ∀ z : A, z = ∑ v, φ₁ (decomposeColumns z v) * φ₀ (basis v)
  /-- **Column additivity**: `decomposeColumns` is additive in its `A`-argument (it is a genuine
  coordinate/`repr` map, not a law-free function). Binius: `map_add` of `baseChangeRight.repr`;
  Hachi: linearity of `ψ⁻¹` (Theorem 2, `ψ` linearly homomorphic). -/
  decomposeColumns_add : ∀ (z z' : A) (v : Fin κ → Fin 2),
    decomposeColumns (z + z') v = decomposeColumns z v + decomposeColumns z' v
  /-- **Column tmul/extraction law**: the `v`-column coordinate of `φ₀ x * φ₁ y` is
  `basis.repr x v • y`. Binius: `Basis.baseChangeRight_repr_tmul`; Hachi: Theorem 2's trace
  inner-product formula `Tr_H(ψ(a)·σ₋₁(ψ(b))) = (d/k)⟨a,b⟩`. Together with `decomposeColumns_add`
  this lets the batching/sumcheck completeness proofs compute `decomposeColumns` on the
  `∑_w φ₀(eqTilde_w)·φ₁(t'(w))` structure of `embedded_MLP_eval` — closing the generic proof. -/
  decomposeColumns_tmul : ∀ (x y : L) (v : Fin κ → Fin 2),
    decomposeColumns (φ₀ x * φ₁ y) v = basis.repr x v • y
  /-- **Row additivity** (dual of `decomposeColumns_add`). -/
  decomposeRows_add : ∀ (z z' : A) (u : Fin κ → Fin 2),
    decomposeRows (z + z') u = decomposeRows z u + decomposeRows z' u
  /-- **Row tmul/extraction law** (dual of `decomposeColumns_tmul`; the `φ₀`/`φ₁` roles swap):
  the `u`-row coordinate of `φ₀ x * φ₁ y` is `basis.repr y u • x`. Binius:
  `Basis.baseChange_repr_tmul`; Hachi: Theorem 2's trace formula. -/
  decomposeRows_tmul : ∀ (x y : L) (u : Fin κ → Fin 2),
    decomposeRows (φ₀ x * φ₁ y) u = basis.repr y u • x
  /-- **Column injectivity/faithfulness**: `decomposeColumns` determines the `A`-element — it is a
  genuine coordinate/`repr` map, so distinct `A`-elements have distinct column-coordinate vectors.
  Binius: `(baseChangeRight β).repr` is a `LinearEquiv`, hence injective; Hachi: `ψ` is a bijection
  (Theorem 2 invertibility, "crucial in arguing knowledge soundness"). Used by the batching
  Schwartz–Zippel soundness argument (`batchingMismatchPoly_nonzero_of_ne`), which needs that a
  nonzero column-coordinate mismatch witnesses a genuine `A`-level difference. -/
  decomposeColumns_injective : Function.Injective decomposeColumns

attribute [instance] RingSwitchingProfile.commRingA RingSwitchingProfile.algLA

end RingSwitching
