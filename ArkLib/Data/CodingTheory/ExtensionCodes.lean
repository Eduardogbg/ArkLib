/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Extension fields and extension codes (ABF26 §2.6)

Definitions and one external-admit lemma from ABF26 §2.6 (Arnon-Boneh-Fenzi,
*Open Problems in List Decoding and Correlated Agreement*, 2026, page 11):
extension-field presentations, extension codes obtained by base-change, and the
relation `|Λ(C_F, δ)| = |Λ(C_B^e, δ)|` between the list size of an extension code
and the list size of the corresponding interleaved base code.

## Main definitions

- `ExtensionFieldPresentation` (D2.19): tuple `(B, F, e, ψ, φ)` packaging a field
  embedding `ψ : B ↪ F` of dimension `e` together with a `B`-linear isomorphism
  `φ : F ≃ B^e`.
- `CodingTheory.extensionCode` (D2.20): the extension code `C_F : F^k → F^n`
  obtained from a `B`-linear code `C_B : B^k → B^n` via an `ExtensionFieldPresentation`.

## Main statements (external admits)

- `CodingTheory.lambda_extensionCode_eq_lambda_interleaved` (L2.21, [BCFW25 Lem D.3]):
  `|Λ(C_F, δ)| = |Λ(C_B^≡e, δ)|`.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [BCFW25] Bordage-Chiesa-Fenzi-Wahby. Lemma D.3.

(The distance equality `δ_min(C_F) = δ_min(C_B)`, referenced in the L2.21 paragraph
context, is from Dao-Petrov 2025 (Theorem 3.2 in their paper). The knowledge-base
citation key for this paper is not yet registered, so we mention it in prose only.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CodingTheory

open scoped NNReal
open ListDecodable

/-- **ABF26 Definition 2.19.** An *extension field presentation* is a tuple
`(B, F, e, ψ, φ)` where:

- `B` and `F` are fields,
- `ψ : B → F` is an injective field homomorphism,
- `e : ℕ` is the dimension of `F` as a `B`-vector space,
- `φ : F ≃ₗ[B] (Fin e → B)` is a `B`-linear isomorphism.

We package these as a structure rather than a tuple for ergonomic access at use
sites. The "systematic" predicate (paper: `φ(ψ(x)) = (x, 0, …, 0)`) is the
optional `systematic` field.

**B-linearity certification.** In addition to invertibility, the structure carries
explicit witnesses `φ_add` and `φ_smul_psi` certifying that `φ` is additive and
compatible with the `B`-action induced by `ψ` (i.e. `φ (ψ b * x) = b • φ x`).
These witnesses are what makes `extensionCode P C_B` an additive- and B-scalar-
closed subset of `ι → F`. -/
structure ExtensionFieldPresentation (B F : Type) [Field B] [Field F] where
  /-- The dimension `e := dim_B F`. -/
  e : ℕ
  /-- The base-field embedding `ψ : B ↪ F`. -/
  ψ : B →+* F
  /-- Injectivity of `ψ` (`ψ` is a *non-trivial* ring hom between fields). -/
  ψ_injective : Function.Injective ψ
  /-- The `B`-linear isomorphism `φ : F ≃ B^e`. The `B`-module structure on `F`
      comes from `ψ` via `letI := ψ.toAlgebra`. The Lean-side equivalence is
      packaged via a `Module` instance on `F` provided at the use site. -/
  φ : F → Fin e → B
  /-- Mirror map `φ⁻¹`. -/
  φ_inv : (Fin e → B) → F
  /-- Left inverse. -/
  φ_left_inv : Function.LeftInverse φ_inv φ
  /-- Right inverse. -/
  φ_right_inv : Function.RightInverse φ_inv φ
  /-- `φ` is additive. -/
  φ_add : ∀ x y : F, φ (x + y) = φ x + φ y
  /-- `φ` respects the `B`-action induced by `ψ`: `φ (ψ b * x) = b • φ x`,
      equivalently `φ ((ψ b) · x) j = b · φ x j` for every coordinate `j`. -/
  φ_smul_psi : ∀ (b : B) (x : F), φ (ψ b * x) = fun j ↦ b * φ x j

namespace ExtensionFieldPresentation

variable {B F : Type} [Field B] [Field F]

/-- A presentation is *systematic* if `φ(ψ(x)) = (x, 0, …, 0)` for every `x : B`.
This makes the base-field copy of `B` inside `F` align with the first coordinate.
Requires `P.e ≥ 1` for the "first coordinate" to exist; we sidestep the
`Fin P.e` typeclass requirement by indexing on `i.val`. -/
def IsSystematic (P : ExtensionFieldPresentation B F) : Prop :=
  ∀ x : B, P.φ (P.ψ x) = fun i ↦ if i.val = 0 then x else 0

/-- The `i`-th coordinate `φᵢ : F → B` of an extension-field presentation. Applied
componentwise to vectors in the paper. -/
def coord (P : ExtensionFieldPresentation B F) (i : Fin P.e) : F → B :=
  fun x ↦ P.φ x i

/-- Each coordinate `P.coord j` is additive. -/
lemma coord_add (P : ExtensionFieldPresentation B F) (j : Fin P.e) (x y : F) :
    P.coord j (x + y) = P.coord j x + P.coord j y := by
  simp only [coord, P.φ_add]
  rfl

/-- Each coordinate `P.coord j` respects the `ψ`-induced `B`-action:
`P.coord j (ψ b · x) = b · P.coord j x`. -/
lemma coord_psi_smul (P : ExtensionFieldPresentation B F)
    (j : Fin P.e) (b : B) (x : F) :
    P.coord j (P.ψ b * x) = b * P.coord j x := by
  simp only [coord, P.φ_smul_psi]

end ExtensionFieldPresentation

/-- **ABF26 Definition 2.20.** The *extension code* `C_F : F^k → F^n` associated to a
linear code `C_B : B^k → B^n` via an extension-field presentation. Defined on a
vector `v : ι → F` by

  `v ∈ C_F  ↔  ∃ c_B : ι → Fin e → B, (∀ i, c_B i ∈ projections of v) ∧`
  `              (∀ j : Fin e, (fun i ↦ c_B i j) ∈ C_B)`

i.e. each of the `e` coordinate-projections of `v` lies in `C_B`. We express the
codeword set; the underlying `Submodule F (ι → F)` structure follows by closure of
`C_B` under linear combinations, but we keep the `Set`-level definition for direct
comparison with the paper's encoder shape.

**Closure properties.** With `B`-linearity certified by `ExtensionFieldPresentation`'s
`φ_add` / `φ_smul_psi` fields, we get:

- `extensionCode_add_mem` — closure under addition (provided `C_B` is closed under
  addition).
- `extensionCode_psi_smul_mem` — closure under the `ψ`-induced `B`-scalar action
  (provided `C_B` is closed under `B`-scalar multiplication).

These together make `extensionCode P C_B` a `B`-submodule-style subset of `ι → F` when
`C_B` is `B`-linear. **Full F-Submodule promotion** (i.e. closure under arbitrary
F-scalar multiplication, not just the `ψ(b)·x` action) requires a basis expansion of
F-multiplication over the `φ`-basis — gated on `[Algebra B F] + [Module.Finite B F] +
Basis B F` from Mathlib. Deferred as a polish follow-up; the bridge lemmas below
provide the structural skeleton. -/
def extensionCode {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) : Set (ι → F) :=
  { v : ι → F | ∀ j : Fin P.e, (fun i ↦ P.coord j (v i)) ∈ C_B }

/-- **Bridge to paper's encoder-image view.** The paper writes
`C_F(v) := φ⁻¹(C_B(φ_1(v)), …, C_B(φ_e(v)))` as an encoder, so
`Im(C_F) = { φ_inv(c_B^{(1)}, …, c_B^{(e)}) | (c_B^{(j)})_j ∈ (C_B)^e }`.

Under the bijection `φ : F ≃ Fin e → B` (componentwise) this is the same as our
set-comprehension `extensionCode`: a vector `v : ι → F` is in `extensionCode P C_B`
iff each of its `e` coordinate-projections lies in `C_B`. The equivalence holds because
`φ` is bijective, so any tuple of base codewords lifts to a unique extension-field
vector.

Formal statement: `v ∈ extensionCode P C_B` iff there exist base codewords
`(c^{(j)} : ι → B)` for each `j : Fin P.e` such that `(c^{(j)})_j ∈ C_B` and
`P.coord j (v i) = c^{(j)} i` everywhere. -/
lemma extensionCode_iff_coord_in_base
    {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) (v : ι → F) :
    v ∈ extensionCode P C_B ↔
      ∀ j : Fin P.e, (fun i ↦ P.coord j (v i)) ∈ C_B := by
  rfl

/-- **`extensionCode` is closed under addition** when `C_B` is. Uses the additivity
field `P.φ_add` (equivalently `P.coord_add` componentwise). -/
lemma extensionCode_add_mem
    {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F]
    (P : ExtensionFieldPresentation B F)
    {C_B : Set (ι → B)}
    (hadd : ∀ {a b : ι → B}, a ∈ C_B → b ∈ C_B → a + b ∈ C_B)
    {u v : ι → F} (hu : u ∈ extensionCode P C_B) (hv : v ∈ extensionCode P C_B) :
    u + v ∈ extensionCode P C_B := by
  intro j
  have h := hadd (hu j) (hv j)
  have hpt : (fun i ↦ P.coord j ((u + v) i)) =
      (fun i ↦ P.coord j (u i)) + fun i ↦ P.coord j (v i) := by
    ext i
    exact P.coord_add j (u i) (v i)
  rw [hpt]
  exact h

/-- **`extensionCode` is closed under the `ψ`-induced `B`-scalar action** when `C_B`
is `B`-scalar closed. Uses `P.φ_smul_psi` (equivalently `P.coord_psi_smul`
componentwise). -/
lemma extensionCode_psi_smul_mem
    {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F]
    (P : ExtensionFieldPresentation B F)
    {C_B : Set (ι → B)}
    (hsmul : ∀ (b : B) {a : ι → B}, a ∈ C_B → b • a ∈ C_B)
    (b : B) {v : ι → F} (hv : v ∈ extensionCode P C_B) :
    (fun i ↦ P.ψ b * v i) ∈ extensionCode P C_B := by
  intro j
  have h := hsmul b (hv j)
  have hpt : (fun i ↦ P.coord j (P.ψ b * v i)) = b • fun i ↦ P.coord j (v i) := by
    ext i
    simpa [Pi.smul_apply, smul_eq_mul] using P.coord_psi_smul j b (v i)
  rw [hpt]
  exact h

/-- **F-scalar closure of `extensionCode`** — full F-Submodule completion.

When `C_B` is `B`-linear, `extensionCode P C_B` is `F`-linear (the paper's D2.20
claim). Together with `extensionCode_add_mem`, this lemma promotes
`extensionCode P C_B` to a `Submodule F (ι → F)` and closes the F-linearity gap that
was flagged in the post-refactor review.

**Proof strategy** (admitted as a tagged sorry; the proof requires structure constants
not currently exposed by `ExtensionFieldPresentation`).

Decompose `α : F` via the `φ`-basis as `α = ∑_l ψ(P.φ α l) * α_l`, where
`α_l := P.φ_inv (Pi.single l 1)` is the `l`-th basis element of `F` over `B`. Then
F-multiplication `α * x` rewrites coordinate-by-coordinate via the structure constants
of `F` as a `B`-algebra wrt this basis: there exist
`γ : Fin e → Fin e → Fin e → B` with `α_l · α_m = ∑_j γ_{l,m,j} · α_j`, giving

  `P.coord j (α * x) = ∑_l ∑_m γ_{l,m,j} · P.φ α l · P.coord m x`.

With this expansion every coordinate of `α · v` is a `B`-linear combination of the
coordinates of `v`, which lie in `C_B` by hypothesis; `B`-linearity of `C_B` closes
the sum.

Closing requires either:
- A structure-constants field `φ_mul` on `ExtensionFieldPresentation` recording `γ`, or
- A refactor of `ExtensionFieldPresentation` using Mathlib's `[Algebra B F] + Basis`
  (B5), in which case `γ` is computed from `Basis.equivFun` applied to multiplication.
The latter is cleaner long-term. -/
lemma extensionCode_smul_mem
    {ι : Type} [Fintype ι]
    {B F : Type} [Field B] [Field F]
    (P : ExtensionFieldPresentation B F)
    {C_B : Set (ι → B)}
    (_hadd : ∀ {a b : ι → B}, a ∈ C_B → b ∈ C_B → a + b ∈ C_B)
    (_hsmul : ∀ (b : B) {a : ι → B}, a ∈ C_B → b • a ∈ C_B)
    (α : F) {v : ι → F} (_hv : v ∈ extensionCode P C_B) :
    (fun i ↦ α * v i) ∈ extensionCode P C_B := by
  sorry -- ABF26-D2.20 F-scalar closure; needs F-algebra structure constants (B5 refactor).

/-- **ABF26 Lemma 2.21 [BCFW25 Lemma D.3].** List size of an extension code equals the
list size of the corresponding interleaved base code. Let `C_B : B^k → B^n` be a
linear code and `P` be an extension-field presentation. For every `δ ∈ (0, 1)`:

  `|Λ(C_F, δ)| = |Λ(C_B^≡e, δ)|`

where `C_F` is the extension code (D2.20) and `C_B^≡e` is the `e`-fold interleaved
base code (D2.9). Admitted as an external result. -/
theorem lambda_extensionCode_eq_lambda_interleaved
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {B F : Type} [Field B] [Fintype B] [DecidableEq B]
    [Field F] [Fintype F] [DecidableEq F]
    (P : ExtensionFieldPresentation B F)
    (C_B : Set (ι → B)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    Lambda (extensionCode P C_B) δ =
      Lambda (Code.interleavedCodeSet (κ := Fin P.e) C_B)
        δ := by
  sorry -- ABF26-L2.21; external admit [BCFW25 Lem D.3].

end CodingTheory
