/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Code families specific to ABF26 §2.4 and §2.5

Reed-Solomon variants and subspace-design codes that ABF26 introduces in §2.4 and §2.5
(Arnon-Boneh-Fenzi, *Open Problems in List Decoding and Correlated Agreement*, 2026).

## Main definitions

- `ReedSolomon.Interleaved.irsCode` — ABF26 Definition 2.13: `IRS[F, L, k, s] :=
  (RS[F, L, k/s])^≡s`, the `s`-interleaved Reed-Solomon code.
- `ReedSolomon.Folded.Admissible` — ABF26 Definition 2.14: an element `ω ∈ F` is
  `(L, s)`-admissible iff `α · ω^i ≠ β` for every `α, β ∈ L, α ≠ β` and `0 ≤ i < s`.
- `ReedSolomon.Folded.frsCode` — ABF26 Definition 2.15 [GR08]: the folded RS code
  `FRS[F, L, k, s, ω]`.
- `CodingTheory.IsSubspaceDesign` — ABF26 Definition 2.16 [GX13]: τ-subspace-design
  property for an F-additive code `C : F^k → (F^s)^n`.

## Main statements (external admits)

- `CodingTheory.subspaceDesign_tau_lower` — ABF26 Lemma 2.17 [GG25]: a τ-subspace-design
  code of rate `ρ` has `min_r τ(r) ≥ ρ - 1/n`.
- `CodingTheory.frs_is_subspaceDesign_gk16` — ABF26 Theorem 2.18 [GK16]: folded RS and
  univariate-multiplicity codes are τ-subspace-design for an explicit `τ`.

## Deferred

- Univariate multiplicity codes `UM[F, L, k, s]` are referenced in T2.18 but require a
  separate `D_ux` (derivative-of-x) operation; tracked under ABF26-D2.19 / DA.7.
- L2.10 (interleaved-code list-size bound) is the primary downstream consumer of IRS
  and is stated separately in `ListDecodability.lean`-adjacent work.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [GR08] Guruswami-Rudra. (Original FRS paper.)
- [GX13] Guruswami-Xing. (Original subspace-design definition.)
- [GG25] Goyal-Guruswami. (Cited for L2.17 / T4.13 / T4.14.)
- [GK16] Guruswami-Kopparty. (Cited for T2.18.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ReedSolomon

namespace Interleaved

/-- **ABF26 Definition 2.13.** The `s`-interleaved Reed-Solomon code:

  `IRS[F, L, k, s] := (RS[F, L, k/s])^≡s`

Each codeword is an `s`-tuple of base RS codewords arranged column-wise. Matches the
existing `interleavedCodeSet` API with the `s = Fin s` index type. -/
noncomputable def irsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) : Set (Matrix ι (Fin s) F) :=
  Code.interleavedCodeSet (κ := Fin s)
    ((ReedSolomon.code domain (k / s) : Set (ι → F)))

end Interleaved

namespace Folded

/-- **ABF26 Definition 2.14.** An element `ω : F` is `(L, s)`-admissible if for every
two distinct elements `α, β` of `L` and every `0 ≤ i < s` we have `α · ω^i ≠ β`.

Equivalently, the orbits `{α · ω^i : 0 ≤ i < s}` separate distinct points of `L`. This
ensures that in a folded Reed-Solomon codeword, every evaluation point appears only
once across all folds. -/
def Admissible {F : Type} [Field F] [DecidableEq F]
    (L : Finset F) (s : ℕ) (ω : F) : Prop :=
  ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β

/-- **ABF26 Definition 2.15 [GR08].** The folded Reed-Solomon code:

  `FRS[F, L, k, s, ω] := { f : L → F^s | ∃ f̂ ∈ F^{<k}[X],`
  `                          ∀ x ∈ L, f(x) = (f̂(x), f̂(x·ω), ..., f̂(x·ω^{s-1})) }`

The fold packages `s` consecutive evaluations of a single underlying polynomial into a
length-`s` vector at each evaluation point. We do not bake the `Admissible` hypothesis
into the definition itself — admissibility is left as a side condition for downstream
statements about distance / list decoding. Note that `FRS[F, L, k, 1, ω] = RS[F, L, k]`
for any `ω`. -/
noncomputable def frsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) : Set (ι → Fin s → F) :=
  { f | ∃ p : Polynomial F, p.degree < k ∧
        ∀ x : ι, ∀ j : Fin s, f x j = p.eval (domain x * ω ^ (j : ℕ)) }

end Folded

end ReedSolomon

namespace CodingTheory

open scoped NNReal

/-- **ABF26 Definition 2.16 [GX13].** A code `C : F^k → (F^s)^n` (here represented as a
subspace of `(ι → Fin s → F)` over `F`) is **τ-subspace-design** if for every `r ∈ ℕ`
and every F-linear subspace `A` of `C` with `dim A ≤ r`,

  `(Σ_{i ∈ [n]} dim A_i) / n ≤ dim A · τ(r)`

where `A_i := { a ∈ A : a_i = 0^s }` is the subspace of `A` whose codewords vanish at
position `i`. Here `A_i` is realised as `A ⊓ ker(eval_i)`, the intersection of `A`
with the kernel of the linear map evaluating the `i`-th coordinate. -/
def IsSubspaceDesign {ι : Type} [Fintype ι]
    {F : Type} [Field F] (s : ℕ) (τ : ℕ → ℝ)
    (C : Submodule F (ι → Fin s → F)) : Prop :=
  ∀ r : ℕ, ∀ A : Submodule F (ι → Fin s → F), A ≤ C →
    Module.finrank F A ≤ r →
    (∑ i : ι,
        (Module.finrank F (↥(A ⊓
            (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι => Fin s → F) i))
            : Submodule F (ι → Fin s → F))) : ℝ))
        / Fintype.card ι ≤
      Module.finrank F A * τ r

/-- **ABF26 Lemma 2.17 [GG25].** For any τ-subspace-design code of rate `ρ`, the
profile `τ` is lower-bounded by `ρ - 1/n`:

  `min_r τ(r) ≥ ρ - 1/n` .

Admitted as an external result. -/
theorem subspaceDesign_tau_lower
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) :
    ∀ r : ℕ, τ r ≥ (Module.finrank F C : ℝ) / Fintype.card ι - 1 / Fintype.card ι := by
  sorry -- ABF26-L2.17; external admit [GG25].

/-- **ABF26 Theorem 2.18 [GK16].** Both folded Reed-Solomon codes and univariate
multiplicity codes are τ-subspace-design for an explicit τ:

  `τ(r) := s · ρ / (s - r + 1)` for `r ∈ [s] = {1, …, s}`, and `τ(r) := 1` otherwise.

Note: `[s]` in the paper denotes `{1, …, s}` (one-based), which we encode in Lean as
`Finset.Icc 1 s`. With this convention `τ(1) = ρ` and `τ(s) = s · ρ`, matching the paper's
boundary values.

The FRS case requires `(L, s)`-admissibility of `ω`; the multiplicity case requires
`|F| > n` and `char(F) > ρ·s·n > s`. We state only the FRS half here; the multiplicity
half is gated on `D2.19 / DA.7` (univariate-multiplicity definition), which is tracked
separately. Admitted as an external result. -/
theorem frs_is_subspaceDesign_gk16
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (_hL_dom : ∀ i : ι, domain i ∈ L)
    (_hω : ReedSolomon.Folded.Admissible L s ω) :
    let τ : ℕ → ℝ := fun r =>
      if r ∈ Finset.Icc 1 s then
        (s : ℝ) * (k : ℝ) / Fintype.card ι / (s - r + 1)
      else 1
    ∃ C : Submodule F (ι → Fin s → F),
      (C : Set (ι → Fin s → F)) = ReedSolomon.Folded.frsCode domain k s ω ∧
      IsSubspaceDesign s τ C := by
  sorry -- ABF26-T2.18 (FRS half); external admit [GK16].

end CodingTheory
