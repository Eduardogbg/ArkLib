/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded

/-!
# Subspace-design codes (ABF26 §2.5)

ABF26 Definition 2.16 [GX13]: the τ-subspace-design property for an F-additive code
`C : F^k → (F^s)^n`. Lemmas 2.17 [GG25] and Theorem 2.18 [GK16] are stated as external
admits.

## Main definitions

- `CodingTheory.IsSubspaceDesign` — ABF26 Definition 2.16.

## Main statements (external admits)

- `CodingTheory.ker_proj_eq_vanish_at` — bridge between `ker(proj i)` and `{a | a i = 0}`.
- `CodingTheory.subspaceDesign_tau_lower` — ABF26 Lemma 2.17 [GG25]: τ-subspace-design
  code of rate `ρ` has `min_r τ(r) ≥ ρ - 1/n`.
- `CodingTheory.frs_is_subspaceDesign_gk16` — ABF26 Theorem 2.18 [GK16]: folded RS codes
  are τ-subspace-design for explicit τ.

## Deferred

- Univariate multiplicity codes `UM[F, L, k, s]` are referenced in T2.18 but require a
  separate `D_ux` (derivative-of-x) operation; tracked under ABF26-D2.19 / DA.7.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §2.5 Definition 2.16, Lemma 2.17, Theorem 2.18.
- [GX13] Guruswami-Xing. (Original subspace-design definition.)
- [GG25] Goyal-Guruswami. (Cited for L2.17.)
- [GK16] Guruswami-Kopparty. (Cited for T2.18.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

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
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) : ℝ)) /
        Fintype.card ι ≤
      Module.finrank F A * τ r

/-- **Bridge: kernel of the `i`-th projection equals the comprehension `{a | a i = 0}`.**

The subspace `A_i := {a ∈ A : a_i = 0^s}` from the paper's `IsSubspaceDesign` definition
is `A ⊓ ker(LinearMap.proj i)`. This lemma confirms the underlying set: a word
`a : ι → Fin s → F` lies in `ker(proj i)` iff `a i = 0`. Combined with `Submodule.inf_*`
this lets downstream proofs rewrite freely between the technical `ker(proj i)` form (used
in the `IsSubspaceDesign` definition for type-class reasons) and the paper's
comprehension form. -/
lemma ker_proj_eq_vanish_at {ι : Type*} {F : Type*} [Semiring F] {s : ℕ} (i : ι) :
    (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) :
        Set (ι → Fin s → F)) =
      {a | a i = 0} := by
  ext a
  simp [LinearMap.mem_ker, LinearMap.proj_apply]

/-- **ABF26 Lemma 2.17 [GG25].** For any τ-subspace-design code of rate `ρ`, the
profile `τ` is lower-bounded by `ρ - 1/n` over the paper's range `r ∈ [s] = {1, …, s}`:

  `min_{r ∈ [s]} τ(r) ≥ ρ - 1/n` .

The quantifier is restricted to `r ∈ Finset.Icc 1 s` to match the paper's `[s]`
notation: outside this range the `IsSubspaceDesign` predicate places no
constraint on `τ`, so the bound is vacuous for `r = 0` (where `A ≤ C` with
`finrank A ≤ 0` forces `A = ⊥`, making the design inequality `0 ≤ 0 · τ(0)`
trivially satisfied by any `τ(0)` including ones violating the lower bound).

Admitted as an external result. -/
theorem subspaceDesign_tau_lower
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) :
    ∀ r ∈ Finset.Icc 1 s,
      τ r ≥ (Module.finrank F C : ℝ) / Fintype.card ι - 1 / Fintype.card ι := by
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
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then
        (s : ℝ) * (k : ℝ) / Fintype.card ι / (s - r + 1)
      else 1
    IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω) := by
  sorry -- ABF26-T2.18 (FRS half); external admit [GK16].

end CodingTheory
