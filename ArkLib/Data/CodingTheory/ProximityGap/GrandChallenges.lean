/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.EpsilonErrors
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Grand Challenges from ABF26 §1

The paper *Open Problems in List Decoding and Correlated Agreement* (Arnon, Boneh, Fenzi;
April 8, 2026) frames its survey around two open problems, stated on page 5:

1. **Grand MCA Challenge.** Given a Reed-Solomon code `C := RS[F, L, k]` over a smooth
   evaluation domain `L`, with constant rate `ρ(C) := k/|L| ∈ {1/2, 1/4, 1/8, 1/16}` and a
   threshold `ε*` (e.g. `2^(-128)`), determine the largest `δ*_C ∈ [0, 1]` such that
   `ε_mca(C, δ*_C) ≤ ε*`, assuming `|F|` is sufficiently large so that such a `δ*_C` exists.

2. **Grand List Decoding Challenge.** With the same RS setup and a constant interleaving
   parameter `m`, determine the largest `δ*_C ∈ [0, 1]` such that
   `|Λ(C^≡m, δ*_C)| ≤ ε* · |F|`, again assuming sufficiently large `|F|`.

The paper notes that resolving these challenges does not require an efficient
list-decoding algorithm; the questions are purely combinatorial.

## Formalisation choices

Both challenges are stated as `Prop`-valued predicates over generic codes. The rate
constraints `ρ ∈ {1/2, 1/4, 1/8, 1/16}` and the threshold `ε* = 2^(-128)` are paper-level
parameter regimes; the Lean statement leaves `ε*` as an arbitrary `ℝ≥0` so a future
caller can plug in concrete values. Likewise the `|F|`-sufficiently-large hypothesis is a
meta-comment, not a Lean hypothesis — instantiating the predicate at a specific code
either constructs the witness `δ*_C` or rules it out.

Resolution paths:

- **Upper-bound progress**: any theorem of the form `ε_mca(RS[F, L, k], δ) ≤ ε*` for some
  computable `δ`-expression in terms of `(F, L, k, ε*)` yields a constructive witness.
  This is exactly what Table 1 of the paper summarizes, with the various `BCIKS20`,
  `BCHKS25`, `GG25`, … bounds filling in the picture.
- **Lower-bound progress**: any theorem `ε_mca(RS[F, L, k], δ) > ε*` for `δ` above some
  threshold rules out witnesses above that threshold, tightening the search.

The two challenges sit at the centre of the dependency graph of the paper: §3 list-decoding
bounds feed into the list-decoding challenge directly, and §4 / §5 results bound `ε_mca`
either above (for the upper-bound direction) or below (for the lower-bound direction).
-/

namespace ProximityGap

open scoped NNReal

universe u

/-- **ABF26 §1 Grand MCA Challenge.**

There exists a maximal `δ*_C ∈ [0, 1]` such that `ε_mca(C, δ*_C) ≤ ε*` and the bound fails
strictly above `δ*_C`. The paper poses this for `C := RS[F, L, k]` with `ρ(C)` in a
specific small set and `ε* = 2^(-128)`; in Lean we leave `C` and `ε*` generic and
specialise at the call site.

Resolution would require either constructing an explicit `δ*_C` witness with the bound and
maximality, or proving no such `δ*_C` exists for some parameter regime. Both directions
are open at the time of the paper. -/
def grandMCAChallenge {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C : Submodule F (ι → F)) (ε_star : ℝ≥0) : Prop :=
  ∃ δ_C_star : ℝ≥0,
    δ_C_star ≤ 1 ∧
    epsMCA (F := F) (A := F) ((C : Set (ι → F))) δ_C_star ≤ (ε_star : ENNReal) ∧
    ∀ δ : ℝ≥0, δ_C_star < δ → δ ≤ 1 →
      epsMCA (F := F) (A := F) ((C : Set (ι → F))) δ > (ε_star : ENNReal)

/-- **ABF26 §1 Grand List Decoding Challenge.**

There exists a maximal `δ*_C ∈ [0, 1]` such that `|Λ(C^≡m, δ*_C)| ≤ ε* · |F|` and the
bound fails strictly above `δ*_C`. The paper poses this for `C := RS[F, L, k]` with
`ρ(C)` in a specific small set, constant interleaving parameter `m`, and `ε* = 2^(-128)`.

`|Λ(C^≡m, δ)|` is the maximised list size from `ABF26-D2.8`. The bound `ε* · |F|` is read
in `ENNReal` to handle the `Lambda = ⊤` edge case uniformly. -/
def grandListDecodingChallenge {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) : Prop :=
  ∃ δ_C_star : ℝ≥0,
    δ_C_star ≤ 1 ∧
    (ListDecodable.Lambda (C^⋈ (Fin m)) (δ_C_star : ℝ) : ENNReal) ≤
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) ∧
    ∀ δ : ℝ≥0, δ_C_star < δ → δ ≤ 1 →
      (ListDecodable.Lambda (C^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
        ((ε_star : ENNReal) * (Fintype.card F : ENNReal))

end ProximityGap
