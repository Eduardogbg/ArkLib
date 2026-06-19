/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Erasure
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Toy problem definitions (ABF26 §6)

Statement-layer definitions for the toy problem of ABF26 §6 — the small
protocol whose analysis motivates mutual correlated agreement (MCA) over
mere correlated agreement (CA), and which doubles as a textbook example of
the complexities of real list-decoding-based protocol analyses.

This file is the code-theoretic foundation:

* `ToyProblem.relationFor` — Definition 6.1, the toy problem relation
  `R_C^ℓ` over a code with encoding `encode` and constraint shape `ℓ`.
* `ToyProblem.relaxedRelationFor` — Definition 6.3, the `δ`-relaxed version
  used as the soundness target.
* Definition 6.4 (erasure-correction predicate) is realised directly by
  `CodingTheory.SupportsErasureCorrection` in
  [`ArkLib/Data/CodingTheory/Erasure.lean`](../../Data/CodingTheory/Erasure.lean)
  (the predicate is generic across proof systems; use the in-tree name
  directly rather than a paper-shape wrapper).
* `ToyProblem.winningSetFor` — Definition 6.11, the set of "winning"
  challenges `γ` for the simplified IOR attack of §6.4.

## Why the encoding is pinned (and the existential family was deleted)

The paper's code is **its encoding**: ABF26 writes `C : F^k → (F^s)^n` for an
`F`-additive code (`\AdditiveCodeDefinition`) and "interchangeably consider[s]
a code `C` as a subset … and as the injective map" (canonical `.tex` ~1133).
The relation `R_C^ℓ` therefore constrains the pre-image under *the code's
fixed encoding*, not under some encoding with the same image.

An earlier in-tree variant (`relation`/`relaxedRelation`/`winningSet`)
quantified the encoding **existentially** (`∃ encode, range ⊆ C ∧ …`). That
form is defectively permissive: an adversary can satisfy the relaxed relation
at a target `(μ₁, μ₂)` by reparameterising the linear constraint through a
*different* linear encoding with the same image, so for linear `C` with
`k ≥ 2` the violation conjunct of the §6.4 attacks (L6.12/L6.13) becomes
unprovable (and the Definition-6.11 soundness supremum collapses). The
existential family was deleted (2026-06-10) once all users — the §6.4 attack
lemmas in `SoundnessBounds.lean` and the leaderboard in `Leaderboard.lean` —
migrated to the fixed-encoding definitions below; the protocol layer
(`Spec/General.lean`, `Spec/SimplifiedIOR.lean`) had already migrated for the
same faithfulness reason (completeness fails under the existential form).

Protocol-level items (Construction 6.2, Lemmas 6.6 / 6.8, Construction
6.9, Lemma 6.10) live in `ToyProblem/Spec/General.lean` and are stated
over ArkLib's `OracleReduction/` machinery, following the conventions
of `ProofSystem/Fri/Spec/` and `ProofSystem/Sumcheck/Spec/`. Soundness
bounds (L6.12, L6.13) live in `ToyProblem/SoundnessBounds.lean`; L6.5
(erasure correction) is proven in `Data/CodingTheory/Erasure.lean`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
* [Guruswami, V., Rudra, A., Sudan, M., *Essential Coding Theory*][GRS25]
-/

namespace ToyProblem

open Code InterleavedCode
open scoped NNReal

variable {ι F A : Type*} [Fintype ι] [Field F] [AddCommGroup A] [Module F A]

/-- **Definition 6.1 of [ABF26]** (toy problem relation `R_C^ℓ`).

Given a code presented as its `F`-linear encoding
`encode : (Fin k → F) →ₗ[F] (ι → A)` over an alphabet `A` that is an
`F`-module (the paper writes `C : F^k → (F^s)^n` and treats the code as the
injective map, `.tex` ~1133 — `A = F^s` is the folded alphabet, `A = F` the
scalar `s = 1` case), a constraint shape `(ℓ, k)`, a linear-constraint vector
`v : Fin k → F`, and constraint values `μ : Fin ℓ → F`, the toy problem
relation pairs an input `((v, μ), W)`, where `W : Fin ℓ → ι → A` is a stack of
`ℓ` words, with the witness "underlying message matrix" `M : Fin ℓ → Fin k → F`
such that:

  * each row `W i` is the codeword `encode (M i)` — the pre-image is taken
    under **the code's fixed encoding** (see the module docstring for why an
    existential encoding is unfaithful);
  * the linear constraint `(M · v) i = μ i` holds for every `i`.

This is what the paper calls "constrained codes". -/
def relationFor {k ℓ : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → A))
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → A) : Prop :=
  ∃ M : Fin ℓ → Fin k → F, (∀ i, W i = encode (M i)) ∧ ∀ i, ∑ j, M i j * v j = μ i

/-- **Definition 6.3 of [ABF26]** (relaxed toy problem relation
`R̃_{C,δ}^ℓ`, with the code's encoding pinned — cf. `relationFor`).

The relaxed relation only requires that the input word stack `W` is
`δ`-close (in interleaved Hamming distance) to a valid instance `W*`
of `relationFor encode v μ`. This is both necessary (the verifier in the IOR
only reads a few entries of `W`) and sufficient (for downstream uses)
for soundness with respect to `δ`. -/
def relaxedRelationFor {k ℓ : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → A) : Prop :=
  ∃ Wstar : Fin ℓ → ι → A, relationFor encode v μ Wstar ∧
    -- Interleaved Hamming distance between the two word stacks is at
    -- most `δ`: at least `(1 - δ) · |ι|` coordinates agree on every row.
    ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
      ∀ i, ∀ j ∈ S, W i j = Wstar i j

-- Paper Definition 6.4 (erasure-correction predicate) is realised by
-- `CodingTheory.SupportsErasureCorrection` directly; use that name (no
-- paper-shape alias wrapper — see Definitions.lean module docstring).

/-- **Definition 6.11 of [ABF26]** (winning set `Ω^{f_1, f_2}_{v, μ_1, μ_2}`,
with the code's encoding pinned — cf. `relationFor`).

For the simplified IOR `T'[C, t]` of §6.4 (Construction 6.9), this is the
set of challenges `γ ∈ F` for which the "new instance" output by the
verifier — `(v, μ_1 + γ·μ_2, f_1 + γ·f_2)` — lies in the relaxed
relation `R̃_{C,δ}^1`. The soundness error of `T'` is then exactly
`max_{x,y} |Ω^y_x| / |F|` over inputs `(x, y)` whose original instance
`(v, μ_1, μ_2)` violates `R̃_{C,δ}^2` (realised as
`ToyProblem.winningSetSoundness` in `Leaderboard.lean`). -/
def winningSetFor {k : ℕ} (encode : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → A) : Set F :=
  { γ | relaxedRelationFor (ℓ := 1) encode δ v
         (fun _ ↦ μ₁ + γ * μ₂) (fun _ j ↦ f₁ j + γ • f₂ j) }

end ToyProblem
