/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.ProofSystem.ToyProblem.Definitions

/-!
# Toy problem soundness bounds (ABF26 §6)

Statement-layer for the §6 soundness bounds that do **not** depend on a
formal protocol object. The three protocol-level soundness lemmas
(`L6.6`, `L6.8`, `L6.10`) live alongside the protocol definitions in
`ToyProblem/Spec/General.lean` (C6.2) and
`ToyProblem/Spec/SimplifiedIOR.lean` (C6.9).

Items in this file:

* `ToyProblem.additive_code_supports_erasure_correction_grs12`
   — Lemma 6.5 [GRS12]: every additive code supports erasure correction
   with correction time `O((s · n)^3)`.

* `ToyProblem.simplified_iop_soundness_listDecoding_lb`
   — Lemma 6.12 [ABF26]: list-decoding-based lower bound on the
   soundness error of the simplified IOR `T'[C, t]` (Construction 6.9).
   Uses Claim B.1 via `Probability.exists_large_image_of_pairwise_collision_bound`.

* `ToyProblem.simplified_iop_soundness_ca_lb`
   — Lemma 6.13 [ABF26]: correlated-agreement-based lower bound on the
   soundness error of `T'[C, t]`.

All three are admitted as tagged sorries: L6.5 is a paper-cited
classical result; L6.12 and L6.13 are stated in coding-theory form
(direct cardinality bounds on `winningSet`) — their protocol-level
reading bounds the soundness of `ToyProblem.SimplifiedIOR.reduction`
from below.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
* [Guruswami, V., Rudra, A., Sudan, M., *Essential Coding Theory*][GRS12]
-/

namespace ToyProblem

open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- **Lemma 6.5 of [ABF26]** (= [GRS12]).

Every `F`-additive code `C : F^k → (F^s)^n` supports erasure correction
(in the sense of `SupportsErasureCorrection`) with correction time
`O((s · n)^3)`. Equivalently: the predicate
`SupportsErasureCorrection C ecor` holds for some
`ecor ≤ K · (s · n)^3`. We state the more permissive
"some `ecor` works" form here; pinning down the constant `K` requires
modelling the encoder concretely.

Admitted as an external result. -/
theorem additive_code_supports_erasure_correction_grs12
    (C : Set (ι → F)) :
    ∃ ecor : ℕ, SupportsErasureCorrection C ecor := by
  -- ABF26-L6.5; external admit [GRS12]. Polynomial-time erasure-correction
  -- algorithm via Gaussian elimination on the parity-check matrix of any
  -- additive code (cf. Guruswami-Rudra-Sudan, *Essential Coding Theory*).
  sorry

omit [DecidableEq F] in
/-- **Lemma 6.12 of [ABF26]** (list-decoding lower bound on the simplified IOR).

Coding-theory form: if `|F| > binomial(|Λ(C^{≡2}, δ)|, 2)`, then there
exist witnesses `(v, μ_1, μ_2, f_1, f_2)` with `(f_1, f_2)` lying outside
the relaxed relation `R̃_{C,δ}^2`, for which the winning challenge set
`Ω^{f_1,f_2}_{v,μ_1,μ_2}` (Definition 6.11) has at least
`|Λ(C^{≡2}, δ)| · |F| / (|F| + |Λ(C^{≡2}, δ)| - 1)` elements.

The protocol-level reading: the soundness error of the simplified IOR
`T'[C, t]` (Construction 6.9, `ToyProblem.SimplifiedIOR.reduction`) is
at least `|Λ(C^{≡2}, δ)| / (|F| + |Λ(C^{≡2}, δ)| - 1)`.

## Proof recipe (ABF26 §6.4.1, with B.1 now machine-checked)

The bound `N · F / (F + N − 1)` (writing `N := |Λ(C^{≡2}, δ)|`,
`F := |F|`) is exactly the conclusion of Claim B.1 specialised to
`|S| = N`, `|T| = F`, `ε = 1/F`:
```
N / (1 + (N − 1) · (1/F)) = N · F / (F + N − 1)
```
so the proof skeleton is:

1. **Build the list.** Enumerate `Λ(C^{≡2}, δ)` as `λ : Fin N → ι → F × ι → F`,
   pairs `(W₀(λ), W₁(λ))` of `δ`-close codewords in `C` (paper writes
   `(v_0(λ), v_1(λ))`). Pick any `v ∈ F^k` and define the "evaluation"
   function `φ_v : Fin N → F × F` by `λ ↦ (⟨W₀(λ), v⟩, ⟨W₁(λ), v⟩) — μ`-pair shape.

2. **Pairwise collision bound.** For `λ ≠ λ'` with `(W₀(λ), W₁(λ)) ≠
   (W₀(λ'), W₁(λ'))`, the linear functional `⟨·, v⟩` collides on the
   distinct difference vector with probability `1/F` over a uniform
   `v ←$ F^k`. This is the in-tree predicate
   `Pr_{ let v ←$ᵖ (Fin k → F) }[(decide (φ_v λ = φ_v λ') : Prop)] ≤ 1/F`.
   Unfold via [`ProbabilityTheory.Pr_decide_eq_tsum_indicator`] from
   [`Probability/Notation.lean`](../../Data/Probability/Notation.lean).

3. **Apply B.1.** Feed steps 1 + 2 into
   [`Probability.exists_large_image_of_pairwise_collision_bound`]
   (`ArkLib/Data/Probability/Combinatorial.lean`) to obtain a
   `v* ∈ F^k` whose induced `φ_{v*}` has image size at least
   `N · F / (F + N − 1)` in `F × F`.

4. **Convert to winning set.** Each distinct `(μ₁, μ₂) ∈ image φ_{v*}`
   corresponds to a `γ ∈ winningSet` via the list-decoding bijection
   (paper §6.4.1 — `μ_i = ⟨W_i(λ), v*⟩` for some `λ`, and the constraint
   `μ_new = μ₁ + γ · μ₂` admits a unique `γ` per such pair under the
   `|F| > binom(N, 2)` regime). The witness `(v*, μ₁, μ₂, f₁ := W₀,
   f₂ := W₁)` for some chosen `λ₀ ∈ Λ` exits the proof.

Admitted as an external result (proved in ABF26 §6.4.1); steps 2-3 are
now in scope thanks to B.1's closure (2026-05-20). -/
theorem simplified_iop_soundness_listDecoding_lb {k : ℕ}
    (C : Set (ι → F)) (δ : ℝ≥0) (_hδ_pos : (0 : ℝ≥0) < δ) (_hδ_lt : δ < 1)
    (_hF : (Fintype.card F : ℝ) >
      ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat).choose 2) :
    ∃ (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F),
      ((winningSet C δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) ≥
        (((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)
            * Fintype.card F)
          / (Fintype.card F
              + ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ) - 1) := by
  -- ABF26-L6.12 external admit [ABF26 §6.4.1].
  sorry

/-- **Lemma 6.13 of [ABF26]** (correlated-agreement lower bound on the simplified IOR).

Coding-theory form: there exist `(v, μ_1, μ_2, f_1, f_2)` with
`(f_1, f_2)` outside the relaxed relation `R̃_{C,δ}^2` whose winning
challenge set has size at least `ε_ca(C, δ) · |F|`.

Protocol-level reading: the soundness error of the simplified IOR
`T'[C, t]` (Construction 6.9) is at least `ε_ca(C, δ)`.

Proof sketch: take `f_1, f_2` maximising the CA error; then
`f_1 + γ·f_2` is `δ`-close to `C` precisely on a set `S` of size
`ε_ca · |F|`, and `S` is contained in the winning set
`Ω^{f_1,f_2}_{0^k, 0, 0}` of Definition 6.11.

Admitted as an external result (proved in ABF26 §6.4.2). The bound is in
terms of `ε_ca` (correlated agreement) rather than `ε_mca` (mutual
correlated agreement); the latter would be qualitatively stronger but no
attack reaching `ε_mca > ε_ca` is currently known (Remark 6.14). -/
theorem simplified_iop_soundness_ca_lb {k : ℕ}
    (C : Set (ι → F)) (δ : ℝ≥0) (_hδ_pos : (0 : ℝ≥0) < δ) (_hδ_lt : δ < 1) :
    ∃ (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F),
      ((winningSet (k := k) C δ v μ₁ μ₂ f₁ f₂).ncard : ENNReal)
        ≥ epsCA (F := F) (A := F) C δ δ * (Fintype.card F : ENNReal) := by
  -- ABF26-L6.13 external admit [ABF26 §6.4.2].
  sorry

end ToyProblem
