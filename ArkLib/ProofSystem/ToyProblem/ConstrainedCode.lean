/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.SoundnessBounds

/-!
# The toy-protocol soundness experiment is the MCA experiment of the constrained code

This file formalizes the observation (G. Fenzi) that the soundness experiment of
the §6 toy reduction `T[C, t]` is captured by the mutual-correlated-agreement
(MCA) experiment of the **constrained code** — the code obtained by adjoining the
extra linear constraint `⟨m, v⟩ = μ` to `C`. Concretely we prove a one-directional
bound (`toy γ-event ≤ ε_mca(constrained code)`); see the *caveat* below on why this
is an upper bound rather than the equality the observation suggests.

Concretely, for the scalar alphabet `A = F` we adjoin the constraint value
`⟨m, v⟩` as one extra coordinate (indexed by `Unit`):

  `constrainedCode enc v := range (m ↦ Sum.elim (enc m) (fun _ ↦ ⟨m, v⟩)) ⊆ (ι ⊕ Unit) → F`.

This keeps the code `F`-additive (it is the range of a linear map), turns the
affine constraint into an *exact* coordinate match, and makes the folded target
`μ₁ + γ·μ₂` the value of the line `f₁ + γ·f₂` at the extra coordinate.

The main result, `gamma_transition_prob_le_constrained`, shows that the
γ-round transition probability of the toy reduction (the event of
`ToyProblem.gamma_transition_prob_le` / the private `gammaEvent`) is bounded by

  `ε_mca(constrainedCode enc v, δ)`,

a **single** MCA quantity in which the linear constraint is internalized as a code
coordinate, so no separate `|Λ|/|F|` list-size term appears (compare the paper's
split bound `ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|` proved by
`ToyProblem.gamma_transition_prob_le`).

The proof is purely structural — no coding-theory external is invoked — so it is
sorry-free: the toy bad event implies `mcaEvent (constrainedCode enc v) δ`, taking
the agreement set `S' = S ∪ {extra coordinate}`; the `+1` slack from the extra
coordinate absorbs the `(1-δ)` factor, so the *same* `δ` works with no proximity
rescaling.

## Caveat: this is an upper bound, not an equality or a proven improvement

The result is `toy γ-event ≤ ε_mca(C_v, δ)`, established by a single `le_iSup`.
Two things it does **not** establish, and should not be read to:

* **Not an equality.** `mcaEvent` (hence `ε_mca`) quantifies over *all* agreement
  sets `S'` of size `≥ (1-δ)(n+1)`, including sets that *omit* the extra `Unit`
  coordinate. On such an `S'` the constraint is never tested, so that branch
  reduces to a plain base-code-`C` MCA bad event. Hence `ε_mca(C_v, δ)`
  *over-counts*: it is `≥ ε_mca(C, δ)` and is only an upper bound on the toy
  soundness, not equal to it. Faithfully capturing the observation as an
  *equality* would require a **constraint-pinned** MCA variant (requiring
  `S' ∋` the extra coordinate), which is not the stock `ε_mca`.

* **Not a proven improvement.** Whether `ε_mca(C_v, δ) ≤ ε_mca(C, δ) + |Λ|/|F|`
  (i.e. whether this single quantity is tighter than / equal to the paper's split
  bound, rather than looser) is **not** proved here, and is non-trivial: the
  `|Λ|/|F|` control on the constraint-pinned part of `ε_mca(C_v)` would itself
  need the counting argument of `gamma_transition_prob_le`. Treat the relationship
  to the paper bound as open.

## Scope

This is stated for the **scalar** case `A = F` (the IRS leaderboard setting),
where the `F`-valued constraint coordinate lives in the same alphabet as the
codeword. The general `F`-module alphabet `A` (folded RS, `A = Fin s → F`) would
require the constrained code to live in `(ι → A) × F`, i.e. a generalization of
the `ε_mca` ambient away from the uniform `ι → A` — left as future work.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
-/

namespace ToyProblem

open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

/-- **The constrained code** (scalar alphabet `A = F`).

Adjoin the linear-constraint value `⟨m, v⟩ = ∑ j, m j * v j` as one extra
coordinate (indexed by `Unit`), so the affine constraint becomes an exact
coordinate match and the code stays `F`-additive (it is the range of a linear
map). Its MCA error upper-bounds the toy-protocol soundness experiment
(`gamma_transition_prob_le_constrained`; see that lemma's caveat — the bound is
one-directional, not an equality). -/
def constrainedCode {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → F)) (v : Fin k → F) :
    Set ((ι ⊕ Unit) → F) :=
  Set.range (fun m : Fin k → F ↦ Sum.elim (enc m) (fun _ ↦ ∑ j, m j * v j))

/-- **The toy-protocol γ-round soundness experiment is bounded by the MCA error of
the constrained code.** For an instance `(v, μ₁, μ₂, f₁, f₂)` of the toy reduction
admitting **no** relaxed-relation witness (`hNoWit`), the probability over a
uniform challenge `γ` that some message `m` satisfies the post-`γ` knowledge
state is at most `ε_mca(constrainedCode enc v, δ)`.

This is the constrained-code reformulation of `ToyProblem.gamma_transition_prob_le`
(`A = F`): the linear constraint is internalized as a code coordinate, so the bound
is a single MCA quantity with no separate `|Λ(C^{≡2}, δ)| / |F|` term.

**Caveat (one-directional).** This is an upper bound, established by a single
`le_iSup`. It is *not* an equality (`ε_mca C_v` over-counts: `mcaEvent` admits
agreement sets omitting the constraint coordinate, which reduce to base-code-`C`
MCA events), and it is *not* shown to be `≤` the paper's split bound `ε_mca(C,δ) +
|Λ|/|F|`. See the module docstring's caveat section.

Sorry-free and external-free: the toy bad event implies
`mcaEvent (constrainedCode enc v) δ`, witnessed by the agreement set
`S' = S ∪ {extra coordinate}`. -/
theorem gamma_transition_prob_le_constrained {k : ℕ} [DecidableEq ι]
    (enc : (Fin k → F) →ₗ[F] (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F)
    (hNoWit : ¬ ∃ M : Fin 2 → (Fin k → F),
      (∀ i : Fin 2, ∑ j, M i j * v j = ![μ₁, μ₂] i) ∧
      ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
        ∀ i : Fin 2, ∀ j ∈ S, ![f₁, f₂] i j = enc (M i) j) :
    Pr_{let γ ← $ᵖ F}[∃ m : Fin k → F, (∑ j, m j * v j = μ₁ + γ * μ₂) ∧
        ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
          ∀ j ∈ S, f₁ j + γ • f₂ j = enc m j]
      ≤ epsMCA (F := F) (A := F) (constrainedCode enc v) δ := by
  classical
  set U₀ : (ι ⊕ Unit) → F := Sum.elim f₁ (fun _ ↦ μ₁) with hU₀
  set U₁ : (ι ⊕ Unit) → F := Sum.elim f₂ (fun _ ↦ μ₂) with hU₁
  refine le_trans (Pr_le_Pr_of_implies ($ᵖ F) _
      (fun γ ↦ mcaEvent (constrainedCode enc v) δ U₀ U₁ γ) (fun γ hγ ↦ ?_)) ?_
  · -- The toy bad event implies the constrained code's MCA bad event.
    obtain ⟨m, hconstr, S, hScard, hagree⟩ := hγ
    set S' : Finset (ι ⊕ Unit) := insert (Sum.inr ()) (S.image Sum.inl) with hS'
    have hmem_inr : Sum.inr () ∈ S' := by rw [hS']; exact Finset.mem_insert_self _ _
    have hmem_inl : ∀ {j : ι}, j ∈ S → Sum.inl j ∈ S' := fun hj => by
      rw [hS']; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj)
    refine ⟨S', ?_, ⟨_, ⟨m, rfl⟩, ?_⟩, ?_⟩
    · -- Size: `(1-δ)·(n+1) ≤ |S|+1`, the `+1` slack absorbing the `(1-δ)` factor.
      have hcard_S' : S'.card = S.card + 1 := by
        rw [hS', Finset.card_insert_of_notMem (by simp),
          Finset.card_image_of_injective _ Sum.inl_injective]
      have hcard_univ : Fintype.card (ι ⊕ Unit) = Fintype.card ι + 1 := by
        rw [Fintype.card_sum, Fintype.card_unit]
      have e : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by rw [NNReal.coe_sub hδ]; simp
      rw [ge_iff_le, hcard_S', hcard_univ, ← NNReal.coe_le_coe, NNReal.coe_mul, e]
      push_cast
      nlinarith [hScard, NNReal.coe_nonneg δ]
    · -- Codeword agreement on `S'`: on `ι` by hypothesis, exact at the extra coordinate.
      intro i hi
      rw [hS', Finset.mem_insert, Finset.mem_image] at hi
      rcases hi with rfl | ⟨j, hjS, rfl⟩
      · simpa [hU₀, hU₁, smul_eq_mul] using hconstr
      · simpa [hU₀, hU₁] using (hagree j hjS).symm
    · -- No constrained-code pair agrees on `S'`: it would be a forbidden witness.
      rintro ⟨w₀, ⟨M₀, rfl⟩, w₁, ⟨M₁, rfl⟩, hag⟩
      refine hNoWit ⟨![M₀, M₁], ?_, S, hScard, ?_⟩
      · intro i
        fin_cases i
        · simpa [hU₀] using (hag (Sum.inr ()) hmem_inr).1
        · simpa [hU₁] using (hag (Sum.inr ()) hmem_inr).2
      · intro i j hj
        fin_cases i
        · simpa [hU₀] using ((hag (Sum.inl j) (hmem_inl hj)).1).symm
        · simpa [hU₁] using ((hag (Sum.inl j) (hmem_inl hj)).2).symm
  · -- `Pr[mcaEvent …] ≤ ε_mca` via `le_iSup` at the word stack `(U₀, U₁)`.
    unfold epsMCA
    exact le_iSup (fun u : WordStack F (Fin 2) (ι ⊕ Unit) ↦
      Pr_{let γ ← $ᵖ F}[mcaEvent (constrainedCode enc v) δ (u 0) (u 1) γ]) ![U₀, U₁]

end ToyProblem
