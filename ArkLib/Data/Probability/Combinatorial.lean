/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import ArkLib.Data.Probability.Notation

/-!
# Probabilistic combinatorics

Stand-alone probabilistic-combinatorics statements used elsewhere in ArkLib.
Currently this module hosts `exists_large_image_of_pairwise_collision_bound`,
which is Claim B.1 of [ABF26].

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
-/

namespace Probability

open Finset

/-- **Claim B.1 of [ABF26]** ("Omitted claim for Lemma 6.12").

Suppose `S, T` are finite sets and `Φ` is a distribution on functions `S → T`
such that for any distinct `x, y ∈ S`, the probability that a sample
`φ ← Φ` sends `x` and `y` to the same image is bounded by `ε`:
```
∀ x y ∈ S, x ≠ y → Pr_{φ ← Φ}[φ x = φ y] ≤ ε.
```
Then there exists some `φ` in the support of `Φ` whose image has cardinality
at least `|S| / (1 + (|S| − 1) · ε)`.

## Proof outline (from [ABF26] Appendix B)

Let `C_φ := { (x, y) ∈ Sym2 S : x ≠ y ∧ φ x = φ y }` be the set of distinct
colliding pairs under `φ`.

1. **Expected number of collisions.** By linearity of expectation,
   `E_{φ ← Φ}[|C_φ|] = Σ_{(x,y) ∈ Sym2 S, x ≠ y} Pr[φ x = φ y]
                     ≤ (|S| choose 2) · ε`.

2. **Counting collisions via fibers.** For every fixed `φ`,
   `|S| = Σ_{μ ∈ φ(S)} |φ⁻¹(μ)|` and each `μ ∈ φ(S)` contributes
   `(|φ⁻¹(μ)| choose 2)` colliding pairs, so
   `|C_φ| = ½(Σ_μ |φ⁻¹(μ)|² − |S|)`.

3. **Cauchy–Schwarz on fibers.**
   `(Σ_μ |φ⁻¹(μ)|)² ≤ (Σ_μ 1²) · (Σ_μ |φ⁻¹(μ)|²) = |φ(S)| · Σ_μ |φ⁻¹(μ)|²`,
   hence `|φ(S)| · (2 |C_φ| + |S|) ≥ |S|²` and thus
   `|φ(S)| ≥ |S|² / (2 |C_φ| + |S|)`.

4. **Jensen.** The function `x ↦ |S|² / (2 x + |S|)` is convex on `x ≥ 0`
   (`f''(x) = 8 |S|² / (2 x + |S|)^3 > 0`), so taking expectations,
   `E_{Φ}[|φ(S)|] ≥ |S|² / (2 E_{Φ}[|C_φ|] + |S|)
                  ≥ |S|² / (2 · (|S| choose 2) · ε + |S|)
                  = |S| / (1 + (|S| − 1) · ε)`.

5. **Existence by averaging.** Some `φ` in the support of `Φ` achieves at
   least the expectation, hence the claimed bound. -/
theorem exists_large_image_of_pairwise_collision_bound
    {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (Φ : PMF (S → T)) (ε : ℝ≥0)
    (hΦ : ∀ x y : S, x ≠ y → Pr_{ let φ ← Φ }[φ x = φ y] ≤ ε) :
    ∃ φ ∈ Φ.support, ((Finset.univ.image φ).card : ℝ≥0) ≥
      (Fintype.card S : ℝ≥0) / (1 + (Fintype.card S - 1) * ε) := by
  sorry -- ABF26-B.1; in-paper proof, deferred. Cauchy-Schwarz on fibers + Jensen on `x ↦ |S|²/(2x+|S|)` + averaging argument.

end Probability
