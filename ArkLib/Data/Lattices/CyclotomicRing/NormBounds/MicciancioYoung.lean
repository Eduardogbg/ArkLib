/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.Basic

/-!
# The Micciancio/Young Product Norm-Growth Bound

The Young/Micciancio inequality `‖(c·d)·v‖₂² ≤ ‖d‖₁² · ‖c·v‖₂²` over the power-of-two
negacyclic convolution (`φ = X^{2^α} + 1`, `powTwoCyclotomic α`) with centered
representatives: scaling an already-`c`-scaled vector by a further ring element `d` of
bounded centered `ℓ₁` norm grows the squared `ℓ₂` norm by at most `κ²`.

The statement is pinned to `powTwoCyclotomic α`: the per-entry product bound
`‖d·w‖₂ ≤ ‖d‖₁·‖w‖₂` rests on multiplication-by-`X` being an `ℓ₂`-isometry on the
coefficient vector, which holds for the cyclic/negacyclic rings `X^n ∓ 1` of [Mic07] but
*fails* for a general cyclotomic `Φ_m` (e.g. in `ℤ[X]/(X²+X+1)`, `‖X·X‖₂ = √2 > ‖X‖₁·‖X‖₂`).
Phrasing this for an arbitrary `Φ` would therefore be unsound.

This is one of the two unproven lemmas for the Greyhound [NS24] / Hachi [NOZ26]
weak-binding argument. The paper proof is in [Mic07, Lemma 2]: discrete Cauchy–Schwarz over
the negacyclic convolution, together with minimality of the centered representative, gives the
product norm inequality `‖fg‖ ≤ ‖f‖₁·‖g‖`.

## References

* [Micciancio, D., *Generalized Compact Knapsacks, Cyclic Lattices, and Efficient One-Way
    Functions*][Mic07]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open scoped BigOperators

namespace ArkLib.Lattices.CyclotomicModulus

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] (α : ℕ)

/-- The power-of-two ("Hachi") cyclotomic modulus `X^{2^α}+1` over `ZMod q`. -/
local notation "Φ" => (powTwoCyclotomic (R := ZMod q) α)

/-- **Micciancio/Young product bound.** Over the power-of-two cyclotomic modulus
`powTwoCyclotomic α` (`φ = X^{2^α}+1`), scaling an already-`c`-scaled vector by a further
ring element `d` of bounded centered `ℓ₁` norm grows the squared `ℓ₂` norm by at most `κ²`
(the honest Young/Micciancio inequality `‖(c·d)·v‖₂² ≤ ‖d‖₁² · ‖c·v‖₂²` over the negacyclic
convolution with centered representatives; discrete Cauchy–Schwarz, deferred). -/
theorem scalarVecMul_mul_l2NormSq_le {cols : ℕ} (c d : Rq Φ) (v : PolyVec (Rq Φ) cols)
    {κ βSq : ℕ} (hd : Rq.l1Norm Φ d ≤ κ)
    (hv : vecL2NormSq Φ (scalarVecMul c v) ≤ βSq) :
    vecL2NormSq Φ (scalarVecMul (c * d) v) ≤ scalarVecMulMulL2NormSqBound κ βSq := by
  sorry

end ArkLib.Lattices.CyclotomicModulus
