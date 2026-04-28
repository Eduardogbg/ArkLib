/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import Mathlib.Data.Rat.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib

/-!
# Proximity Generators fundamental definitions

Define the fundamental concepts for different types of generators functions used in coding theory.

## Main Results



## References

* [Guruswami, V., Rudra, A., Sudan M., *Essential Coding Theory*, online copy][GRS25]
* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BSGM25]. Full paper : https://eprint.iacr.org/2025/2051}
-/

section

namespace LinearTransformations

open NNReal ENNReal unitInterval LinearCode CoreDefinitions
open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F] [Fintype F]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ']
         {S : Type}

def hasPseudoLeftInverse [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F) : Prop :=
 ∃ B : Matrix ℓ' ℓ F, B * A = 1

noncomputable def pseudoInverse [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F) (hA : hasPseudoLeftInverse A) :
  Matrix ℓ' ℓ F := Classical.choose hA

def isPseudoLeftInverse [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F) (B : Matrix ℓ' ℓ F) : Prop :=
    B * A = 1

lemma pseudoLeftInverse' [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F)
  (hA : Matrix.colRank A = Fintype.card ℓ') :
  let B :=  (A.transpose * A)⁻¹ * (A.transpose)
  (isPseudoLeftInverse A B) := by
  sorry

lemma pseudoLeftInverse [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F)
  (hA : IsUnit (A.transpose * A).det) :
  isPseudoLeftInverse A ((A.transpose * A)⁻¹ * A.transpose) := by
  unfold isPseudoLeftInverse
  simp only [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ hA

/-- Generator `G'` inside Lemma 4.1 [BSGM25] -/
def pseudoInvNewGen [DecidableEq ℓ']
{S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F)
(A : Matrix ℓ ℓ' F) : Generator S ℓ' F := fun x ↦ (Matrix.vecMul (G x) A)

--- Lemma 4.1

/-
If `B * A = 1` then `U j = ∑ k, B j k • (A * U) k` for any matrix `U`.
-/
lemma left_inv_recover [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F)
    (B : Matrix ℓ' ℓ F) (hBA : B * A = 1) (U : ℓ' → (ι → F)) (j : ℓ') :
    U j = ∑ k : ℓ, B j k • (fun k' i => ∑ l : ℓ', A k' l * U l i) k := by
  ext i;
  simp +decide [ Matrix.mul_apply, mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul, ← Matrix.ext_iff ] at hBA ⊢;
  simp_all +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← Finset.sum_comm, Matrix.one_apply ]

/-
Projection commutes with finite sums and scalar multiplication.
-/
lemma projectedWord_sum (T : Finset ι)
    (a : ℓ → F) (w : ℓ → (ι → F)) :
    projectedWord (∑ k, a k • w k) T = ∑ k, a k • projectedWord (w k) T := by
  funext x; simp [Set.restrict];
  convert Finset.sum_apply _ _ _

-- /-
-- Key step: `IsMCA` for the pseudo-inverse generator implies `IsMCA` for the original.
-- -/
-- lemma isMCA_pseudoInvNewGen_imp [DecidableEq ℓ']
--     {S : Type} [Nonempty S] [Fintype S]
--     (G : Generator S ℓ F) (A : Matrix ℓ ℓ' F) (B : Matrix ℓ' ℓ F) (hBA : B * A = 1)
--     (LC : LinearCode ι F) (x : S) (U : ℓ' → (ι → F)) (γ : I) :
--     IsMCA (pseudoInvNewGen G A) LC x U γ →
--     IsMCA G LC x (fun k i => ∑ l : ℓ', A k l * U l i) γ := by
--   intro h;
--   obtain ⟨ T, hT₁, hT₂, j, hj ⟩ := h;
--   refine' ⟨ T, hT₁, _, _ ⟩;
--   · convert hT₂ using 1;
--     unfold pseudoInvNewGen; ext; simp +decide [ Matrix.vecMul, dotProduct ] ;
--     exact?;
--   · contrapose! hj;
--     have := left_inv_recover A B hBA U j;
--     rw [ this ];
--     convert LinearCode.projectedCode_linearCombination LC T ( fun k => B j k ) ( fun k => ( fun k' i => ∑ l, A k' l * U l i ) k|[T] ) hj using 1;
--     exact?

-- /-- Lemma 4.1 [BSGM25] -/
-- lemma pseudoinverseGen [DecidableEq ℓ']
--     {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (ε_mca : I → I)
--     (LC : LinearCode ι F) (hG : IsMCAGenerator G ε_mca LC) (A : Matrix ℓ ℓ' F)
--     (hA : hasPseudoLeftInverse A) :
--     IsMCAGenerator (pseudoInvNewGen G A) ε_mca LC := by
--   obtain ⟨B, hBA⟩ := hA
--   intro U γ
--   have key : ∀ x, IsMCA (pseudoInvNewGen G A) LC x U γ →
--       IsMCA G LC x (fun k i => ∑ l : ℓ', A k l * U l i) γ :=
--     fun x => isMCA_pseudoInvNewGen_imp G A B hBA LC x U γ
--   calc uniformProb (fun x => IsMCA (pseudoInvNewGen G A) LC x U γ)
--       ≤ uniformProb (fun x => IsMCA G LC x (fun k i => ∑ l, A k l * U l i) γ) :=
--         uniformProb_mono key
--     _ ≤ ENNReal.ofReal (ε_mca γ) := hG _ γ

/-- Lemma 4.1 [BSGM25] -/
lemma pseudoinverseGen [DecidableEq ℓ']
{S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (ε_mca : I → I) (LC : LinearCode ι F)
(hG : IsMCAGenerator G ε_mca LC) (A : Matrix ℓ ℓ' F) (hA : hasPseudoLeftInverse A) :
IsMCAGenerator (pseudoInvNewGen G A) ε_mca LC := by sorry

/-- Generator `G'` inside Corollary 4.2 [BSGM25] -/
def neSubsetGen
{S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (κ : Set ℓ)
: Generator S κ F := fun x ↦ Set.restrict κ (G x)

-- Corollary 4.2

/-- Extend a function on a subset to the full type by zero. -/
noncomputable def extendByZero (κ : Set ℓ) [DecidablePred (· ∈ κ)]
    (U : κ → (ι → F)) : ℓ → (ι → F) :=
  fun j i => if h : j ∈ κ then U ⟨j, h⟩ i else 0

/-
Key step: `IsMCA` for the subset generator implies `IsMCA` for the original.
-/
lemma isMCA_neSubsetGen_imp [DecidableEq ℓ]
    {S : Type} [Nonempty S] [Fintype S]
    (G : Generator S ℓ F) (κ : Set ℓ) [DecidablePred (· ∈ κ)] [Fintype κ]
    (LC : LinearCode ι F) (x : S) (U : κ → (ι → F)) (γ : I) :
    IsMCA (neSubsetGen G κ) LC x U γ → IsMCA G LC x (extendByZero κ U) γ := by
  unfold IsMCA;
  simp +decide [ Matrix.vecMul, extendByZero ];
  intro T hT hT' x hx hx'; use T; simp_all +decide [ Matrix.vecMul, projectedWord ] ;
  refine' ⟨ _, x, _ ⟩;
  · convert hT' using 1;
    ext i; simp +decide [ Matrix.vecMul, neSubsetGen, extendByZero ] ;
    rw [ dotProduct, dotProduct ];
    rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun x : κ => x.val ) Finset.univ ) ) ];
    · rw [ Finset.sum_image ] <;> aesop;
    · aesop;
  · unfold extendByZero; aesop;


/-- Corollary 4.2 [BSGM25]-/
lemma generatorSubset [DecidableEq ℓ']
{S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (ε_mca : I → I) (LC : LinearCode ι F)
(hG : IsMCAGenerator G ε_mca LC) (κ : Set ℓ) (hκ : Nonempty κ) :
  IsMCAGenerator (neSubsetGen G κ) ε_mca LC := by
  classical
  intro U γ
  calc uniformProb (fun x => IsMCA (neSubsetGen G κ) LC x U γ)
      ≤ uniformProb (fun x => IsMCA G LC x (extendByZero κ U) γ) :=
        uniformProb_mono (fun x => isMCA_neSubsetGen_imp G κ LC x U γ)
    _ ≤ ENNReal.ofReal (ε_mca γ) := hG (extendByZero κ U) γ


end LinearTransformations

end
