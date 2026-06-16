/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import ArkLib.Data.CodingTheory.ProximityGap.MCAGenerator
import Mathlib

/-!
# Proximity Generators fundamental definitions

Define the fundamental concepts for different types of generators functions used in coding theory.

## Main Definitions

-

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BCGM25]. Full paper : https://eprint.iacr.org/2025/2051}
-/

open unitInterval NNReal ENNReal CoreDefinitions LinearTransformations
open scoped ProbabilityTheory


variable {ι : Type} [Fintype ι]
         {F : Type} [Field F] [Fintype F]
        --  {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ']
        --  {S : Type} [Fintype S]


noncomputable instance {ℓ : Type} [Fintype ℓ] : Fintype (ℓ → F) := Fintype.ofFinite (ℓ → F)

-- def badSeed {s : ℕ} (G : Generator (Fin s → F) (Fin (s + 1)) F) (LC : LinearCode ι F)
--   (U : Fin (s + 1) → (ι → F)) (γ : I) : Type :=
--   {x : Fin s → F // ∃ y : Fin s → F, (CoreDefinitions.IsMCA G LC y U γ) ∧ x = y}

def badSeed {s : ℕ} (LC : LinearCode ι F) (U : Fin (s + 1) → (ι → F)) (γ : I) : Type :=
  {x : Fin s → F // ∃ y : Fin s → F,
                    (CoreDefinitions.IsMCA (AffineSpaceGenerator F s) LC y U γ) ∧ x = y}

noncomputable def badSeedSet {ι : Type} [Fintype ι]
  {s : ℕ} (LC : LinearCode ι F) (U : Fin (s + 1) → (ι → F))
  (γ : I) (B : badSeed LC U γ) (h : CoreDefinitions.IsMCA (AffineSpaceGenerator F s) LC (B.1) U γ)
      : Finset ι :=
  Classical.choose h

def quotientOfBadSeedSet (LC : Submodule F (ι → F)) (T : Finset ι) :=
  (T → F) ⧸ LinearCode.projectedCode_submod LC T

/-- Lemma 7.1. in [BCGM25]. -/
theorem AffineLine_MCA_AffineSpaceMCA {ℓ : ℕ} (ε_mca : I → ℝ) (LC : LinearCode ι F)
(hGMCA : IsMCAGenerator (AffineLineGenerator F) ε_mca LC) :
  let a := (1 - 1 / Fintype.card F : ℝ)
  let ε_mca' := a • ε_mca
  IsMCAGenerator (AffineSpaceGenerator F ℓ) ε_mca' LC := by sorry
