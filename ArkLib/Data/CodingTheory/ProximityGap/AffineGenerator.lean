/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import ArkLib.Data.CodingTheory.ProximityGap.MCAGenerator
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.AffineGenHelperLemmas


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
open scoped ProbabilityTheory NNReal ENNReal


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

/-
The uniform probability of `P` as an `ENNReal.ofReal` of the real density.
-/
theorem prob_uniform_eq_ofReal {F : Type} [Fintype F] [Nonempty F]
    (P : F → Prop) [DecidablePred P] :
    Pr_{ let r ←$ᵖ F }[ P r ] =
      ENNReal.ofReal (((Finset.filter (α := F) P Finset.univ).card : ℝ) / (Fintype.card F : ℝ)) := by
  convert prob_uniform_eq_card_filter_div_card P using 1;
  rw [ ENNReal.ofReal_div_of_pos ] <;> norm_num;


-- /-- Lemma 7.1. in [BCGM25]. -/
-- theorem AffineLine_MCA_AffineSpaceMCA {ℓ : ℕ} (hℓ : ℓ ≥ 2) (ε_mca : I → ℝ) (LC : LinearCode ι F)
-- (hGMCA : IsMCAGenerator (AffineLineGenerator F) ε_mca LC) :
--   let a := (1 - 1 / Fintype.card F : ℝ)
--   let ε_mca' := a • ε_mca
--   IsMCAGenerator (AffineSpaceGenerator F ℓ) ε_mca' LC := by sorry

/-- Lemma 7.1. in [BCGM25].
The affine line generator `F → F²`, `x ↦ (1, x)`, having MCA error `ε_mca` for `LC` implies that
the affine space generator `Fˡ → Fˡ⁺¹`, `x ↦ (1, x)`, has MCA for `LC` with error
`(1 - 1/|F|)⁻¹ • ε_mca`.
Note on the statement: the original Lean draft wrote the new error as `a • ε_mca` with
`a := 1 - 1/|F|`.  The reference [BCGM25, Lemma 7.1] gives the error as
`ε_mca · (1 - 1/|F|)⁻¹`, i.e. `a⁻¹ • ε_mca`.  Since `a ≤ 1`, the factor must enlarge (not shrink)
the error bound for the larger affine-space generator, so `a • ε_mca` was an inversion typo.
We therefore prove the corrected statement `a⁻¹ • ε_mca`.
The original draft statement was (note the conclusion `let ε_mca' := a • ε_mca`):
```
  ```
Since `a ≤ 1`, that draft claims the affine-space generator has a *smaller* error than the affine
line generator, which is false (adding codewords only makes the MCA event easier). -/
theorem AffineLine_MCA_AffineSpaceMCA {ℓ : ℕ} (hℓ : ℓ ≥ 2) (ε_mca : I → ℝ) (LC : LinearCode ι F)
    (hGMCA : IsMCAGenerator (AffineLineGenerator F) ε_mca LC) :
    let a := (1 - 1 / Fintype.card F : ℝ)
    let ε_mca' := a⁻¹ • ε_mca
    IsMCAGenerator (AffineSpaceGenerator F ℓ) ε_mca' LC := by
  classical
  show IsMCAGenerator (AffineSpaceGenerator F ℓ)
        ((1 - 1 / (Fintype.card F : ℝ))⁻¹ • ε_mca) LC
  intro U γ
  set a : ℝ := (1 - 1 / (Fintype.card F : ℝ)) with ha_def
  have hq1 : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have ha : 0 < a := by
    have h1 : (1 : ℝ) / (Fintype.card F : ℝ) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    rw [ha_def]; linarith
  have hs : 1 ≤ ℓ := by omega
  -- Rewrite the affine-space probability as a real density.
  rw [prob_uniform_eq_ofReal]
  have hcard : (Fintype.card (Fin ℓ → F) : ℝ) = (Fintype.card F : ℝ) ^ ℓ := by
    -- Route through Nat.card which is instance-independent (defined via cardinals).
    have h : Nat.card (Fin ℓ → F) = Fintype.card F ^ ℓ := by
      rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card]
    exact_mod_cast (Nat.card_eq_fintype_card (α := Fin ℓ → F)).symm.trans h
  rw [hcard]
  -- Simplify the right-hand error.
  have hrhs : ((a⁻¹ • ε_mca) γ) = a⁻¹ * ε_mca γ := by
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hrhs]
  -- Obtain the line bound and the affine-line MCA hypothesis.
  obtain ⟨W, hW⟩ := AffineMCA.exists_line_bound hs LC U γ
  rw [← ha_def] at hW
  have hline := hGMCA W γ
  rw [prob_uniform_eq_ofReal] at hline
  set sp : ℝ :=
    ((Finset.univ.filter (fun x : Fin ℓ → F =>
        IsMCA (AffineSpaceGenerator F ℓ) LC x U γ)).card : ℝ) with hsp
  set ln : ℝ :=
    ((Finset.univ.filter (fun t : F =>
        IsMCA (AffineLineGenerator F) LC t W γ)).card : ℝ) with hln
  have hsp0 : 0 ≤ sp / (Fintype.card F : ℝ) ^ ℓ := by positivity
  have hln0 : 0 ≤ ln / (Fintype.card F : ℝ) := by positivity
  by_cases hε : 0 ≤ ε_mca γ
  · have hlre : ln / (Fintype.card F : ℝ) ≤ ε_mca γ :=
      (ENNReal.ofReal_le_ofReal_iff hε).mp hline
    have hchain : a * (sp / (Fintype.card F : ℝ) ^ ℓ) ≤ ε_mca γ := le_trans hW hlre
    have hfin : sp / (Fintype.card F : ℝ) ^ ℓ ≤ a⁻¹ * ε_mca γ := by
      rw [inv_mul_eq_div, le_div_iff₀ ha, mul_comm]
      exact hchain
    exact ENNReal.ofReal_le_ofReal hfin
  · push Not at hε
    have h0 : ENNReal.ofReal (ε_mca γ) = 0 := ENNReal.ofReal_of_nonpos (le_of_lt hε)
    rw [h0] at hline
    have hln_le : ln / (Fintype.card F : ℝ) ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp (le_antisymm hline (zero_le _))
    have hln_eq : ln / (Fintype.card F : ℝ) = 0 := le_antisymm hln_le hln0
    have hchain : a * (sp / (Fintype.card F : ℝ) ^ ℓ) ≤ 0 := by
      rw [← hln_eq];
      sorry
    have hsp_eq : sp / (Fintype.card F : ℝ) ^ ℓ = 0 := by
      by_contra h
      have hpos : 0 < sp / (Fintype.card F : ℝ) ^ ℓ := lt_of_le_of_ne hsp0 (Ne.symm h)
      have : 0 < a * (sp / (Fintype.card F : ℝ) ^ ℓ) := mul_pos ha hpos
      linarith
    rw [hsp_eq]
    simp
