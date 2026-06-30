/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import ArkLib.Data.CodingTheory.ProximityGap.MCAGenerator
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.AffineGenHelperLemmas
import ArkLib.Data.Probability.Notation
import ArkLib.Data.Probability.Instances


/-!
## Main Results

- Lemma 7.1. [BCGM25]: Mutual correlated agreement (MCA) for the affine line generator implies
MCA for the affine space generator.

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BCGM25]. Full paper : https://eprint.iacr.org/2025/2051}
-/

open unitInterval NNReal ENNReal CoreDefinitions LinearTransformations LinearCode
open scoped ProbabilityTheory NNReal ENNReal BigOperators


variable {ι : Type} [Fintype ι]
         {F : Type} [Field F] [Fintype F]


/-- Lemma 7.1. [BCGM25].
The affine line generator `F → F²`, `x ↦ (1, x)`, having MCA error `ε_mca` for `LC` implies that
the affine space generator `Fˡ → Fˡ⁺¹`, `x ↦ (1, x)`, has MCA for `LC` with error
`(1 - 1/|F|)⁻¹ • ε_mca`. -/
theorem AffineLine_MCA_AffineSpaceMCA {ℓ : ℕ} (hℓ : ℓ ≥ 2) (ε_mca : I → ℝ) (LC : LinearCode ι F)
    (hGMCA : IsMCAGenerator (AffineLineGenerator F) ε_mca LC) :
    letI a := (1 - 1 / Fintype.card F : ℝ)
    letI ε_mca' := a⁻¹ • ε_mca
    IsMCAGenerator (AffineSpaceGenerator F ℓ) ε_mca' LC := by
  classical
  intro U γ
  set a : ℝ := (1 - 1 / (Fintype.card F : ℝ))
  have ha : 0 < a := by
    have hq1 : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hs : 1 ≤ ℓ := by omega
  rw [prob_uniform_eq_ofReal]
  have hcard : (Fintype.card (Fin ℓ → F) : ℝ) = (Fintype.card F : ℝ) ^ ℓ := by
    norm_cast
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [hcard]
  simp only [Pi.smul_apply, smul_eq_mul]
  obtain ⟨W, hW⟩ := AffineMCA.exists_line_bound hs LC U γ
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
      ENNReal.ofReal_eq_zero.mp (le_antisymm hline zero_le)
    have hln_eq : ln / (Fintype.card F : ℝ) = 0 := le_antisymm hln_le hln0
    have hchain : a * (sp / (Fintype.card F : ℝ) ^ ℓ) ≤ 0 := by
      rw [← hln_eq]; exact hW
    have hsp_eq : sp / (Fintype.card F : ℝ) ^ ℓ = 0 := by
      by_contra h
      have hpos : 0 < sp / (Fintype.card F : ℝ) ^ ℓ := lt_of_le_of_ne hsp0 (Ne.symm h)
      have : 0 < a * (sp / (Fintype.card F : ℝ) ^ ℓ) := mul_pos ha hpos
      linarith
    rw [hsp_eq]
    simp
