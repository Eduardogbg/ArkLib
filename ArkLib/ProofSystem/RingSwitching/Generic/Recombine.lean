/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Generic.Carrier

/-!
# Generic Ring-Switching — Recombination Injectivity (S4)

Discharges design safe-core (iii), **Flock Remark 5** [BRW26]: naive recombination is complete
but *not sound* — soundness requires the packing-basis recombination `s ↦ ∑ᵢ sᵢ • bᵢ^P`
(`B`-coordinates into the packed algebra) to be injective. In the generic design this is not an
instance obligation: the map *is* `packBasis.equivFun.symm`, so injectivity — indeed bijectivity —
is inherited from the `Basis` being a bundled linear equivalence. A fake or lossy recombination is
unrepresentable (design safety pillar 1; see `docs/kb/concepts/ring-switching.md`, "The Generic
layer", for the spine-step and pillar vocabulary used here).

Scope (design §2, pillar-1 clarification): the soundness-relevant injective map is the
**packing-basis** recombination (step 4). The bridge `Φ = openBasis.constr weight` (step 7) is a
batching *combiner* and is deliberately not injective for general weights — do not conflate the
two.

No domain/field hypotheses — pure `CommRing B` + `Basis` module theory — so the result is
exercised on both S1 carriers (tower and the non-domain decoupled toy) directly (INV-2).

## References

- [BRW26] Bünz, Rothblum, Wang. "Flock: Fast Proving for Batch Boolean Computations." Cryptology
  ePrint Archive, Report 2026/1329. Appendix B, Remark 5 and Eq. (8)
  (slice-wise recombination over the packing basis; injectivity in the base-field coefficients).
-/

noncomputable section

namespace RingSwitching.Generic

open Module

namespace RingSwitchCarrier

variable {B : Type} [CommRing B] (car : RingSwitchCarrier B)

/-- Recombination is a **bijection**: every packed value arises from a *unique* `B`-coordinate
tuple, because `s ↦ ∑ᵢ sᵢ • bᵢ^P` is exactly `packBasis.equivFun.symm`. The inverse direction is
how S5's anchor argument reads (packed value determines the coordinates). -/
theorem recombine_bijective :
    Function.Bijective (fun s : car.ιP → B => ∑ i, s i • car.packBasis i) := by
  have h : (fun s : car.ιP → B => ∑ i, s i • car.packBasis i)
      = car.packBasis.equivFun.symm := by
    funext s
    rw [Basis.equivFun_symm_apply]
  rw [h]
  exact car.packBasis.equivFun.symm.bijective

/-- **Recombination injectivity** (design step 4 / safe-core (iii); [BRW26] Remark 5). Distinct
`B`-coordinate tuples recombine to distinct packed values. This is the property whose *absence*
makes naive recombination unsound (Flock Remark 5); here it is free from the packing `Basis`. -/
theorem recombine_injective :
    Function.Injective (fun s : car.ιP → B => ∑ i, s i • car.packBasis i) :=
  car.recombine_bijective.injective

end RingSwitchCarrier

/-! ## Sanity / testable deliverables (S4 §5.3) -/

section Sanity

-- INV-2: exercised on the *tower* carrier at full generality — arbitrary field extension,
-- arbitrary finite rank…
example {K L : Type} [Field K] [Field L] [Algebra K L] {ι : Type} [Fintype ι]
    (β : Basis ι K L) :
    Function.Injective
      (fun s : (towerCarrier β).ιP → K => ∑ i, s i • (towerCarrier β).packBasis i) :=
  (towerCarrier β).recombine_injective

-- …with a fully concrete pin (no missing instances at a closed type; NB `Pi.basisFun` has the
-- wrong module structure for `towerCarrier`, `Basis.singleton` works)…
example : Function.Injective
    (fun s : (towerCarrier (Basis.singleton (Fin 1) (ZMod 2))).ιP → ZMod 2
      => ∑ i, s i • (towerCarrier (Basis.singleton (Fin 1) (ZMod 2))).packBasis i) :=
  (towerCarrier _).recombine_injective

-- …and on the *decoupled* `P ≠ E` carrier — a non-domain product ring, pinning that the result
-- is CommRing-only (no `[IsDomain]`/`Field` needed anywhere in this file).
example : Function.Injective
    (fun s : decoupledToyCarrier.ιP → ZMod 2 => ∑ i, s i • decoupledToyCarrier.packBasis i) :=
  decoupledToyCarrier.recombine_injective

end Sanity

end RingSwitching.Generic

end
