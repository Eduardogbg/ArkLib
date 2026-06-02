/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.CommitmentScheme.Ajtai.InnerOuter.Correctness
import ArkLib.CommitmentScheme.Ajtai.InnerOuter.Arithmetic

/-!
# Weak-Binding Security of the Inner-Outer Ajtai Commitment

The Greyhound [NS24] / Hachi [NOZ26] weak-binding reduction over the cyclotomic ring `Rq Φ`
(`R = ZMod q`).
A weak opening carries, per block `i`, a message `sᵢ`, an inner-decomposition `t̂ᵢ`, and a
challenge `cᵢ`; the verifier `verify_weak` bounds each challenge (nonzero, `ℓ₁ ≤ κ`), bounds
each scaled message (`‖cᵢ·sᵢ‖₂² ≤ β²`), checks the inner gadget relation, and bounds and
checks the outer commitment.

The *definitions* (opening, verifier, experiment, advantage, reductions) are polymorphic in
the cyclotomic modulus `Φ`. The *security statements*, however, are pinned to the power-of-two
cyclotomic modulus `Φ = powTwoCyclotomic α` (`φ = X^{2^α} + 1`), abbreviated `𝓜(q, α)`,
because they invoke the two deep inputs that only hold there: accepted challenges are
genuinely invertible via the Lyubashevsky–Seiler [LS18] result (`isUnit_of_l1Norm_le`), and
scaled messages stay short via the Micciancio/Young product bound
(`scalarVecMul_mul_l2NormSq_le`). The reductions therefore carry the remaining [LS18]
hypotheses: `q ≡ 5 (mod 8)` and `κ² < q`.

`outputToModuleSIS_valid` is the cryptographic heart: a winning pair of distinct weak
openings yields a valid inner *or* outer Module-SIS witness. `advantage_le_moduleSIS` wraps
it probabilistically.

Adapted from VCV-io's `LatticeCrypto.Ajtai.InnerOuter.Security`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings*][LS18]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleComp CommitmentScheme CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
  ArkLib.Lattices.Ajtai
open scoped ENNReal BigOperators

namespace ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ] (α : ℕ)
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}

-- `𝓜(q, α)` (the inner-outer commitment modulus `hachiModulus q α`) is the scoped notation from
-- `InnerOuter.Arithmetic`, active here since this namespace is nested in `…InnerOuter`.

/-! ## Generic helpers -/

/-- Boolean monotonicity of `pure` outcome probability into a disjunction. -/
theorem probOutput_pure_bool_le_or (win inner outer : Bool)
    (h : win = true → inner = true ∨ outer = true) :
    Pr[= true | ((pure win) : ProbComp Bool)] ≤
      Pr[= true | ((pure inner) : ProbComp Bool)] +
        Pr[= true | ((pure outer) : ProbComp Bool)] := by
  cases win <;> cases inner <;> cases outer <;> simp_all

/-- The first index where two function-vectors differ, if any. -/
def firstDiff? {T : Type*} [DecidableEq T] {n : Nat} (x y : Fin n → T) : Option (Fin n) :=
  (List.finRange n).find? (fun i => decide (x i ≠ y i))

theorem firstDiff?_some_of_differs {T : Type*} [DecidableEq T] {n : Nat}
    {x y : Fin n → T} (h : (firstDiff? x y).isSome = true) :
    ∃ i : Fin n, firstDiff? x y = some i :=
  Option.isSome_iff_exists.mp h

theorem firstDiff?_eq_some_ne {T : Type*} [DecidableEq T] {n : Nat}
    {x y : Fin n → T} {i : Fin n} (h : firstDiff? x y = some i) : x i ≠ y i := by
  have := List.find?_some h
  simpa using this

/-! ## Weak opening, verifier, and experiment -/

/-- A Hachi/Greyhound weak opening: per-block messages `(sᵢ)`, inner decompositions `(t̂ᵢ)`,
and challenges `(cᵢ)`. -/
structure Opening (Φ : CyclotomicModulus (ZMod q))
    (innerRows messageRows messageDigits blocks innerDigits : Nat) where
  /-- Per-block messages `(sᵢ)`. -/
  message : PolyVec (PolyVec (Rq Φ) (messageRows * messageDigits)) blocks
  /-- Per-block inner decompositions `(t̂ᵢ)`. -/
  innerDecomp : PolyVec (PolyVec (Rq Φ) (innerRows * innerDigits)) blocks
  /-- Per-block challenges `(cᵢ)`. -/
  challenge : PolyVec (Rq Φ) blocks

/-- The trivial fallback witness, used on the branch where the other matrix yields a witness. -/
def dummySolution (cols : Nat) : ModuleSIS.Solution Φ cols := fun _ => 0

/-- Verify a Hachi/Greyhound weak opening. -/
def verify_weak (base : ZMod q) (βSq γSq κ : Nat)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (u : Commitment Φ outerRows)
    (opening : Opening Φ innerRows messageRows messageDigits blocks innerDigits) : Bool :=
  (List.finRange blocks).all (fun i =>
    decide (0 < Rq.l1Norm Φ (opening.challenge i)) &&
      decide (Rq.l1Norm Φ (opening.challenge i) ≤ κ) &&
      decide (vecL2NormSq Φ (scalarVecMul (opening.challenge i) (opening.message i)) ≤ βSq) &&
      Simple.verify Φ (gadgetMatrix Φ base innerRows innerDigits)
        (opening.innerDecomp i) (Simple.commit Φ pp.innerMatrix (opening.message i)) ()) &&
    decide (vecL2NormSq Φ (PolyVec.flattenBlocks opening.innerDecomp) ≤ γSq) &&
    Simple.verify Φ pp.outerMatrix (PolyVec.flattenBlocks opening.innerDecomp) u ()

/-- Weak openings differ when they contain different message tuples `(sᵢ)`. -/
def openingsDiffer
    (opening₁ opening₂ : Opening Φ innerRows messageRows messageDigits blocks innerDigits) : Bool :=
  (firstDiff? opening₁.message opening₂.message).isSome

/-- A weak-binding adversary outputs two weak openings for the same commitment. -/
abbrev Adversary (Φ : CyclotomicModulus (ZMod q))
    (innerRows messageRows messageDigits outerRows blocks innerDigits : Nat) :=
  PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits →
    ProbComp
      (Commitment Φ outerRows ×
        Opening Φ innerRows messageRows messageDigits blocks innerDigits ×
        Opening Φ innerRows messageRows messageDigits blocks innerDigits)

/-! ## Extracted witnesses -/

/-- The scaled message `(c₁ᵢ · c₂ᵢ) · s₁ᵢ`. -/
def scaledMessage
    (opening₁ opening₂ : Opening Φ innerRows messageRows messageDigits blocks innerDigits)
    (i : Fin blocks) : PolyVec (Rq Φ) (messageRows * messageDigits) :=
  scalarVecMul (opening₁.challenge i * opening₂.challenge i) (opening₁.message i)

/-- Turn two weak openings into either an inner or outer Module-SIS witness: if the inner
decompositions flatten equally, use the first differing message block (scaled witness);
otherwise use the difference of the flattened inner decompositions. -/
def outputToModuleSIS
    (opening₁ opening₂ : Opening Φ innerRows messageRows messageDigits blocks innerDigits) :
    Sum (ModuleSIS.Solution Φ (messageRows * messageDigits))
      (ModuleSIS.Solution Φ (blocks * (innerRows * innerDigits))) :=
  let flat₁ := PolyVec.flattenBlocks opening₁.innerDecomp
  let flat₂ := PolyVec.flattenBlocks opening₂.innerDecomp
  if flat₁ = flat₂ then
    match firstDiff? opening₁.message opening₂.message with
    | some i => Sum.inl (scaledMessage Φ opening₁ opening₂ i - scaledMessage Φ opening₂ opening₁ i)
    | none => Sum.inr (flat₁ - flat₂)
  else Sum.inr (flat₁ - flat₂)

/-- Per-block facts from a successful weak-opening verification. -/
structure VerifiedBlock (base : ZMod q) (βSq κ : Nat)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (opening : Opening Φ innerRows messageRows messageDigits blocks innerDigits)
    (i : Fin blocks) : Prop where
  /-- The challenge is invertible (Lyubashevsky–Seiler). -/
  unit : IsUnit (opening.challenge i)
  /-- The challenge is `ℓ₁`-short. -/
  challenge_short : Rq.l1Norm Φ (opening.challenge i) ≤ κ
  /-- The scaled message is `ℓ₂²`-short. -/
  scaled_short :
    vecL2NormSq Φ (scalarVecMul (opening.challenge i) (opening.message i)) ≤ βSq
  /-- The inner gadget relation holds. -/
  inner_eq :
    Simple.commit Φ (gadgetMatrix Φ base innerRows innerDigits) (opening.innerDecomp i) =
      Simple.commit Φ pp.innerMatrix (opening.message i)

/-- Facts from a successful weak-opening verification. -/
structure VerifiedOpening (base : ZMod q) (βSq γSq κ : Nat)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (u : Commitment Φ outerRows)
    (opening : Opening Φ innerRows messageRows messageDigits blocks innerDigits) : Prop where
  /-- The outer commitment opens to `u`. -/
  outer_eq :
    Simple.commit Φ pp.outerMatrix (PolyVec.flattenBlocks opening.innerDecomp) = u
  /-- The flattened inner decomposition is `ℓ₂²`-short. -/
  outer_short : vecL2NormSq Φ (PolyVec.flattenBlocks opening.innerDecomp) ≤ γSq
  /-- Every block is verified. -/
  block : ∀ i : Fin blocks, VerifiedBlock Φ base βSq κ pp opening i

/-! ## Security: pinned to the power-of-two modulus `𝓜(q, α)` -/

/-- Extract reusable weak-opening facts from a successful verification (over `𝓜(q, α)`,
where Lyubashevsky–Seiler invertibility applies). -/
theorem verifiedOpening_of_verify_eq_true {base : ZMod q}
    (hq5 : q % 8 = 5) {βSq γSq κ : Nat} (hκ : κ ^ 2 < q)
    {pp : PublicParams 𝓜(q, α)
      innerRows messageRows messageDigits outerRows blocks innerDigits}
    {u : Commitment 𝓜(q, α) outerRows}
    {opening : Opening 𝓜(q, α) innerRows messageRows messageDigits blocks innerDigits}
    (hverify : verify_weak 𝓜(q, α) base βSq γSq κ pp u opening = true) :
    VerifiedOpening 𝓜(q, α) base βSq γSq κ pp u opening := by
  simp only [verify_weak, Bool.and_eq_true] at hverify
  obtain ⟨⟨hall, hgamma⟩, houter⟩ := hverify
  refine ⟨(Simple.verify_eq_true_iff 𝓜(q, α) _ _ u ()).1 houter, by simpa using hgamma,
    fun i => ?_⟩
  rw [List.all_eq_true] at hall
  have hb := hall i (List.mem_finRange i)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hpos, hshort⟩, hscaled⟩, hinner⟩ := hb
  exact ⟨isUnit_of_l1Norm_le α hq5 hpos hshort hκ, hshort, hscaled,
    (Simple.verify_eq_true_iff 𝓜(q, α) _ _ _ ()).1 hinner⟩

/-- Equal flattened inner decompositions make verified inner messages collide. -/
theorem inner_commit_eq_of_flatten_eq {base : ZMod q} {βSq γSq κ : Nat}
    {pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits}
    {u : Commitment Φ outerRows}
    {opening₁ opening₂ : Opening Φ innerRows messageRows messageDigits blocks innerDigits}
    (hv₁ : VerifiedOpening Φ base βSq γSq κ pp u opening₁)
    (hv₂ : VerifiedOpening Φ base βSq γSq κ pp u opening₂)
    (hflat : PolyVec.flattenBlocks opening₁.innerDecomp =
      PolyVec.flattenBlocks opening₂.innerDecomp)
    (i : Fin blocks) :
    Simple.commit Φ pp.innerMatrix (opening₁.message i) =
      Simple.commit Φ pp.innerMatrix (opening₂.message i) := by
  have hblock : opening₁.innerDecomp i = opening₂.innerDecomp i :=
    PolyVec.block_eq_of_flattenBlocks_eq hflat i
  calc Simple.commit Φ pp.innerMatrix (opening₁.message i)
      = Simple.commit Φ (gadgetMatrix Φ base innerRows innerDigits) (opening₁.innerDecomp i) :=
        (hv₁.block i).inner_eq.symm
    _ = Simple.commit Φ (gadgetMatrix Φ base innerRows innerDigits) (opening₂.innerDecomp i) := by
        rw [hblock]
    _ = Simple.commit Φ pp.innerMatrix (opening₂.message i) := (hv₂.block i).inner_eq

/-- Verified blocks preserve message inequality after challenge scaling. -/
theorem scaledMessage_ne_of_message_ne {base : ZMod q} {βSq κ : Nat}
    {pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits}
    {opening₁ opening₂ : Opening Φ innerRows messageRows messageDigits blocks innerDigits}
    {i : Fin blocks}
    (hB₁ : VerifiedBlock Φ base βSq κ pp opening₁ i)
    (hB₂ : VerifiedBlock Φ base βSq κ pp opening₂ i)
    (hmsgNe : opening₁.message i ≠ opening₂.message i) :
    scaledMessage Φ opening₁ opening₂ i ≠ scaledMessage Φ opening₂ opening₁ i :=
  scalarVecMul_mul_ne_of_ne hB₁.unit hB₂.unit hmsgNe

/-- A verified block pair bounds a scaled message's squared `ℓ₂` norm (over `𝓜(q, α)`,
where the Micciancio/Young product bound applies). -/
theorem scaledMessage_l2NormSq_le {base : ZMod q} {βSq κ : Nat}
    {pp : PublicParams 𝓜(q, α)
      innerRows messageRows messageDigits outerRows blocks innerDigits}
    {opening₁ opening₂ :
      Opening 𝓜(q, α) innerRows messageRows messageDigits blocks innerDigits}
    {i : Fin blocks}
    (hB₁ : VerifiedBlock 𝓜(q, α) base βSq κ pp opening₁ i)
    (hB₂ : VerifiedBlock 𝓜(q, α) base βSq κ pp opening₂ i) :
    vecL2NormSq 𝓜(q, α) (scaledMessage 𝓜(q, α) opening₁ opening₂ i) ≤
      scalarVecMulMulL2NormSqBound κ βSq :=
  scalarVecMul_mul_l2NormSq_le α (opening₁.challenge i) (opening₂.challenge i)
    (opening₁.message i) hB₂.challenge_short hB₁.scaled_short

/-- Inner Module-SIS shortness: the extracted scaled-message witness has squared `ℓ₂` norm
within `subL2NormSqBound (scalarVecMulMulL2NormSqBound κ β²)`. -/
def innerShort (κ βSq : ℕ) : ModuleSIS.Solution Φ (messageRows * messageDigits) → Bool :=
  fun z => decide (vecL2NormSq Φ z ≤ subL2NormSqBound (scalarVecMulMulL2NormSqBound κ βSq))

/-- Outer Module-SIS shortness: the extracted inner-decomposition difference has squared `ℓ₂`
norm within `subL2NormSqBound γ²`. -/
def outerShort (γSq : ℕ) : ModuleSIS.Solution Φ (blocks * (innerRows * innerDigits)) → Bool :=
  fun z => decide (vecL2NormSq Φ z ≤ subL2NormSqBound γSq)

/-- Verified weak blocks with equal flattened inner decomps give a valid inner relation. -/
theorem inner_relation_of_verified {base : ZMod q} {βSq γSq κ : Nat}
    {pp : PublicParams 𝓜(q, α)
      innerRows messageRows messageDigits outerRows blocks innerDigits}
    {u : Commitment 𝓜(q, α) outerRows}
    {opening₁ opening₂ :
      Opening 𝓜(q, α) innerRows messageRows messageDigits blocks innerDigits}
    (hv₁ : VerifiedOpening 𝓜(q, α) base βSq γSq κ pp u opening₁)
    (hv₂ : VerifiedOpening 𝓜(q, α) base βSq γSq κ pp u opening₂)
    (hflat : PolyVec.flattenBlocks opening₁.innerDecomp =
      PolyVec.flattenBlocks opening₂.innerDecomp)
    {i : Fin blocks} (hmsgNe : opening₁.message i ≠ opening₂.message i) :
    ModuleSIS.relation 𝓜(q, α) (innerShort 𝓜(q, α) κ βSq)
      pp.innerMatrix (scaledMessage 𝓜(q, α) opening₁ opening₂ i -
        scaledMessage 𝓜(q, α) opening₂ opening₁ i)
      = true := by
  have hB₁ := hv₁.block i
  have hB₂ := hv₂.block i
  have hne : scaledMessage 𝓜(q, α) opening₁ opening₂ i -
      scaledMessage 𝓜(q, α) opening₂ opening₁ i ≠ 0 :=
    sub_ne_zero.mpr (scaledMessage_ne_of_message_ne 𝓜(q, α) hB₁ hB₂ hmsgNe)
  have hshort : vecL2NormSq 𝓜(q, α)
      (scaledMessage 𝓜(q, α) opening₁ opening₂ i -
        scaledMessage 𝓜(q, α) opening₂ opening₁ i) ≤
        subL2NormSqBound (scalarVecMulMulL2NormSqBound κ βSq) :=
    sub_l2NormSq_le 𝓜(q, α) _ _ (scaledMessage_l2NormSq_le α hB₁ hB₂)
      (scaledMessage_l2NormSq_le α hB₂ hB₁)
  have hinnerEq := inner_commit_eq_of_flatten_eq 𝓜(q, α) hv₁ hv₂ hflat i
  have heq : pp.innerMatrix *ᵥ scaledMessage 𝓜(q, α) opening₁ opening₂ i =
      pp.innerMatrix *ᵥ scaledMessage 𝓜(q, α) opening₂ opening₁ i := by
    simpa [scaledMessage, Simple.commit] using
      matVecMul_scalarVecMul_mul_eq_of_eq pp.innerMatrix (opening₁.challenge i)
        (opening₂.challenge i) (by simpa [Simple.commit] using hinnerEq)
  have hker : pp.innerMatrix *ᵥ
      (scaledMessage 𝓜(q, α) opening₁ opening₂ i -
        scaledMessage 𝓜(q, α) opening₂ opening₁ i) = 0 := by
    rw [matVecMul_sub]; exact sub_eq_zero.mpr heq
  simp [ModuleSIS.relation, innerShort, hne, hshort, hker]

/-- Verified weak openings with different flattened witnesses give a valid outer relation. -/
theorem outer_relation_of_verified {base : ZMod q} {βSq γSq κ : Nat}
    {pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits}
    {u : Commitment Φ outerRows}
    {opening₁ opening₂ : Opening Φ innerRows messageRows messageDigits blocks innerDigits}
    (hv₁ : VerifiedOpening Φ base βSq γSq κ pp u opening₁)
    (hv₂ : VerifiedOpening Φ base βSq γSq κ pp u opening₂)
    (hflat : PolyVec.flattenBlocks opening₁.innerDecomp ≠
      PolyVec.flattenBlocks opening₂.innerDecomp) :
    ModuleSIS.relation Φ (outerShort Φ γSq)
      pp.outerMatrix
      (PolyVec.flattenBlocks opening₁.innerDecomp - PolyVec.flattenBlocks opening₂.innerDecomp)
      = true := by
  have hne : PolyVec.flattenBlocks opening₁.innerDecomp -
      PolyVec.flattenBlocks opening₂.innerDecomp ≠ 0 := sub_ne_zero.mpr hflat
  have hshort : vecL2NormSq Φ
      (PolyVec.flattenBlocks opening₁.innerDecomp - PolyVec.flattenBlocks opening₂.innerDecomp) ≤
        subL2NormSqBound γSq :=
    sub_l2NormSq_le Φ _ _ hv₁.outer_short hv₂.outer_short
  have heq : pp.outerMatrix *ᵥ PolyVec.flattenBlocks opening₁.innerDecomp =
      pp.outerMatrix *ᵥ PolyVec.flattenBlocks opening₂.innerDecomp := by
    simpa [Simple.commit] using hv₁.outer_eq.trans hv₂.outer_eq.symm
  have hker : pp.outerMatrix *ᵥ
      (PolyVec.flattenBlocks opening₁.innerDecomp -
        PolyVec.flattenBlocks opening₂.innerDecomp) = 0 := by
    rw [matVecMul_sub]; exact sub_eq_zero.mpr heq
  simp [ModuleSIS.relation, outerShort, hne, hshort, hker]

/-- A successful pair of weak openings yields a valid inner or outer Module-SIS witness (over
`𝓜(q, α)`). -/
theorem outputToModuleSIS_valid (base : ZMod q)
    (hq5 : q % 8 = 5) (βSq γSq κ : Nat) (hκ : κ ^ 2 < q)
    (pp : PublicParams 𝓜(q, α)
      innerRows messageRows messageDigits outerRows blocks innerDigits)
    (u : Commitment 𝓜(q, α) outerRows)
    (opening₁ opening₂ :
      Opening 𝓜(q, α) innerRows messageRows messageDigits blocks innerDigits)
    (hwin : (openingsDiffer 𝓜(q, α) opening₁ opening₂ &&
      verify_weak 𝓜(q, α) base βSq γSq κ pp u opening₁ &&
      verify_weak 𝓜(q, α) base βSq γSq κ pp u opening₂) = true) :
    match outputToModuleSIS 𝓜(q, α) opening₁ opening₂ with
    | Sum.inl z =>
        ModuleSIS.relation 𝓜(q, α) (innerShort 𝓜(q, α) κ βSq) pp.innerMatrix z = true
    | Sum.inr z =>
        ModuleSIS.relation 𝓜(q, α) (outerShort 𝓜(q, α) γSq)
          pp.outerMatrix z = true := by
  simp only [Bool.and_eq_true] at hwin
  obtain ⟨⟨hdiff, hverify₁⟩, hverify₂⟩ := hwin
  have hv₁ := verifiedOpening_of_verify_eq_true α hq5 hκ hverify₁
  have hv₂ := verifiedOpening_of_verify_eq_true α hq5 hκ hverify₂
  unfold outputToModuleSIS
  by_cases hflat : PolyVec.flattenBlocks opening₁.innerDecomp =
      PolyVec.flattenBlocks opening₂.innerDecomp
  · obtain ⟨i, hfind⟩ := firstDiff?_some_of_differs hdiff
    have hmsgNe : opening₁.message i ≠ opening₂.message i := firstDiff?_eq_some_ne hfind
    simp only [hflat, if_true, hfind]
    exact inner_relation_of_verified α hv₁ hv₂ hflat hmsgNe
  · simp only [hflat, if_false]
    exact outer_relation_of_verified 𝓜(q, α) hv₁ hv₂ hflat

/-! ## The weak-binding reductions and advantage bound -/

variable
  [SampleableType (Simple.PublicParams Φ innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))]

/-- The Hachi/Greyhound weak-binding experiment. -/
def experiment (base : ZMod q) (βSq γSq κ : Nat)
    (adv : Adversary Φ innerRows messageRows messageDigits outerRows blocks innerDigits) :
    ProbComp Bool := do
  let A ← $ᵗ (Simple.PublicParams Φ innerRows (messageRows * messageDigits))
  let B ← $ᵗ (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))
  let pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits :=
    { innerMatrix := A, outerMatrix := B }
  let (u, opening₁, opening₂) ← adv pp
  pure (openingsDiffer Φ opening₁ opening₂ &&
    verify_weak Φ base βSq γSq κ pp u opening₁ &&
    verify_weak Φ base βSq γSq κ pp u opening₂)

/-- Weak-binding advantage. -/
noncomputable def advantage (base : ZMod q) (βSq γSq κ : Nat)
    (adv : Adversary Φ innerRows messageRows messageDigits outerRows blocks innerDigits) : ℝ≥0∞ :=
  Pr[= true | experiment Φ base βSq γSq κ adv]

/-- Reduction attacking the inner Module-SIS matrix. -/
def innerAdvToModuleSIS
    (isShort : ModuleSIS.Solution Φ (messageRows * messageDigits) → Bool)
    (adv : Adversary Φ innerRows messageRows messageDigits outerRows blocks innerDigits) :
    ModuleSIS.Adversary Φ innerRows (messageRows * messageDigits) isShort :=
  fun A => do
    let B ← $ᵗ (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))
    let (_u, opening₁, opening₂) ← adv { innerMatrix := A, outerMatrix := B }
    match outputToModuleSIS Φ opening₁ opening₂ with
    | Sum.inl z => pure z
    | Sum.inr _ => pure (dummySolution Φ (messageRows * messageDigits))

/-- Reduction attacking the outer Module-SIS matrix. -/
def outerAdvToModuleSIS
    (isShort : ModuleSIS.Solution Φ (blocks * (innerRows * innerDigits)) → Bool)
    (adv : Adversary Φ innerRows messageRows messageDigits outerRows blocks innerDigits) :
    ModuleSIS.Adversary Φ outerRows (blocks * (innerRows * innerDigits)) isShort :=
  fun B => do
    let A ← $ᵗ (Simple.PublicParams Φ innerRows (messageRows * messageDigits))
    let (_u, opening₁, opening₂) ← adv { innerMatrix := A, outerMatrix := B }
    match outputToModuleSIS Φ opening₁ opening₂ with
    | Sum.inl _ => pure (dummySolution Φ (blocks * (innerRows * innerDigits)))
    | Sum.inr z => pure z

/-- Pointwise weak-binding to Module-SIS bound for fixed samples (over `𝓜(q, α)`). -/
theorem sample_advantage_le_moduleSIS (base : ZMod q)
    (hq5 : q % 8 = 5) (βSq γSq κ : Nat) (hκ : κ ^ 2 < q)
    (A : Simple.PublicParams 𝓜(q, α) innerRows (messageRows * messageDigits))
    (B : Simple.PublicParams 𝓜(q, α) outerRows (blocks * (innerRows * innerDigits)))
    (u : Commitment 𝓜(q, α) outerRows)
    (opening₁ opening₂ :
      Opening 𝓜(q, α) innerRows messageRows messageDigits blocks innerDigits) :
    Pr[= true | ((pure (openingsDiffer 𝓜(q, α) opening₁ opening₂ &&
        verify_weak 𝓜(q, α) base βSq γSq κ
          { innerMatrix := A, outerMatrix := B } u opening₁ &&
        verify_weak 𝓜(q, α) base βSq γSq κ
          { innerMatrix := A, outerMatrix := B } u opening₂))
      : ProbComp Bool)] ≤
      Pr[= true | ((pure (ModuleSIS.relation 𝓜(q, α) (innerShort 𝓜(q, α) κ βSq)
          A (match outputToModuleSIS 𝓜(q, α) opening₁ opening₂ with
            | Sum.inl z => z
            | Sum.inr _ => dummySolution 𝓜(q, α) (messageRows * messageDigits))))
        : ProbComp Bool)] +
      Pr[= true | ((pure (ModuleSIS.relation 𝓜(q, α) (outerShort 𝓜(q, α) γSq)
          B (match outputToModuleSIS 𝓜(q, α) opening₁ opening₂ with
            | Sum.inl _ => dummySolution 𝓜(q, α) (blocks * (innerRows * innerDigits))
            | Sum.inr z => z)))
        : ProbComp Bool)] := by
  let pp : PublicParams 𝓜(q, α)
      innerRows messageRows messageDigits outerRows blocks innerDigits :=
    { innerMatrix := A, outerMatrix := B }
  refine probOutput_pure_bool_le_or _ _ _ (fun hwin => ?_)
  have hvalid := outputToModuleSIS_valid α base hq5 βSq γSq κ hκ pp u
    opening₁ opening₂ hwin
  cases hsol : outputToModuleSIS 𝓜(q, α) opening₁ opening₂ with
  | inl z => exact Or.inl (by rw [hsol] at hvalid; simpa [hsol, pp] using hvalid)
  | inr z => exact Or.inr (by rw [hsol] at hvalid; simpa [hsol, pp] using hvalid)

variable
  [SampleableType (Simple.PublicParams 𝓜(q, α) innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams 𝓜(q, α) outerRows (blocks * (innerRows * innerDigits)))]

/-- **Weak binding reduces to Module-SIS.** The Hachi/Greyhound weak-binding advantage (over
`𝓜(q, α)`) is bounded by the sum of the inner and outer extracted Module-SIS advantages. -/
theorem advantage_le_moduleSIS (base : ZMod q)
    (hq5 : q % 8 = 5) (βSq γSq κ : Nat) (hκ : κ ^ 2 < q)
    (adv :
      Adversary 𝓜(q, α) innerRows messageRows messageDigits outerRows blocks innerDigits) :
    advantage 𝓜(q, α) base βSq γSq κ adv ≤
      ModuleSIS.advantage 𝓜(q, α) innerRows (messageRows * messageDigits)
          (innerShort 𝓜(q, α) κ βSq)
          (innerAdvToModuleSIS 𝓜(q, α) (innerShort 𝓜(q, α) κ βSq) adv) +
        ModuleSIS.advantage 𝓜(q, α) outerRows (blocks * (innerRows * innerDigits))
          (outerShort 𝓜(q, α) γSq)
          (outerAdvToModuleSIS 𝓜(q, α) (outerShort 𝓜(q, α) γSq) adv) := by
  unfold advantage experiment ModuleSIS.advantage SIS.advantage SIS.experiment
    ModuleSIS.problem innerAdvToModuleSIS outerAdvToModuleSIS
  simp only [monad_norm]
  rw [← probOutput_bind_bind_swap
    ($ᵗ (Simple.PublicParams 𝓜(q, α) innerRows (messageRows * messageDigits)))
    ($ᵗ (Simple.PublicParams 𝓜(q, α) outerRows (blocks * (innerRows * innerDigits)))) _ true]
  refine probOutput_bind_congr_le_add
    (mx := $ᵗ (Simple.PublicParams 𝓜(q, α) innerRows (messageRows * messageDigits)))
    (y := true) (z₁ := true) (z₂ := true) (fun A _ => ?_)
  refine probOutput_bind_congr_le_add
    (mx := $ᵗ (Simple.PublicParams 𝓜(q, α) outerRows (blocks * (innerRows * innerDigits))))
    (y := true) (z₁ := true) (z₂ := true) (fun B _ => ?_)
  refine probOutput_bind_congr_le_add
    (mx := adv { innerMatrix := A, outerMatrix := B })
    (y := true) (z₁ := true) (z₂ := true) (fun x _ => ?_)
  obtain ⟨u, opening₁, opening₂⟩ := x
  have hs := sample_advantage_le_moduleSIS α base hq5 βSq γSq κ hκ A B u
    opening₁ opening₂
  cases hsol : outputToModuleSIS 𝓜(q, α) opening₁ opening₂ with
  | inl z => rw [hsol] at hs; simpa using hs
  | inr z => rw [hsol] at hs; simpa using hs

end ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding
