/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.JohnsonBound.Basic
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# ABF26 §3.1 — Johnson family `J_{q,ℓ}, J_q, J` and Theorem 3.2 / Corollary 3.3

Extensions to `JohnsonBound/Basic.lean` matching the paper-shaped statements from
ABF26 §3.1 (Arnon-Boneh-Fenzi, *Open Problems in List Decoding and Correlated
Agreement*, 2026).

The existing `JohnsonBound.J q δ : ℝ` matches the paper's `J_q(δ)`. This file adds:

- `JohnsonBound.Jqℓ q ℓ δ` — paper's `J_{q,ℓ}(δ)`, with the `(ℓ-1)/ℓ` factor inside
  the square root (matching the `.tex`, ~line 1347).
- `JohnsonBound.Jcap δ` — paper's asymptotic Johnson bound `J(δ) := 1 - √(1 - δ)`.

The three are related by `J_{q,ℓ}(δ) →_{ℓ → ∞} J_q(δ) →_{q → ∞} J(δ)`; we state the
limit relationships in docstrings but do not formalise the limits (the paper does
not prove them either).

The file also states the paper-shaped versions of:

- `johnson_bound_lambda_le_ell` — ABF26 Theorem 3.2 [Joh62]:
  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`.
- `mds_johnson_lambda_le` — ABF26 Corollary 3.3:
  for any MDS code `C` of rate `ρ` and `η > 0`, `|Λ(C, 1 - √ρ - η)| ≤ 1/(2·η·ρ)`.

Both are admitted as external results (T3.2 has an existing in-tree proof via
`johnson_bound` / `johnson_bound_alphabet_free` in `JohnsonBound/Basic.lean` that
needs porting from the absolute-distance form to ABF26's `Lambda` form; C3.3
follows from L2.6 + T3.2, but uses the asymptotic Johnson radius which crosses
ArkLib's existing rate/distance bridge).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [Joh62] Johnson. (Original Johnson bound paper.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace JohnsonBound

open Real

/-- **ABF26 Definition 3.1, `J_{q,ℓ}`.** The q-ary ℓ-radius Johnson function:

  `J_{q,ℓ}(δ) := (1 - 1/q) · (1 - √(1 - q/(q-1) · (ℓ-1)/ℓ · δ))`

The `(ℓ-1)/ℓ` list factor matches the canonical `.tex` (~line 1347). It is the
classical list-`ℓ` Johnson factor (= `1 - 1/ℓ`, cf. [GRS12]), increasing in `ℓ`,
so a *smaller* list budget `ℓ` gives a *smaller* radius. Both `(ℓ-1)/ℓ` and the
limiting factor `1` agree as `ℓ → ∞`, so the paper's `J_q = lim_{ℓ→∞} J_{q,ℓ}`
is unaffected.

For `ℓ = 2` this is the binary Johnson radius; as `ℓ → ∞`, `Jqℓ q ℓ δ → J q δ`
(the existing `JohnsonBound.J`). The `ℓ` parameter is the target list size. -/
noncomputable def Jqℓ (q ℓ : ℚ) (δ : ℚ) : ℝ :=
  let frac : ℚ := q / (q - 1)
  let lFac : ℚ := (ℓ - 1) / ℓ
  ((1 - 1 / q) : ℚ) * (1 - √(1 - frac * lFac * δ))

/-- **ABF26 Definition 3.1, `J`.** Paper's asymptotic Johnson bound:

  `J(δ) := 1 - √(1 - δ)`

Equals the `q → ∞` limit of `J_q(δ)` and the `q, ℓ → ∞` limit of `J_{q,ℓ}(δ)`.
This is also the binary Johnson bound (q = 2, ℓ → ∞).

Distinct from the existing `JohnsonBound.J q δ`, which is the paper's `J_q(δ)`
(the q-ary limit, parametrised by `q`). To avoid renaming the existing `J`, we
name this `Jcap` (Johnson — *cap*acity). -/
noncomputable def Jcap (δ : ℝ) : ℝ := 1 - √(1 - δ)

@[simp]
lemma Jcap_zero : Jcap 0 = 0 := by simp [Jcap]

@[simp]
lemma Jcap_one : Jcap 1 = 1 := by simp [Jcap]

end JohnsonBound

namespace CodingTheory

open scoped NNReal
open ListDecodable JohnsonBound

/-- **ABF26 Theorem 3.2 [Joh62].** Johnson bound on list size. For any code
`C ⊆ Σ^n` with `|Σ| = q`,

  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`

where `δ_min(C) = minDist(C) / n` is the relative minimum distance and `J_{q,ℓ}`
is the paper's q-ary ℓ-radius Johnson function. **Admitted (tagged sorry).** Note
the existing absolute-distance Johnson bound in
[`JohnsonBound/Basic.lean`](Basic.lean) (`johnson_bound`, `johnson_bound_alphabet_free`)
is **not** directly portable to this `J_{q,ℓ}`-radius `Lambda` form: at the `Jqℓ`
boundary the existing bound's `JohnsonConditionStrong` precondition is violated (the
denominator goes negative — see the inline comment below for the computation), so a
Guruswami–Sudan-style `J_{q,ℓ}`-specific argument is required. Tracked in
`docs/kb/ABF26_PLAN.md`.

**Alphabet generality.** Stated over an arbitrary alphabet `α` (not necessarily a
field), matching the paper's `Σ`. The Johnson bound is a purely combinatorial fact
about Hamming distance — it does not need field structure.

**Radicand guard (`_h_radicand`).** `Jqℓ` contains
`√(1 - q/(q-1) · (ℓ-1)/ℓ · δ_min)`. Lean's `Real.sqrt` silently truncates negative
inputs to `0`, so without a guard the radius would silently inflate to
`(1 - 1/q) · (1 - 0) = 1 - 1/q` whenever the radicand is negative — at which radius
the list-size-`ℓ` claim is **false** (e.g. a high-distance code can have more than `ℓ`
codewords within relative distance `1 - 1/q`). The hypothesis
`q/(q-1) · (ℓ-1)/ℓ · δ_min ≤ 1` is exactly nonnegativity of the radicand, i.e. the
regime where `J_{q,ℓ}` is a real (untruncated) Johnson radius. (With the corrected
`(ℓ-1)/ℓ` factor — see `Jqℓ` — the guard is weaker than the printed one.) -/
theorem johnson_bound_lambda_le_ell
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : Set (ι → α)) (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ)
    (_h_radicand :
        ((Fintype.card α : ℚ) / ((Fintype.card α : ℚ) - 1))
            * (((ℓ : ℚ) - 1) / (ℓ : ℚ))
            * ((Code.minDist C : ℚ) / Fintype.card ι) ≤ 1) :
    let q : ℚ := Fintype.card α
    let δ_min : ℚ := Code.minDist C / Fintype.card ι
    Lambda C (Jqℓ q ℓ δ_min) ≤ (ℓ : ℕ∞) := by
  sorry -- ABF26-T3.2; external admit (stated with the `(ℓ-1)/ℓ` list factor,
        -- matching the `.tex` ~line 1347, see `Jqℓ`).
        -- With this factor the in-tree `johnson_bound`'s denominator
        -- `Denom = (1 - frac·e/n)² - (1 - frac·d/n)` at `e/n = Jqℓ q ℓ δ_min`
        -- simplifies to `frac·δ_min·(1 - (ℓ-1)/ℓ) = frac·δ_min/ℓ > 0`, so a direct
        -- port may now be possible (the printed factor made it negative); kept as
        -- an external admit pending that port.

/-- **ABF26 Corollary 3.3.** MDS coarse Johnson corollary. For every MDS code `C` with
rate `ρ := dim C / n` and `η > 0`:

  `|Λ(C, 1 - √ρ - η)| ≤ 1 / (2 · η · ρ)`

**Status: DEFERRED IN-TREE DERIVATION, not an independent literature citation.** The paper
*derives* this corollary itself (it is not cited to an external source); it reduces to
L2.6 (Singleton bound: MDS implies `δ_min = 1 - ρ + 1/n`, available via the
`IsMDS_iff_rate_distance` bridge) plus the already-owed Johnson bound T3.2
(`johnson_bound_lambda_le_ell`). So the only genuinely external content here is T3.2; this
`sorry` adds **no new external debt**, it merely defers the Singleton + arithmetic glue. A
machine-checked proof requires first establishing the asymptotic-Johnson form
`Lambda C δ ≤ 1/(2·(Jcap δ - δ))` from the `Jqℓ`-form T3.2 (the standard optimise-over-`ℓ`
step), then the MDS rate-distance manipulation. Tracked as a coverage gap, not a faithfulness
defect (the statement below is exactly the paper's `cor:Jonhson-for-mds`).

**Rate derivation.** `ρ` is bound inline as `(Module.finrank F C : ℝ) / Fintype.card ι`
rather than passed as a separate parameter — this matches the upstream `IsMDS`
signature (additive Nat form, no rate parameter) and lets call sites use
`IsMDS_iff_rate_distance` to extract the rate-distance equation when needed. -/
theorem mds_johnson_lambda_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (η : ℝ) (_hη_pos : 0 < η)
    (_h_mds : LinearCode.IsMDS C) :
    let ρ : ℝ := (Module.finrank F C : ℝ) / Fintype.card ι
    (Lambda ((C : Set (ι → F))) (1 - Real.sqrt ρ - η) : ENNReal) ≤
      ENNReal.ofReal (1 / (2 * η * ρ)) := by
  sorry -- ABF26-C3.3; DEFERRED in-tree derivation (no new external debt): reduces to the
        -- owed T3.2 (johnson_bound_lambda_le_ell) + L2.6 Singleton via IsMDS_iff_rate_distance.

end CodingTheory
