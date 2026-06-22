/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import ArkLib.ProofSystem.ToyProblem.Leaderboard

/-!
# Toy problem — folded Reed–Solomon instantiation (ABF26 §6.3.2)

The second concrete leaderboard entry for the §6 toy-problem frontier: take the
underlying code to be a **folded** Reed–Solomon code `FRS[F, L, k, s, ω]` with
folding parameter `s > 1`, so a codeword symbol is a length-`s` tuple
`Fin s → F` rather than a scalar `F` (ABF26 Definition 2.15 [GR08]). This is the
`A = Fin s → F` instantiation of the alphabet-generic toy problem (the `A = F`
scalar case is the interleaved-RS entry `koalaIRS` in `Leaderboard.lean`).

Folding is the lever behind the paper's §6.3.2 *subspace-design* analysis: the
`τ`-subspace-design list-decodability of FRS (`τ(r) = s·ρ/(s − r + 1)`) drives
the list-size term, and the construction's **argument-size at enforced 128-bit
security** improves over interleaved RS for large folding. Here we record the
KoalaBear-sextic FRS leaderboard anchors for the **`s = 2^5 = 32` row** — the
paper's primary fully-worked example (`tab:subspace-design-security-analysis`
and `tab:subspace-elias-lowerbound-thresholds`, both at `t = 128`).

## The `s = 32` row at `t = 128` (ABF26 §6.3.2)

* Field `F = KoalaSextic` (`|F| = q^6 ≈ 2^186`), rate `ρ = 1/2`, evaluation
  domain `|L| = 2^16`, message size `k = 2^20`, folding `s = 2^5 = 32`
  (so `k = 2^20 ≤ s·|L| = 2^21`).
* **Provable** RBR knowledge soundness (X side, `tab:subspace-design-security-`
  `analysis`, `r = 8`, at `δ = 7/48`): `bestProvableError ≤ 2^(-29.10)` — the
  convex combination of the spot-check term `(τ(r+1) + 3/(2r))^128 = (41/48)^128
  = 2^(-29.1085)` and the list-size term `≈ 2^(-166.8)`. The certified figure
  rounds the magnitude **down** to `29.10` (the convex combination dominates the
  spot-check term, so `2^(-29.1085)` is a strict ceiling; `29.11` would
  *overstate*, as `2^(-29.1085) > 2^(-29.11)`) — the same round-down discipline
  as the interleaved `koalaIRS` anchor (`64 → 63.99`).
* **Attack** (Y side): `bestProvableError ≥ 2^(-128.01)`. This is the **sweep
  floor** `⨅_δ (1-δ)^t + …`, certified from the **spot-check term alone** — the
  convex combination dominates `(1-δ)^t`, whose infimum over the window
  `(0, δ_min)` is `(1-δ_min)^128 ≈ 2^(-128.006)` because the folded code's MDS
  relative distance `δ_min = D/|L| = 32769/65536 ≈ 0.50002` (a degree-`< k`
  polynomial has `< k` roots, hence `< (k-1)/s = 32767` zero folded-symbols).
  No Elias/list-size lower bound is needed for this ceiling. The paper's
  per-`δ*` Elias value (`tab:subspace-elias-lowerbound-thresholds`, `δ* = 0.499`)
  is the *weaker* point reading `2^(-127.63) = (1-0.499)^128`; it is **not** the
  sweep floor (just above `δ*` the spot-check keeps dropping toward `2^(-128)`,
  so `2^(-127.63)` is not a valid floor unless the list-size term is active
  across the whole `(δ*, δ_min)` sliver — the same sub-band subtlety that bumped
  the interleaved ceiling `116.49 → 117`). The ceiling rounds **up** to `128.01`.
* `securityGap = 128.01 − 29.10 = 98.91` bits.

**Reading the gap honestly.** At a *fixed* `t = 128`, `s = 32` folding gives a
*larger* `bestProvableError` gap than the interleaved entry (`koalaIRS`:
`53.01`). This is faithful, not a defect: folding at fixed `t` does not by
itself improve the δ-swept provable frontier (for `s ≤ 2^4` the paper proves
*no* soundness at all at `t = 128`). The FRS advantage lives on a **different
axis** the toy `bestProvableError` (a fixed-`t` δ-sweep) does not capture:

* **larger folding closes the gap** — at `s = 2^12` the provable side reaches
  `2^(-118.14)` (`r = 108`), a `≈ 10`-bit gap to the `≈ 2^(-128)` attack; and
* **argument-size at enforced 128-bit security** — the `s = 2^5` row reaches
  full `2^(-128.03)` provable soundness at repetition `t = 563`, `r = 8` with
  argument size `417.9 KiB` (`tab:subspace-design-128bit-security`), the metric
  on which folding genuinely beats interleaving.

Both anchors are **full reductions** down to named externals (the sorry-free
integer spot-check leaves `koalaFRS_spotcheck` / `koalaFRS_spotcheck_lb` /
`koalaFRS_combine` plus the proven L6.10 bridge), matching the `koalaIRS` anchors.
The attack ceiling owes a *single* external — the folded MDS relative distance
`koalaFRS_minRelDist` (`δ_min = 32769/65536`); the provable bound owes the
τ-subspace-design `ε_mca` term, the FRS counterpart of the `koalaIRS` owed `ε_mca`
(see `frsLowerBound` / `frsUpperBound_attack`).

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.3.2, Tables for folded Reed–Solomon).
-/

namespace ToyProblem

namespace Impl.FRS

open scoped NNReal ENNReal
open Polynomial ReedSolomon.Folded Code

/-- The folding multiplier `ω` for the `s = 32` folded RS code. A faithful
instantiation takes the paper's `ω` (a field element whose folded orbits
`{α · ω^i : α ∈ L, i < s}` are pairwise distinct — the GR08 `(L, s)`-admissibility
condition, `ReedSolomon.Folded.Admissible`). Over the **noncomputable**
`GaloisField KoalaBear.fieldSize 6` the multiplicative-order facts establishing
admissibility are not available `sorry`-free (the multiplicative analogue of the
additive distinctness used for `koalaDomain`); admissibility — and hence encoder
injectivity — is therefore an owed structural fact (`koalaFRSEnc_injective`). The
concrete witness here is documentary. -/
noncomputable def koalaFoldω : KoalaSextic := 7

/-- The `2^16`-point folded-RS evaluation domain `{1, 2, …, 2^16} ⊆ KoalaSextic`
— deliberately **zero-free** (each point is `i + 1`). Distinctness is injectivity
of `Nat.cast` below the characteristic (`2^16 + 1 ≤ KoalaBear.fieldSize ≈ 2^31`),
exactly as for `koalaDomain`.

The paper's folded-RS evaluation domain is a *smooth multiplicative coset*
(`{g · h^j}`, [ABF26] §6.3 "common case"), which is zero-free; we exclude `0`
here for the same reason it matters downstream: the GR08 admissibility condition
(`ReedSolomon.Folded.Admissible`) requires the folded orbits `{α · ω^i}` to be
pairwise distinct, and its intra-orbit clause `α · ω^i ≠ α` (for `0 < i < s`) is
*false* at `α = 0` (`0 · ω^i = 0`). A domain containing `0` could therefore never
be admissible; a zero-free domain keeps admissibility a genuinely-owed (not
provably-false) side condition (see `koalaFRSEnc_injective`). -/
noncomputable def koalaFRSDomain : Fin (2 ^ 16) ↪ KoalaSextic where
  toFun i := ((i.val + 1 : ℕ) : KoalaSextic)
  inj' i j hij := by
    have hil : (i : ℕ) < 2 ^ 16 := i.isLt
    have hjl : (j : ℕ) < 2 ^ 16 := j.isLt
    have hchar : (2 ^ 16 : ℕ) < KoalaBear.fieldSize := by norm_num [KoalaBear.fieldSize]
    have hi : (i.val + 1) ∈ Set.Iio KoalaBear.fieldSize := Set.mem_Iio.mpr (by omega)
    have hj : (j.val + 1) ∈ Set.Iio KoalaBear.fieldSize := Set.mem_Iio.mpr (by omega)
    have hnat : i.val + 1 = j.val + 1 :=
      CharP.natCast_injOn_Iio KoalaSextic KoalaBear.fieldSize hi hj hij
    exact Fin.val_injective (by omega)

/-- The genuine §6.3.2 folded encoder: the degree-`< 2^20` folded Reed–Solomon
evaluation map on the `2^16` points of `koalaFRSDomain` with folding `s = 32`
(`k = 2^20`, `|L| = 2^16`, `s = 2^5`, rate `ρ = 1/2`), as an `F`-linear map
`(Fin 2^20 → F) →ₗ (Fin 2^16 → Fin 32 → F)`. Built as
`frsEvalOnPoints ∘ (degreeLTEquiv).symm`, mirroring `koalaEnc` with
`ReedSolomon.Folded.frsEvalOnPoints` in place of `evalOnPoints` (the scalar
`s = 1` case). The codeword alphabet is `A = Fin 32 → KoalaSextic`. -/
noncomputable def koalaFRSEnc :
    (Fin (2 ^ 20) → KoalaSextic) →ₗ[KoalaSextic] (Fin (2 ^ 16) → Fin 32 → KoalaSextic) :=
  (frsEvalOnPoints koalaFRSDomain 32 koalaFoldω).domRestrict
      (Polynomial.degreeLT KoalaSextic (2 ^ 20))
    ∘ₗ (Polynomial.degreeLTEquiv KoalaSextic (2 ^ 20)).symm.toLinearMap

/-- **Injectivity of the folded encoder** ([ABF26] Definition 6.1's "code as the
injective map"). Mathematically this would follow from `(L, s)`-admissibility of
`koalaFoldω` (`ReedSolomon.Folded.Admissible`, the GR08 condition that the `s·|L|`
folded evaluation points `{α · ω^i}` are pairwise distinct) together with
`k ≤ s·|L|` (here `2^20 ≤ 32·2^16 = 2^21`): a degree-`< k` polynomial vanishing
on `s·|L| ≥ k` distinct points is zero, so the unfolded evaluation — hence
`frsEvalOnPoints` on `degreeLT k` — would be injective. `koalaFRSDomain` is
zero-free precisely so `Admissible koalaFoldω` is not *provably false* (its
intra-orbit clause fails at `0`; see `koalaFRSDomain`).

**Owed (structural), in two parts.** (1) `ReedSolomon.Folded` provides **no**
`Admissible ω → Function.Injective (frsEvalOnPoints …)` bridge — `dim_frsCode`
takes encoder injectivity as a *hypothesis* (`h_encoder_inj`); that general lemma
would have to be added (unlike the interleaved case, whose `koalaEnc_injective`
*did* have the in-tree bridge `ReedSolomon.evalOnPoints_domRestrict_injective`).
(2) Even with the bridge, `Admissible koalaFoldω` requires multiplicative-order
facts about `ω` in the **noncomputable** `GaloisField KoalaBear.fieldSize 6`,
not available `sorry`-free here (the multiplicative analogue of the additive
characteristic argument behind `koalaDomain`; cf. the Session 1a finding). This
is the FRS counterpart of the owed external dependencies carried by the
`koalaIRS` anchors — a named, legitimately-owed gap, not a hand-wave. -/
theorem koalaFRSEnc_injective : Function.Injective koalaFRSEnc := by
  sorry

/-- The folded-RS Proximity-Prize parameter point: the KoalaBear-sextic regime
with folding `s = 2^5 = 32` (`|F| = q^6 ≈ 2^186`, `ρ = 1/2`, eval domain
`|L| = 2^16`, message `k = 2^20`, `t = 128`). The codeword alphabet is the folded
`A = Fin 32 → KoalaSextic`; the `A = F` scalar case is `koalaIRS`. As with
`koalaIRS`, δ is swept inside `bestProvableError` (no pinned δ). -/
noncomputable def koalaFRS : ToyParams := by
  haveI : Fintype KoalaSextic := Fintype.ofFinite _
  classical
  exact
    { F := KoalaSextic
      ι := Fin (2 ^ 16)
      A := Fin 32 → KoalaSextic
      k := 2 ^ 20
      enc := koalaFRSEnc
      enc_injective := koalaFRSEnc_injective
      t := 128
      q := KoalaBear.fieldSize
      ext := 6
      ρ := 1 / 2
      s := 32
      n := 2 ^ 16 }

/-- **Folded-RS minimum relative distance** (the owed external, path (b) of the
FRS-anchor-reduction session). `minRelHammingDistCode koalaFRS.code = 32769/65536`,
the folded-Singleton (MDS-type) distance for `FRS[F, L, 2^20, 32, ω]`: a nonzero
degree-`< k = 2^20` polynomial has `< k` roots, so it vanishes on `< (k-1)/s =
32767` *whole* folded symbols (each pools `s = 32` field evaluations on the
admissible orbit `{α·ω^i}`), hence the folded Hamming distance is
`D = |L| - 32767 = 65536 - 32767 = 32769` and `δ_min = D/|L| = 32769/65536`.

This is the FRS counterpart of `koalaIRS_minRelDist` (which is proved sorry-free
via `ReedSolomon.minDist_eq'` + the MDS bridge). The folded analogue is **owed**:
`ReedSolomon.Folded` provides `dim_frsCode` but **no** minimum-distance lemma, and
the folded-Singleton count rests on `(L, s)`-admissibility of `koalaFoldω` — the
multiplicative-order facts unavailable `sorry`-free over the noncomputable
`GaloisField` (the same gap behind `koalaFRSEnc_injective`). It is admitted as one
named external, exactly as the `koalaIRS` anchors rest on their `ε_mca` admit; both
anchors below pin their δ-window through it. -/
theorem koalaFRS_minRelDist :
    minRelHammingDistCode koalaFRS.code = (32769 / 65536 : ℚ≥0) := by
  -- Folded-Singleton bound + (L,s)-admissibility of koalaFoldω over the noncomputable
  -- GaloisField (cf. koalaFRSEnc_injective). Owed external; path (b). Phase-5/external.
  sorry

/-- **Attack-side spot-check integer leaf (sorry-free):** `2^(-128.01) ≤
(32767/65536)^128`. The crux of the folded MDS sweep-floor. Split off `2^(-128)`:
since `32767/65536 = (32767/32768)·(1/2)`, this reduces to `2^(-0.01) ≤
(32767/32768)^128`. Bernoulli (`one_add_mul_le_pow`) gives `(32767/32768)^128 =
(1 - 1/32768)^128 ≥ 1 - 128/32768 = 255/256`, and `2^(-0.01) ≤ 255/256` is the
**proven integer inequality** `256^100 ≤ 2·255^100` (`log₁₀`: `100·2.4082 =
240.82 ≤ 0.301 + 240.65`). No float `#eval`. (True value `(32767/65536)^128 ≈
2^(-128.006)`, comfortably above the `2^(-128.01)` ceiling.) -/
theorem koalaFRS_spotcheck_lb :
    (2 : ℝ≥0) ^ (-(128.01 : ℝ)) ≤ ((32767 : ℝ≥0) / 65536) ^ (128 : ℕ) := by
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [show (-128.01 : ℝ) = (-0.01 : ℝ) + (-(128 : ℝ)) by norm_num]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [show (32767:ℝ)/65536 = (32767/32768) * (1/2) by ring]
  rw [mul_pow]
  rw [show ((1:ℝ)/2)^128 = 2^(-(128:ℝ)) by
    rw [Real.rpow_neg (by norm_num), show (128:ℝ) = ((128:ℕ):ℝ) by norm_num,
        Real.rpow_natCast]; norm_num]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hbern : (255 : ℝ) / 256 ≤ (32767/32768 : ℝ)^128 := by
    have := one_add_mul_le_pow (a := (-1/32768:ℝ)) (by norm_num) 128
    linarith
  have h2neg : (2:ℝ)^(-0.01:ℝ) ≤ 255/256 := by
    apply le_of_pow_le_pow_left₀ (n := 100) (by norm_num) (by positivity)
    rw [← Real.rpow_natCast ((2:ℝ)^(-0.01:ℝ)) 100]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  linarith [hbern, h2neg]

/-- **Provable-side spot-check integer leaf (sorry-free):** `(41/48)^128 ≤ 2^(-29)·
(116/125)`, the dominant term of the §6.3.2 `r = 8` provable bound at `δ = 7/48`.
Reduced to the integer fact `41^128·2^29·125 ≤ 116·48^128` (`log₁₀`: `128·1.6128 +
8.73 + 2.10 = 217.27 ≤ 2.06 + 215.30 = 217.36`). A proven inequality, no float
`#eval`. (True value `(41/48)^128 ≈ 2^(-29.1085)`; the `2^(-29)·116/125 ≈
2^(-29.106)` ceiling leaves room for the list-size term below `2^(-29.10)`.)

**Maintainer note — tuned split, thin margin.** The integer core holds with ratio
`≈ 1.0005`; the constants `116/125` here and `1/200` in the `ε_mca` admit are
co-tuned so that `116/125 + 1/200 = 933/1000` closes against `2^(-0.10)` in
`koalaFRS_combine` (also razor-thin, `≈ 1.00035`). Do **not** nudge either constant
without re-checking both integer inequalities in python — they are individually
correct but have little slack. -/
theorem koalaFRS_spotcheck :
    ((41 : ℝ≥0) / 48) ^ (128 : ℕ) ≤ (2 : ℝ≥0) ^ (-(29 : ℝ)) * (116 / 125) := by
  have h : ((((41 : ℝ≥0) / 48) ^ (128 : ℕ) : ℝ≥0) : ℝ) ≤
           (((2 : ℝ≥0) ^ (-(29 : ℝ)) * (116 / 125) : ℝ≥0) : ℝ) := by
    push_cast [NNReal.coe_rpow]
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        show (29:ℝ) = ((29:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [div_pow]
    rw [show ((2:ℝ)^(29:ℕ))⁻¹ * (116/125) = 116 / ((2:ℝ)^(29:ℕ) * 125) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast (by norm_num : (41:ℕ)^128 * (2^29 * 125) ≤ 116 * 48^128)
  exact_mod_cast h

/-- **Provable-side combination leaf (sorry-free):** `2^(-29)·(933/1000) ≤
2^(-29.10)`, closing the §6.3.2 lower-anchor sum. After the spot-check
(`116/125`) and the owed `ε_mca` term (`1/200`) are added, `116/125 + 1/200 =
933/1000`; this leaf certifies `933/1000 ≤ 2^(-0.10)` via the **proven integer
inequality** `2·933^10 ≤ 1000^10` (`log₁₀`: `0.301 + 10·2.9699 = 30.00 ≤ 30`). No
float `#eval`. -/
theorem koalaFRS_combine :
    (2 : ℝ≥0) ^ (-(29 : ℝ)) * (933 / 1000) ≤ (2 : ℝ≥0) ^ (-(29.10 : ℝ)) := by
  rw [show (-(29.10 : ℝ)) = (-(0.10 : ℝ)) + (-(29 : ℝ)) by norm_num]
  rw [NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
  rw [mul_comm ((2 : ℝ≥0) ^ (-(0.10 : ℝ))) ((2 : ℝ≥0) ^ (-(29 : ℝ)))]
  gcongr
  apply le_of_pow_le_pow_left₀ (n := 10) (by norm_num) (by positivity)
  have key : ((2:ℝ≥0)^(-(0.10:ℝ)))^(10:ℕ) = (2:ℝ≥0)^(-1:ℝ) := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    norm_num
  rw [key, NNReal.rpow_neg_one]
  rw [← NNReal.coe_le_coe]
  push_cast
  norm_num

/-- **Folded-RS provable lower bound (`29.10` bits) at the KoalaBear/`s=32`/`t=128`
point.** Cites the §6.3.2 subspace-design analysis
(`tab:subspace-design-security-analysis`, `s = 2^5`, minimizing `r = 8`). As with
`arklib_lowerBound_irs_t128`, the proof is a **full formalized derivation down to
named owed externals** (no longer an opaque `sorry`):

1. **Pick `δ := 7/48`** — the `r = 8` τ-subspace-design operating point (`τ(r+1) =
   τ(9) = s·ρ/(s−r+1) = 32·(1/2)/(32−9+1) = 2/3`, spot-check `1−δ = τ(9)+3/(2r) =
   2/3+3/16 = 41/48`). Admissible: `0 < 7/48 < δ_min = 32769/65536`
   (`koalaFRS_minRelDist`). The lower bound is an infimum, so one admissible δ
   suffices (`bestProvableError_le`).
2. **Spot-check term** `(1−δ)^128 = (41/48)^128 ≤ 2^(-29)·(116/125)` — proven
   sorry-free in `koalaFRS_spotcheck` (integer fact `41^128·2^29·125 ≤ 116·48^128`).
3. **`winningSetSoundness` term** — bounded by the **proven** L6.10 bridge
   `winningSetSoundness_le_epsMCA_add` down to `ε_mca(C, 7/48) + |Λ|/|F|`, which the
   single owed external τ-subspace-design admit caps at `2^(-29)·(1/200)` (the
   actual subspace-design list-size figure is `≈ 2^(-166.8)`, far below this).
4. The convex combination is then `≤ 2^(-29)·(116/125 + 1/200) = 2^(-29)·(933/1000)
   ≤ 2^(-29.10)` (`koalaFRS_combine`, integer fact `2·933^10 ≤ 1000^10`).

**Why `bits := 29.10`, not `29.11`.** `(41/48)^128 = 2^(-29.1085)` *exactly* (the
convex combination always dominates this spot-check term), so the strict provable
ceiling is `2^(-29.1085)` and an honest **lower** bound must round the magnitude
**down**: `29.10`, not the display-rounded `29.11`. This is the same round-down
discipline as the interleaved anchor (`64 → 63.99`); the earlier opaque `sorry`
quoted the table's 2-dp magnitude `29.11`, which is unprovable as a strict bound
(`2^(-29.1085) > 2^(-29.11)`).

**The owed external** (τ-subspace-design `ε_mca`; `koalaFRSEnc_injective` flows in
through the bridge). Below the folded unique-decoding radius the `ε_mca`/`|Λ|`
terms are negligible (`≈ 2^(-166.8)`); like every ArkLib `ε_mca` upper bound this
is a by-design external literature admit (BCHKS25/ACFY25/KKH26 subspace-design
list-decodability), the FRS counterpart of the `koalaIRS` owed `ε_mca`.

**Why folding at fixed `t = 128` is not where FRS wins.** `s = 32` gives only
`≈ 29` provable bits (for `s ≤ 2^4` *no* soundness is provable at `t = 128`).
Folding's payoff is on two other axes: larger folding closes the gap
(`s = 2^12`, `r = 108`: `2^(-118.14)`, a `≈ 10`-bit gap), and the
128-bit-enforcing construction reaches `2^(-128.03)` provable soundness at
repetition `t = 563`, `r = 8`, argument size `417.9 KiB`
(`tab:subspace-design-128bit-security`) — the argument-size metric on which FRS
beats interleaved RS. -/
noncomputable def frsLowerBound : SecurityLowerBound koalaFRS where
  bits := 29.10
  proof := by
    -- ABF26-§6.3.2, fully formalized **down to one external coding-theory bound**.
    -- δ := 7/48 (the r=8 τ-subspace-design point). One admissible δ suffices
    -- (`bestProvableError_le`); the convex combination splits into the spot-check
    -- term (`koalaFRS_spotcheck`, proven) and the `winningSetSoundness` term,
    -- bounded by the **proven** L6.10 bridge down to `ε_mca + |Λ|/|F|` (single owed
    -- external admit). Sum `≤ 2^(-29)·933/1000 ≤ 2^(-29.10)` (`koalaFRS_combine`).
    have hmin : ((minRelHammingDistCode koalaFRS.code : ℚ≥0) : ℝ≥0) = (32769 / 65536 : ℝ≥0) := by
      rw [koalaFRS_minRelDist]; push_cast; norm_num
    have hδmem : (7 / 48 : ℝ≥0) ∈
        Set.Ioo (0 : ℝ≥0) ((minRelHammingDistCode koalaFRS.code : ℝ≥0)) := by
      rw [Set.mem_Ioo, hmin]; constructor <;> norm_num
    refine le_trans (bestProvableError_le koalaFRS hδmem) ?_
    rw [ENNReal.coe_le_coe]
    have ht : koalaFRS.t = 128 := rfl
    rw [ht]
    have h41 : (1 : ℝ≥0) - 7 / 48 = 41 / 48 := tsub_eq_of_eq_add (by norm_num)
    rw [h41]
    -- The `winningSetSoundness` term via the proven L6.10 bridge, then the external bound.
    have hW : winningSetSoundness koalaFRS.enc (7 / 48) ≤ (2 : ℝ≥0) ^ (-(29 : ℝ)) * (1 / 200) := by
      refine le_trans (winningSetSoundness_le_epsMCA_add (C := koalaFRS.code)
        (7 / 48 : ℝ≥0) hδmem koalaFRS.enc koalaFRS.enc_injective rfl) ?_
      -- ★ THE single owed external coding-theory bound: at the folded `r = 8` point
      --   `ε_mca(frsCode, 7/48) + |Λ(frsCode^{≡2}, 7/48)|/|F| ≤ 2^(-29)·(1/200)`.
      -- The τ-subspace-design list-decodability bound (lemma:subspace-design-are-list-
      -- decodable + lemma:interleaving-list-decoding) puts the actual figure at
      -- `≈ 2^(-166.8)`, far below this ceiling. Every such `ε_mca`/`|Λ|` upper bound in
      -- ArkLib is a by-design external admit (BCHKS25/ACFY25/KKH26); this anchor inherits
      -- exactly that single external dependency, plus `koalaFRSEnc_injective` through the
      -- bridge. Phase-5/external-owed.
      sorry
    have h1ms : (1 - ((41 : ℝ≥0) / 48) ^ (128 : ℕ)) ≤ 1 := tsub_le_self
    calc ((41 : ℝ≥0) / 48) ^ koalaFRS.t
            + winningSetSoundness koalaFRS.enc (7 / 48) * (1 - ((41 : ℝ≥0) / 48) ^ koalaFRS.t)
        ≤ (2 : ℝ≥0) ^ (-(29 : ℝ)) * (116 / 125) + (2 : ℝ≥0) ^ (-(29 : ℝ)) * (1 / 200) := by
          rw [ht]
          refine add_le_add koalaFRS_spotcheck ?_
          calc winningSetSoundness koalaFRS.enc (7 / 48) * (1 - ((41 : ℝ≥0) / 48) ^ (128 : ℕ))
              ≤ (2 : ℝ≥0) ^ (-(29 : ℝ)) * (1 / 200) * 1 :=
                mul_le_mul hW h1ms zero_le' (by positivity)
            _ = (2 : ℝ≥0) ^ (-(29 : ℝ)) * (1 / 200) := mul_one _
      _ = (2 : ℝ≥0) ^ (-(29 : ℝ)) * (933 / 1000) := by rw [← mul_add]; congr 1; norm_num
      _ ≤ (2 : ℝ≥0) ^ (-(29.10 : ℝ)) := koalaFRS_combine

/-- **Folded-RS attack upper bound (`128.01` bits) at the KoalaBear/`s=32`/`t=128`
point — the δ-sweep floor, certified from the spot-check term alone.** As of the
FRS-anchor-reduction session the proof is a **full formalized reduction** (no longer
an opaque `sorry`): `le_bestProvableError` reduces the infimum-`≥` goal to a per-δ
floor over the window `(0, δ_min)`, and at *every* admissible δ the convex
combination dominates its round-2 spot-check term `(1-δ)^t` (drop the nonnegative
`winningSetSoundness` term), which is `≥ (1-δ_min)^128` by monotonicity. The folded
code's **MDS relative distance** `δ_min = 32769/65536` (`koalaFRS_minRelDist`) pins
`1 - δ > 32767/65536`, and `(32767/65536)^128 ≥ 2^(-128.01)` is the sorry-free leaf
`koalaFRS_spotcheck_lb`. So the **only owed external is the folded distance** — no
Elias/list-size lower bound enters (strictly better-owed than the interleaved
attack `listDecoding_upperBound_attack`, which owes two list-size bounds).

**Why `128.01`, and stronger than the paper's per-`δ*` reading.** `(1-δ_min)^128 =
(32767/65536)^128 ≈ 2^(-128.006)`, so the ceiling rounds **up** to `128.01`. The
§6.3.2 Elias table (`tab:subspace-elias-lowerbound-thresholds`, `δ* = 0.499`)
reports `2^(-127.63) = (1-0.499)^128`, the *point* soundness at `δ*` — **not** the
sweep floor: just above `δ*` the spot-check keeps dropping toward `2^(-128)` at
`δ_min`, the same sub-band subtlety that forced the interleaved ceiling
`116.49 → 117`. The owed fact here is a *distance* bound, not a list-size bound. -/
noncomputable def frsUpperBound_attack : SecurityUpperBound koalaFRS where
  bits := 128.01
  proof := by
    -- Sweep floor from the spot-check term alone, fully formalized **down to the
    -- owed folded distance** `koalaFRS_minRelDist`. `le_bestProvableError` reduces
    -- to a per-δ floor over (0, δ_min = 32769/65536); drop the nonnegative
    -- winningSetSoundness term, then `(1-δ)^128 ≥ (32767/65536)^128 ≥ 2^(-128.01)`
    -- by monotonicity + `koalaFRS_spotcheck_lb`. No Elias/list-size bound needed.
    refine le_bestProvableError koalaFRS (fun δ hδ => ?_)
    have hmin : ((minRelHammingDistCode koalaFRS.code : ℚ≥0) : ℝ≥0) = (32769 / 65536 : ℝ≥0) := by
      rw [koalaFRS_minRelDist]; push_cast; norm_num
    rw [Set.mem_Ioo, hmin] at hδ
    obtain ⟨hδpos, hδlt⟩ := hδ
    rw [ENNReal.coe_le_coe]
    have ht : koalaFRS.t = 128 := rfl
    rw [ht]
    -- Drop the nonnegative winningSetSoundness term, floor by the spot-check term.
    refine le_trans ?_ (le_add_of_nonneg_right zero_le')
    -- ⊢ 2^(-128.01) ≤ (1-δ)^128
    have h1md : (32767 / 65536 : ℝ≥0) ≤ 1 - δ := by
      apply le_tsub_of_add_le_right
      calc (32767 / 65536 : ℝ≥0) + δ ≤ 32767 / 65536 + 32769 / 65536 := by gcongr
        _ = 1 := by norm_num
    exact le_trans koalaFRS_spotcheck_lb (pow_le_pow_left₀ zero_le' h1md 128)

/-- **The folded-RS leaderboard frontier (`s = 32`, `t = 128`).** The honest
certified anchors are `29.10` provable bits and a `128.01`-bit attack ceiling (the
spot-check sweep floor; see `frsUpperBound_attack`), so the §6.3.2 gap at this
folded point is `128.01 − 29.10 = 98.91` bits. As with
`securityGap_koalaIRS_anchors`, this is a pure arithmetic readoff of the two
`bits` fields (it inherits the anchors' owed `sorry`s). At fixed `t = 128` this
gap is *wider* than the interleaved `koalaIRS` frontier (`53.01`) — folding's
advantage is argument-size at enforced 128-bit security and gap-closing at large
folding, not the fixed-`t` δ-swept frontier (see `frsLowerBound`). -/
theorem securityGap_koalaFRS :
    securityGap frsLowerBound frsUpperBound_attack = 98.91 := by
  simp only [securityGap, frsLowerBound, frsUpperBound_attack]
  norm_num

end Impl.FRS

end ToyProblem
