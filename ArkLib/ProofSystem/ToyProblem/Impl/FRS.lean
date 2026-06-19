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
  `analysis`, `r = 8`): `bestProvableError ≤ 2^(-29.11)` — the convex
  combination of the spot-check term `(τ(r+1) + 3/(2r))^128 ≈ 2^(-29.11)` and
  the list-size term `≈ 2^(-166.8)`.
* **Attack** (Y side, `tab:subspace-elias-lowerbound-thresholds`, `δ* = 0.499`):
  `bestProvableError ≥ 2^(-127.63)` via the Elias list-size lower bound on the
  folded code viewed over alphabet `B^s` of rate `ρ`.
* `securityGap = 127.63 − 29.11 = 98.52` bits.

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

Both are recorded in the docstrings of `frsLowerBound` / `securityGap_koalaFRS`
(cited, not re-derived — the numerics are owed external coding-theory results,
exactly as for `koalaIRS`).

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.3.2, Tables for folded Reed–Solomon).
-/

namespace ToyProblem

namespace Impl.FRS

open scoped NNReal ENNReal
open Polynomial ReedSolomon.Folded

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

/-- The `2^16`-point folded-RS evaluation domain `{0, 1, …, 2^16 − 1} ⊆
KoalaSextic`. Distinctness is injectivity of `Nat.cast` below the characteristic
(`2^16 ≤ KoalaBear.fieldSize ≈ 2^31`), exactly as for `koalaDomain`. -/
noncomputable def koalaFRSDomain : Fin (2 ^ 16) ↪ KoalaSextic where
  toFun i := (i.val : KoalaSextic)
  inj' i j hij := by
    have hfs : (2 ^ 16 : ℕ) ≤ KoalaBear.fieldSize := by norm_num [KoalaBear.fieldSize]
    have hi : (i : ℕ) ∈ Set.Iio KoalaBear.fieldSize := Set.mem_Iio.mpr (i.isLt.trans_le hfs)
    have hj : (j : ℕ) ∈ Set.Iio KoalaBear.fieldSize := Set.mem_Iio.mpr (j.isLt.trans_le hfs)
    exact Fin.val_injective
      (CharP.natCast_injOn_Iio KoalaSextic KoalaBear.fieldSize hi hj hij)

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
injective map"). Mathematically this follows from `(L, s)`-admissibility of
`koalaFoldω` (`ReedSolomon.Folded.Admissible`, the GR08 condition that the `s·|L|`
folded evaluation points `{α · ω^i}` are pairwise distinct) together with
`k ≤ s·|L|` (here `2^20 ≤ 32·2^16 = 2^21`): a degree-`< k` polynomial vanishing
on `s·|L| ≥ k` distinct points is zero, so the unfolded evaluation — hence
`frsEvalOnPoints` on `degreeLT k` — is injective (`dim_frsCode`'s
`h_encoder_inj` hypothesis).

**Owed (structural).** Establishing `Admissible koalaFoldω` requires
multiplicative-order facts about `ω` in the **noncomputable**
`GaloisField KoalaBear.fieldSize 6`, which are not available `sorry`-free here —
the multiplicative analogue of the additive characteristic argument used for
`koalaDomain` (cf. the Session 1a finding). This is the FRS counterpart of the
owed external numerics carried by the `koalaIRS` anchors; it is a named,
legitimately-owed gap, not a hand-wave. -/
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

/-- **Folded-RS provable lower bound (≈29 bits) at the KoalaBear/`s=32`/`t=128`
point.** Cites the §6.3.2 subspace-design analysis
(`tab:subspace-design-security-analysis`, `s = 2^5`, minimizing `r = 8`): the RBR
knowledge soundness is `≤ 2^(-29.11)`, the convex combination of the spot-check
term `(τ(9) + 3/16)^128 = (2/3 + 3/16)^128 ≈ 2^(-29.11)` and the
subspace-design list-size term `≈ 2^(-166.8)` (with `τ(r) = s·ρ/(s − r + 1)`).

`sorry`-backed by design: the τ-subspace-design list-decodability bound
(`lemma:subspace-design-are-list-decodable` + `lemma:interleaving-list-decoding`)
and the `ε_mca` term are external coding-theory results — the FRS counterpart of
the owed numerics in `arklib_lowerBound_irs_t128`.

**Why folding at fixed `t = 128` is not where FRS wins.** `s = 32` gives only
`≈ 29` provable bits (for `s ≤ 2^4` *no* soundness is provable at `t = 128`).
Folding's payoff is on two other axes: larger folding closes the gap
(`s = 2^12`, `r = 108`: `2^(-118.14)`, a `≈ 10`-bit gap), and the
128-bit-enforcing construction reaches `2^(-128.03)` provable soundness at
repetition `t = 563`, `r = 8`, argument size `417.9 KiB`
(`tab:subspace-design-128bit-security`) — the argument-size metric on which FRS
beats interleaved RS. -/
noncomputable def frsLowerBound : SecurityLowerBound koalaFRS where
  bits := 29.11
  proof := by
    -- ABF26 §6.3.2 subspace-design analysis (tab:subspace-design-security-analysis,
    -- s = 2^5, r = 8). Provable RBR soundness ≤ 2^(-29.11); the τ-subspace-design
    -- list-decodability bound + ε_mca are owed external coding-theory results
    -- (the FRS counterpart of the koalaIRS owed numerics). Phase-5/external-owed.
    sorry

/-- **Folded-RS list-decoding attack upper bound (≈128 bits) at the KoalaBear/
`s=32`/`t=128` point.** Cites the §6.3.2 Elias soundness lower bound
(`tab:subspace-elias-lowerbound-thresholds`, `s = 2^5`): viewing the folded code
`C_B` as a block-length-`|L|` code over alphabet `B^s` of rate `ρ`, the Elias
bound gives, at `δ* = 0.499`, soundness error `≥ 2^(-127.63)` at `t = 128` — so
no δ-relaxation analysis proves more than `≈ 128` bits.

`sorry`-backed by design: the Elias list-size lower bound (`corollary:elias`) is
an external coding-theory result, exactly as for `listDecoding_upperBound_attack`
(and, as there, the genuine ceiling is a δ-sweep floor, not just the per-`δ*`
value — owed at the same status). -/
noncomputable def frsUpperBound_attack : SecurityUpperBound koalaFRS where
  bits := 127.63
  proof := by
    -- ABF26 §6.3.2 Elias lower bound (tab:subspace-elias-lowerbound-thresholds,
    -- s = 2^5, δ* = 0.499): bestProvableError ≥ 2^(-127.63) at t = 128. External
    -- list-size lower bound, as in listDecoding_upperBound_attack. Phase-5/external-owed.
    sorry

/-- **The folded-RS leaderboard frontier (`s = 32`, `t = 128`).** The honest
certified anchors are `29.11` provable bits and a `127.63`-bit attack ceiling, so
the §6.3.2 gap at this folded point is `127.63 − 29.11 = 98.52` bits. As with
`securityGap_koalaIRS_anchors`, this is a pure arithmetic readoff of the two
`bits` fields (it inherits the anchors' owed `sorry`s). At fixed `t = 128` this
gap is *wider* than the interleaved `koalaIRS` frontier (`53.01`) — folding's
advantage is argument-size at enforced 128-bit security and gap-closing at large
folding, not the fixed-`t` δ-swept frontier (see `frsLowerBound`). -/
theorem securityGap_koalaFRS :
    securityGap frsLowerBound frsUpperBound_attack = 98.52 := by
  simp only [securityGap, frsLowerBound, frsUpperBound_attack]
  norm_num

end Impl.FRS

end ToyProblem
