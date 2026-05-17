# Paper Audit: Open Problems in List Decoding and Correlated Agreement

Paper-to-ArkLib audit for *Open Problems in List Decoding and Correlated
Agreement* (Arnon, Boneh, Fenzi; April 8, 2026). Lists the paper's named
formal items and records whether each one is currently present in ArkLib,
missing, or present in a materially different form.

This audit is the **status snapshot**. The forward-looking roadmap lives in
[`../../../ABF26_PLAN.md`](../../../ABF26_PLAN.md). Every per-item PR is
expected to update both files in the same commit.

`ABF26.pdf` in the working tree and the file the previous audit referred to
as `paper.pdf` are the same document; the audit always refers to it by its
short name `ABF26`.

## Metadata

- **Paper**: ABF26 — *Open Problems in List Decoding and Correlated Agreement*, April 8, 2026
- **Paper SHA-256** (of `ABF26.pdf` at audit time): `e543ec6a4f3312b4383000e72e5aa23862e79cc9770ce21db2c48db679581de3`
- **Last verified against commit**: `05a010e3` (2026-05-14)
- **Audit owner**: Phase 0 of [`ABF26_PLAN.md`](../../../ABF26_PLAN.md)

## Status Legend

- `present`: close match in ArkLib, no `sorry` blocking it.
- `present-but-different`: underlying concept exists, but the interface,
  statement shape, or abstraction level differs materially from the paper.
- `present-but-incomplete`: the relevant theorem/symbol exists but the cited
  file still contains `sorry`.
- `missing`: no close formalization was found.
- `deferred`: in scope of a later phase per the plan; not currently worked
  on.

## Notes

- Rows follow the theorem-like items extracted from the PDF, plus named
  facts and remarks when they materially affect the comparison.
- The **ABF26 ID** column matches the `ABF26-*` identifiers used throughout
  [`../../../ABF26_PLAN.md`](../../../ABF26_PLAN.md) (e.g. `D2.13`, `T4.13`,
  `L4.6`).
- The **Lean target** column gives the canonical declaration name we will
  use once the plan lands. For `present` rows this is the existing name;
  for other rows it is the proposed name locked in by the plan.
- The **Lean refs** column lists existing declarations and the files
  containing them.
- "External" Lean target rows reference results the paper itself states
  without proof; per the plan they will be admitted with tagged `sorry`s.
  See the conjecture/external-result ledger in `ABF26_PLAN.md` §6.

## Drift since last audit

Three rows the previous audit flagged as `present-but-incomplete` are now
fully sorry-free, thanks to PR #385 (AHIV22, 2026-04-24), PR #463 (BCIKS20
`ReedSolomonGap`, 2026-04-30), and commit `6389c0e` (BCIKS20
`AffineSpaces`, 2026-05-05; pushed directly with no associated PR
number). Those rows are re-tagged `present` below. One file
([`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean))
still has the single `sorry` the previous audit identified at line 40 of
`RS_correlatedAgreement_affineLines`. Several files under
`BCIKS20/ListDecoding/`, `BCIKS20/WeightedAgreement.lean`,
`DG25/MainResults.lean`, and `Whir/MutualCorrAgreement.lean` retain
pre-existing `sorry`s and are surfaced in the **Existing Inconsistencies**
section below. Two supporting files relevant to the Phase 1 ε-error
migration and the still-open non-unique-decoding branch:
[`ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean)
(smooth-domain FFT infrastructure, added 2026-04-17 in PR #448) and
[`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/JointAgreement.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/JointAgreement.lean)
(bivariate-existence lemmas, added 2026-03-11 by `b333f6ba`).

**This-PR additions** (`feat/abf26-plan` branch): three in-tree sorries
discharged in proof-discharge passes after the statement layer landed:
`dim_irsCode` (D2.13 dim formula, commit `3b0cfc99`),
`hammingBallVolume_eq_ncard_hammingBall` and its sub-sorries
`card_filter_hammingDist_eq` (`c01232f3`) and the Set/Finset card conversion
(`13f02444`) for D2.4, and `minDist_div_card_eq_minRelHammingDistCode`
(`3f344a00`, via a `Set.Finite.toFinset` refactor of `minRelHammingDistCode`
to dodge a `Fintype.ofFinite` instance diamond). Several new bridge lemmas
land in `Basic/LinearCode.lean` (`IsMDS_iff_singleton_bound_tight`),
`Basic/RelativeDistance.lean` (the `minDist_div_card` bridge above plus
characterisation lemmas for `minRelHammingDistCode`), and
`Whir/MutualCorrAgreement.lean` (`proximityCondition_imp_mcaEvent_affineLine`
and the probability-level `Pr_proximityCondition_le_epsMCA`, one-way bridges
documenting the WHIR↔ABF26 MCA asymmetry recorded in commit `d01117c8`).

## Section 1 — Grand Challenges (introduction)

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `GC1` | Grand MCA Challenge (page 5): "determine the largest `δ*_C ∈ [0, 1]` such that `ε_mca(C, δ*_C) ≤ ε*`" | present (as predicate) | `ProximityGap.grandMCAChallenge` in [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean) | existing | Stated as a generic `Prop`-valued predicate over a `LinearCode ι F` and a threshold `ε* : ℝ≥0`. Specialisation to the paper's RS parameter regime (ρ ∈ {1/2, 1/4, 1/8, 1/16}, ε* = 2^(-128)) is a call-site instantiation. Resolution is open. |
| `GC2` | Grand List Decoding Challenge (page 5): "determine the largest `δ*_C ∈ [0, 1]` such that `\|Λ(C^≡m, δ*_C)\| ≤ ε* · \|F\|`" | present (as predicate) | `ProximityGap.grandListDecodingChallenge` in [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean) | existing | Stated as a generic `Prop`-valued predicate. Uses `ListDecodable.Lambda` for `\|Λ(C^≡m, ·)\|` (ABF26 D2.8). Resolution is open. |

## Section 2 — Preliminaries

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `L2.1` | Polynomial identity lemma | present-but-different | `prob_schwartz_zippel_mv_polynomial` in [Instances.lean](../../../ArkLib/Data/Probability/Instances.lean); `schwartz_zippel_of_fintype` in [Interpolation.lean](../../../ArkLib/Data/MvPolynomial/Interpolation.lean) | `ABF26.polyIdentity_le` (alias) | Paper bound is `m(d-1)/|F|` for individual-degree-`<d` polynomials; ArkLib's Schwartz-Zippel gives the equivalent bound, but no paper-shaped alias yet. |
| `D2.2` | q-entropy function `H_q` | present | `CodingTheory.qEntropy` in [Entropy.lean](../../../ArkLib/Data/CodingTheory/Basic/Entropy.lean) | existing | `noncomputable def`; uses Mathlib's `Real.logb`. Boundary case `qEntropy q 0 = 0` is a `@[simp]` lemma. |
| `D2.3` | Restricted Hamming distance `Δ_T` | present | `CodingTheory.restrictedRelHammingDist` in [RelativeDistance.lean](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean); existing full-domain `Δ₀`/`δᵣ` in [Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean) and [RelativeDistance.lean](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean) | existing | `ℝ≥0`-valued; `T = ∅` gives `0` via `NNReal`'s `0/0 = 0`. |
| `D2.4` | Hamming-ball volume `Vol_q(δ,n)` | present | `CodingTheory.hammingBallVolume` in [HammingBallVolume.lean](../../../ArkLib/Data/CodingTheory/HammingBallVolume.lean); supporting `hammingBall`/`relHammingBall` sets in [ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean) | existing | `noncomputable def` (depends on `Nat.floor` over `ℝ`). Boundary case `Vol_q(0, n) = 1` is a `@[simp]` lemma. |
| `D2.5` | ECC, `δ_min`, rate | present-but-different | `Code.dist`, `Code.minDist` in [Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean); `LinearCode.rate` in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean); bridge `minDist_div_card_eq_minRelHammingDistCode` and supporting `minRelHammingDistCode` in [RelativeDistance.lean](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean) linking the raw `Code.minDist C / n` form to `δᵣ C` (proved, via `Set.Finite.toFinset` refactor of `minRelHammingDistCode`) | existing | Paper uses `C ⊆ Σ^n`; ArkLib uses function spaces. Mathematically equivalent. Paper-style `δ_min` / `ρ` scoped-notation file was once planned but never materialised — call sites use `Code.minDist C / Fintype.card ι` and `LinearCode.rate` directly. |
| `L2.6` | Singleton bound | present | `singleton_bound`, `singleton_bound_linear`, `IsMDS` predicate (from PR #430), and `IsMDS_iff_rate_distance` bridge in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | existing | `IsMDS LC` encodes the additive Nat Singleton-tight condition `Code.dist LC.carrier = length LC - dim LC + 1`; the bridge `IsMDS_iff_rate_distance` connects it to the rate-distance form `δ_min(LC)/n = 1 - dim/n + 1/n` used by ABF26 §2-§3. |
| `D2.7` | F-additive code | present-but-different | `ModuleCode`, `LinearCode` in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | `CodingTheory.IsFAdditive` | Same idea modulo `Σ ≃ₗ[F] (Fin s → F)`; no F-additive predicate yet. |
| `D2.8` | `Λ(C,δ,f)` and `\|Λ(C,δ)\|` | present | `ListDecodable.Lambda_at`, `ListDecodable.Lambda`, `Lambda_at_subset_of_le`, `Lambda_mono`, `Lambda_le_ncard` in [ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean) | existing | Closed by the first Phase 1 commit; `Lambda_at` is an `abbrev` over `closeCodewordsRel`, `Lambda` is the `ℕ∞`-valued maximised list size. |
| `D2.9` | `m`-interleaved code `C^≡m` | present-but-different | `interleavedCodeSet`, `codewordStackSet` in [InterleavedCode.lean](../../../ArkLib/Data/CodingTheory/InterleavedCode.lean) | existing + `scoped notation "_^≡_"` | Matrix-based API; paper uses tuple notation. |
| `L2.10` | `\|Λ(C^≡m,δ)\| ≤ binom(b+r,r)·\|Λ\|^r` | missing | none | `InterleavedCode.lambda_le` | GGR11 bound. |
| `D2.11` | Reed-Solomon code `RS[F,L,k]` | present-but-different | `ReedSolomon.code` in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) | existing + `scoped notation "RS[" F ", " L ", " k "]"` | Parameterised by injection `ι ↪ F` rather than `L ⊆ F`. Strictly more general. |
| `D2.12` | Smooth domain | present | `ReedSolomon.Smooth` in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) | existing | Verified: typeclass requires multiplicative coset of a subgroup with order a power of two. New companion file [FftDomain.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean) provides FFT-domain machinery; not a paper-item match but noted here for completeness. |
| `D2.13` | s-interleaved RS `IRS[F,L,k,s]` | present | [ReedSolomon/Interleaved.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Interleaved.lean) | `ReedSolomon.Interleaved.irsCode`, plus `dim_irsCode` (proved) | Defined as `interleavedCodeSet (RS[F, L, ⌊k/s⌋])`. Dimension formula `dim(IRS) = s · (k/s)` proved via injective F-linear `(Fin s → ↥RS) → (ι → Fin s → F)` + `finrank_pi_fintype`. |
| `D2.14` | `(L,s)`-admissible field element | present | [ReedSolomon/Folded.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean) | `ReedSolomon.Folded.Admissible` | Required by D2.15. |
| `D2.15` | Folded RS `FRS[F,L,k,s,ω]` | present | [ReedSolomon/Folded.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean) | `ReedSolomon.Folded.frsCode` | Used pervasively in §3, §4, §6.3.2. |
| `D2.16` | τ-subspace-design code | present | [SubspaceDesign.lean](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean) | `CodingTheory.IsSubspaceDesign` | GX13 definition; uses `LinearMap.proj` for `A_i`. |
| `L2.17` | `min τ(r) ≥ ρ − 1/n` | stated (external admit) | [SubspaceDesign.lean](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean) | `CodingTheory.subspaceDesign_tau_lower` | GG25 lemma; tagged sorry. |
| `T2.18` | FRS and UM are subspace-design | stated (external admit; FRS half only) | [SubspaceDesign.lean](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean) | `CodingTheory.frs_is_subspaceDesign_gk16` | GK16 theorem; tagged sorry. UM half deferred pending D2.19. |
| `D2.19` | Extension field presentation `(B,F,e,ψ,φ)` | present | [ExtensionCodes.lean](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean) | `CodingTheory.ExtensionFieldPresentation` (structure), plus `IsSystematic` for the systematic variant. | `φ : F → Fin e → B` plus `φ_inv` for invertibility. Univariate-multiplicity code (D2.19's paper namesake DA.7) is a *different* item, despite sharing a number. |
| `D2.20` | Extension code `C_F` | present | [ExtensionCodes.lean](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean) | `CodingTheory.extensionCode` | Set-level definition; uses coordinate-projections `P.coord j` of D2.19. Distance equality `δ_min(C_F) = δ_min(C_B)` from DP25 not formalised. |
| `L2.21` | `\|Λ(C_F,δ)\| = \|Λ(C_B^e,δ)\|` | stated (external admit) | [ExtensionCodes.lean](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean) | `CodingTheory.lambda_extensionCode_eq_lambda_interleaved` | BCFW25 Lemma D.3; tagged sorry. |

## Section 3 — List Decoding

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `D3.1` | Johnson functions `J_{q,ℓ}`, `J_q`, `J` | present | existing `J` in [JohnsonBound/Basic.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean) (which matches paper's `J_q`); new `JohnsonBound.Jqℓ` and `JohnsonBound.Jcap` in [JohnsonBound/Family.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Family.lean) | `JohnsonBound.Jqℓ`, `JohnsonBound.J` (= paper `J_q`), `JohnsonBound.Jcap` | All three functions present. Limit relationships documented in docstrings; not formalised (paper does not prove them either). |
| `T3.2` | Johnson bound (Joh62) | stated (external admit; in-tree proof available) | absolute-distance form `johnson_bound`, `johnson_bound_alphabet_free` in [JohnsonBound/Basic.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean); paper-shaped `johnson_bound_lambda_le_ell` in [JohnsonBound/Family.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Family.lean) | `CodingTheory.johnson_bound_lambda_le_ell` | Statement closed; porting the existing absolute-distance proof to `Lambda`-form is tracked separately. |
| `C3.3` | MDS coarse Johnson | stated (external admit) | [JohnsonBound/Family.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Family.lean) | `CodingTheory.mds_johnson_lambda_le` | Derivable from L2.6 + T3.2 via `Jcap` form. |
| `T3.4` | τ-subspace-design list decoding | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.subspaceDesign_list_decoding_cz25` | CZ25 Thm B.5; tagged sorry. Uses `IsSubspaceDesign` from `SubspaceDesign.lean`. |
| `C3.5` | Folded RS up to capacity | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.frs_list_decoding_capacity_cz25` | CZ25 Cor 2.21; tagged sorry. Uses `frsCode` from `ReedSolomon/Folded.lean`. |
| `T3.6` | Random RS near capacity | missing | none | `ABF26.random_rs_list_decoding` (external) | AGL24 Thm 1.1. |
| `L3.7` | Elias volume bound | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.linear_lambda_ge_elias_volume_eli57` | Eli57; tagged sorry. Uses `hammingBallVolume` from `HammingBallVolume.lean`. |
| `C3.8` | Volume-based lower bound | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.linear_lambda_ge_entropy_volume` | Uses `qEntropy`; tagged sorry. |
| `T3.9` | Generalized Singleton bound | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.linear_C_le_generalized_singleton_st20` | ST20 Thm 1.2; tagged sorry. |
| `T3.10` | Large-alphabet lower bound | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.large_alphabet_barrier_bdg24_agl23` | BDG24, AGL23; tagged sorry. |
| `T3.11` | Random linear code lower bound | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.random_linear_lambda_lower_glmrsw22` | GLMRSW22 Thm 4.1; tagged sorry. Probability over linear codes existentially packaged as "exists a witness code". |
| `T3.12` | RS superpoly over extensions | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.rs_lambda_superpoly_extension_bkr06` | BKR06 Cor 2.2; tagged sorry. "Infinitely many q" captured as `∃ qs : ℕ → ℕ, StrictMono qs ∧ ...`. |
| `T3.13` | RS large list over prime fields | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.rs_lambda_large_prime_ghsz02` | GHSZ02 Cor 20; tagged sorry. |
| `T3.14` | Large-rate RS lower bound | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.rs_lambda_high_rate_jh01` | JH01 Thm 2; tagged sorry. |
| `T3.15` | CW07 hardness barrier | out of scope | none | `CodingTheory.rs_dlog_barrier` (external; not stated) | Algorithmic hardness (discrete-log reduction); per `ABF26_PLAN.md` §7 D2 we formalise combinatorial statements only. |

## Section 4 — Correlated Agreement Conjectures

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `D4.1` | `ε_ca(C,δ_fld,δ_int)` | present | `ProximityGap.epsCA`, `epsCA'`, `epsCA_curves`, `epsCA_affineSpaces`, `epsCA_mono_δ_fld`, `epsCA_antitone_δ_int`, three bridges `δ_ε_correlatedAgreement{AffineLines,Curves,AffineSpaces}_iff_epsCA{_,_curves_,_affineSpaces_}le` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean); coexisting predicate API in [Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean) | existing | Definition, monotonicity in both arguments, and bridges to all three predicate-style API variants (`AffineLines`, `Curves`, `AffineSpaces`) closed. |
| `R4.2` | ε_ca discretization | present | `ProximityGap.epsCA_eq_of_floor_eq` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) | existing | General "level set" form proved (`⌊δ_int · n⌋ = ⌊δ_int' · n⌋ → ε_ca's agree`). The paper's `β`-shift idiom is a corollary when `δ_int` is a multiple of `1/n`. |
| `D4.3` | `ε_mca(C,δ)` | present | `ProximityGap.epsMCA`, helper preds `ProximityGap.pairJointAgreesOn`, `ProximityGap.mcaEvent` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean); WHIR-specific `hasMutualCorrAgreement` still in [Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean) | existing | Code-theory MCA definition closed. The WHIR `hasMutualCorrAgreement` re-expression as a specialization of `epsMCA` is a follow-up commit. |
| `R4.4` | MCA with proximity loss intentionally undefined | present | file docstring in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) | docstring | Documentation only; documented in the "Note on MCA with proximity loss" subsection of the file docstring. |
| `F4.5` | `ε_pg ≤ ε_ca ≤ ε_mca` | present | `ProximityGap.epsPG`, `ProximityGap.epsPG_le_epsCA`, `ProximityGap.epsCA_le_epsMCA`, `ProximityGap.epsPG_le_epsCA_le_epsMCA`, plus helper `ProximityGap.jointProximity_imp_line_close` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) | existing | Closed in stages; proved for `Submodule F (ι → A)`. |
| `L4.6` | `ε_mca = ε_ca` below `δ_min/2` | present-but-incomplete | `ProximityGap.epsMCA_eq_epsCA_below_udr` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) (admitted) | existing | Stated with a tagged external `sorry` referring to ACFY25 Lemma 4.10. Proof is non-trivial — not the obvious `δ < δ_min/2` uniqueness, but a dominance argument over `u`. Tracked in `ABF26_PLAN.md` §6 conjecture ledger. |
| `L4.7` | `ε_mca(C^≡t,δ) ≤ t·ε_mca(C,δ)` | present | `ProximityGap.epsMCA_interleaved_le` plus local helper `ProximityGap.Pr_exists_Fin_le_sum` (union-bound for finitely-indexed existentials) in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) | existing | Proved via row-decomposition of the interleaved `mcaEvent` plus the `Pr_exists_Fin_le_sum` union bound. |
| `T4.8` | AHIV17 general-code unique-decoding | present-but-different | [`ProximityGap/AHIV22.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean) (sorry-free as of `05a010e3`) | `ABF26.ahiv17_epsCA_bound` (ε-wrapping of existing AHIV22 result) | Previously `present-but-incomplete`; PR #385 closed all sorries. Awaiting Phase 1 ε-interface to restate. |
| `T4.9.1` | RS unique-decoding Item 1 (BCIKS20 Thm 1.4) | present-but-incomplete | [`BCIKS20/AffineLines/UniqueDecoding.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/UniqueDecoding.lean), [`AffineLines/Main.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean) | `ABF26.rs_epsMCA_uniqueDecoding` | `AffineLines/Main.lean:40` has one `sorry` in the non-unique-decoding branch of `RS_correlatedAgreement_affineLines`. New supporting file [JointAgreement.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/JointAgreement.lean) provides bivariate existence machinery for closing this. |
| `T4.9.2` | RS unique-decoding Item 2 (BCHKS25 Thm 1.3) | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_bchks25_item2` | BCHKS25 Thm 1.3; tagged sorry. Tighter than T4.8 in the `δ_min/3`-to-Johnson regime. |
| `R4.10` | Small proximity-loss simplification | stated (derived; external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_small_loss_r4_10` | Tagged sorry; derives from R4.2 + T4.9.2 once both are proved. |
| `T4.11` | 1.5-Johnson regime general linear | stated (external admit, 2 items) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.linear_epsMCA_1_5_johnson_gkl24`, `CodingTheory.linear_epsCA_1_5_johnson_bgks20` | Both Items stated with tagged sorries (GKL24 Thm 3 and BGKS20 Lem 3.2). |
| `T4.12` | Johnson-range RS MCA | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsMCA_johnson_range_bchks25` | BCHKS25 Thm 4.6; tagged sorry. Existing WHIR conjecture is a different shape. |
| `T4.13` | MCA from τ-subspace-design | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.subspaceDesign_epsMCA_gg25` | GG25 Cor 4.9; tagged sorry. Uses `IsSubspaceDesign`. |
| `T4.14` | Folded RS MCA up to capacity | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.frs_epsMCA_capacity_gg25` | GG25 Cor 4.10; tagged sorry. Uses `frsCode`. |
| `BCGM25` (extends T4.13/T4.14) | Polynomial-generator MCA | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.subspaceDesign_epsMCA_polynomial_generators_bcgm25` | BCGM25 (footnote 2 of ABF26 intro); extends T4.13/T4.14 to polynomial generators beyond affine lines. Tagged sorry. |
| `T4.15` | Random RS MCA up to capacity | missing (deferred — needs uniform-subset distribution) | none | `CodingTheory.random_rs_mca` (external) | GG25 Thm 5.15. |
| `T4.16` | CA lower bound near capacity | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_lower_capacity_bchks25_kk25` | BCHKS25 + KK25; tagged sorry. `Θ(1/log n)` slack existentially packaged. |
| `T4.17` | Complete CA breakdown | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_breakdown_cs25` | CS25 Cor 1; tagged sorry. Uses `qEntropy` from `Basic/Entropy.lean`. |
| `T4.18` | CA jump at Johnson bound | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_johnson_jump_bchks25` | BCHKS25 Cor 1.7; tagged sorry. Johnson radius `J(δ) := 1 - √(1-δ)` inlined. |
| `L4.19` | CA bounded below by sampling probability | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean), related DG25 work in [DG25/MainResults.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean) (contains 2 sorries) | `CodingTheory.linear_epsCA_ge_sampling_dg25` | DG25 Thm 2.5; tagged sorry. |
| `D4.20` | Line-decoding | present | [ProximityGap/LineDecoding.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecoding.lean) | `CodingTheory.LineDecodable` | GG25 Def 3.1. |
| `T4.21` | Line-decoding implies MCA | stated (external admit) | [ProximityGap/LineDecoding.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecoding.lean) | `CodingTheory.lineDecodable_imp_epsMCA_le` | GG25 Thm 3.5. Proof admitted as external; tagged sorry. |

## Section 5 — Connections Between List Decoding and Correlated Agreement

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `T5.1` | List decoding implies MCA | stated (external admit) | [Connections/ListDecodingAndCA.lean](../../../ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean); WHIR-specific `mca_list_decoding` in [Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean) (contains `sorry`) | `CodingTheory.linear_listSize_to_epsMCA_gcxk25` | GCXK25 Thm 3; tagged sorry. WHIR variant is at different abstraction layer. |
| `T5.2` | Small ε_ca implies list size < `\|F\|` | stated (external admit) | [Connections/ListDecodingAndCA.lean](../../../ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean) | `CodingTheory.rs_epsCA_small_implies_lambda_lt_F_bchks25` | BCHKS25 Thm 1.9; tagged sorry. |
| `T5.3` | CA implies list decoding for related RS | stated (external admit) | [Connections/ListDecodingAndCA.lean](../../../ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean) | `CodingTheory.rs_epsCA_implies_lambda_extended_cs25` | CS25 Thm 2; tagged sorry. |
| `T5.4` | Separation: list-decoding does not tightly imply CA | stated (external admit) | [Connections/ListDecodingAndCA.lean](../../../ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean) | `CodingTheory.rs_epsCA_separation_bgks20` | BGKS20 Lem 3.3; tagged sorry. Includes both no-loss and proximity-loss forms. |

## Section 6 — Toy Problem (deferred)

All §6 items are tracked as `deferred` pending the OracleReduction security
framework gaps being closed. Plan Phase 8 holds these.

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `D6.1` | Toy problem relation `R_C^ℓ` | present | `ToyProblem.relation` in [Definitions.lean](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean) | `ToyProblem.relation` | Existence-of-message-matrix form; works for any `Set`-shaped code. |
| `C6.2` | Construction 6.2 | present-but-incomplete | `ToyProblem.Protocol.pSpec`, `StmtIn`, `OStmtIn`, `WitIn`, `accepts`, `accepts_of_relation` in [Protocol.lean](../../../ArkLib/ProofSystem/ToyProblem/Protocol.lean) | same | ProtocolSpec (3 rounds: γ challenge / g claim / spot-checks), input/oracle/witness types, and the decision predicate `accepts` landed. The honest prover and the OracleReduction object proper are deferred (point-form `accepts_of_relation` covers the completeness obligation). |
| `D6.3` | Relaxed toy relation `R̃_C,δ^ℓ` | present | `ToyProblem.relaxedRelation` in [Definitions.lean](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean) | `ToyProblem.relaxedRelation` | Existence of a valid instance `W*` with at least `(1−δ)·\|ι\|` columns agreeing on every row. |
| `D6.4` | Erasure correction | present | `ToyProblem.SupportsErasureCorrection` in [Definitions.lean](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean) | `ToyProblem.SupportsErasureCorrection` | Predicate only; correction-time `ecor` is a `ℕ` parameter (not yet enforced operationally). |
| `L6.5` | Every additive code supports erasure correction | present-but-incomplete | `ToyProblem.additive_code_supports_erasure_correction_grs12` in [SoundnessBounds.lean](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean) | same | External admit `[GRS25]`; existence form (some `ecor` works). |
| `L6.6` | Knowledge soundness of Construction 6.2 | present-but-incomplete | `ToyProblem.Protocol.protocol62_knowledgeSound` in [Protocol.lean](../../../ArkLib/ProofSystem/ToyProblem/Protocol.lean) | same | Placeholder statement; full Reduction-level formulation lands once the prover object is wired up. |
| `R6.7` | CA insufficient for L6.6 proof | present | `ToyProblem.Protocol.remark67` (narrative; sits in L6.6 docstring) in [Protocol.lean](../../../ArkLib/ProofSystem/ToyProblem/Protocol.lean) | same | Encoded as a docstring + a `Unit`-valued marker definition. |
| `L6.8` | Round-by-round knowledge soundness of Construction 6.2 | present-but-incomplete | `ToyProblem.Protocol.protocol62_rbrKnowledgeSound` in [Protocol.lean](../../../ArkLib/ProofSystem/ToyProblem/Protocol.lean) | same | ArkLib's `Verifier.rbrKnowledgeSoundness` + `KnowledgeStateFunction` (matching paper Def A.5) is in `OracleReduction/Security/RoundByRound.lean`. Wiring is deferred. |
| `C6.9` | Construction 6.9 (attack target) | deferred | related framework in [OracleReduction/Basic.lean](../../../ArkLib/OracleReduction/Basic.lean) | `ToyProblem.protocol69` | Simplified IOR `T'[C, t]`; lands with `Protocol.lean`. |
| `L6.10` | Soundness of Construction 6.9 | deferred | related framework | `ToyProblem.protocol69_knowledgeSound` | Awaits C6.9. |
| `D6.11` | Winning set `Ω` | present | `ToyProblem.winningSet` in [Definitions.lean](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean) | `ToyProblem.winningSet` | `Set F` of challenges; cardinality bounds drive L6.12 / L6.13. |
| `L6.12` | List-decoding lower-bound attack | present-but-incomplete | `ToyProblem.simplified_iop_soundness_listDecoding_lb` in [SoundnessBounds.lean](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean) | same | Tagged sorry; uses Claim B.1 via `Probability.exists_large_image_of_pairwise_collision_bound`. |
| `L6.13` | CA lower-bound attack | present-but-incomplete | `ToyProblem.simplified_iop_soundness_ca_lb` in [SoundnessBounds.lean](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean) | same | Tagged sorry; the bound is in terms of `ε_ca`, not `ε_mca` (cf. R6.14). |
| `R6.14` | Attack reaches `ε_ca` not `ε_mca` | deferred | docstring on `simplified_iop_soundness_ca_lb` | docstring | Already noted in L6.13's docstring. |

## Appendix A — Additional Preliminaries

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `A.1` | IOR completeness | present-but-different | `Reduction.completeness`, `Reduction.perfectCompleteness` in [Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | alias `ABF26.IOR.completeness` | Existing definition is more general. |
| `A.2` | IOP as IOR to trivial relation | present-but-different | same framework in [Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | docstring on `Reduction.completeness` | Conceptually supported. |
| `A.3` | IOR knowledge soundness | present-but-different | `Verifier.knowledgeSoundness` in [Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | alias `ABF26.IOR.knowledgeSoundness` | Richer execution/log model. |
| `A.4` | Knowledge state function | present | [Security/RoundByRound.lean](../../../ArkLib/OracleReduction/Security/RoundByRound.lean) | existing | Aligned with paper. |
| `A.5` | Round-by-round knowledge soundness | present-but-different | `Verifier.rbrKnowledgeSoundnessOneShot`, `Verifier.rbrKnowledgeSoundness` in [Security/RoundByRound.lean](../../../ArkLib/OracleReduction/Security/RoundByRound.lean) | alias `ABF26.IOR.rbrKnowledgeSoundness` | Abstract transcript/state-function framework. |
| `A.6` | Formal derivative `f^(s)` | present-but-different | Mathlib `Polynomial.derivative` | alias `ABF26.formalDerivative` and iterated `^[s]` | Iterated derivative wrapped in `ReedSolomon/Multiplicity.lean` (new). |
| `A.7` | Univariate multiplicity code `UM[F,L,k,s]` | missing | none | `ReedSolomon.Multiplicity.umCode` in `ReedSolomon/Multiplicity.lean` (new) | GW13, KSY14. |

## Appendix B

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `B.1` | Collision bound for random functions | present-but-incomplete | `Probability.exists_large_image_of_pairwise_collision_bound` in [Combinatorial.lean](../../../ArkLib/Data/Probability/Combinatorial.lean) | `Probability.exists_large_image_of_pairwise_collision_bound` | Statement landed; proof deferred (tagged sorry, full paper proof outline in docstring: Cauchy–Schwarz on fibres + Jensen on `x ↦ |S|²/(2x+|S|)` + averaging). |

## Existing Inconsistencies

The largest mismatches between the paper and ArkLib are structural rather
than mathematical. These drive Phase 1 of `ABF26_PLAN.md`.

1. **Correlated agreement is formalized as predicates, not error functions.**
   ArkLib currently exposes `δ_ε_correlatedAgreement...` predicates in
   [ProximityGap/Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean),
   while the paper is organized around numeric error functions `ε_pg`,
   `ε_ca`, and `ε_mca`. Closing this is the linchpin of Phase 1.

2. **General MCA is not yet a first-class coding-theory notion.**
   The TODO at the top of
   [ProximityGap/Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean)
   still lists mutual correlated agreement as missing. The
   [Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean)
   file is WHIR/proximity-generator specific and is not a drop-in
   formalization of Section 4. Phase 1 re-expresses the WHIR notion as a
   specialization of the new general `epsMCA`.

3. **The non-unique-decoding branch of BCIKS20 AffineLines is still open.**
   [BCIKS20/AffineLines/Main.lean:40](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean)
   contains a single `sorry` in `RS_correlatedAgreement_affineLines`. The
   newly-added
   [JointAgreement.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/JointAgreement.lean)
   builds the bivariate-existence machinery needed to close it.

4. **Some proximity-gap and MCA files retain `sorry`s.** Specifically:
   [BCIKS20/Curves.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean)
   (3),
   [BCIKS20/ListDecoding/Agreement.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean)
   (8),
   [Extraction.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Extraction.lean)
   (2),
   [Guruswami.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean)
   (2),
   [WeightedAgreement.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/WeightedAgreement.lean)
   (6),
   [DG25/MainResults.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean)
   (2),
   [Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean)
   (5), and
   [GuruswamiSudan/GuruswamiSudan.lean](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean)
   (3). The previously-flagged files
   [AHIV22.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean),
   [BCIKS20/ReedSolomonGap.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ReedSolomonGap.lean),
   and
   [BCIKS20/AffineSpaces.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineSpaces.lean)
   are now sorry-free thanks to PRs #385, #463, and commit `6389c0e`
   (the last was pushed directly to `main` with no associated PR number).

5. **Several code families used centrally by the paper are absent.**
   Folded Reed-Solomon (D2.14, D2.15), univariate multiplicity codes (A.7),
   subspace-design codes (D2.16, L2.17, T2.18), and extension-field codes
   (D2.19, D2.20, L2.21) are not yet represented directly in ArkLib.
   Plan Phase 3 adds them.

## Forward roadmap

The previous version of this document contained a six-phase roadmap. That
roadmap has been migrated and substantially expanded in
[`../../../ABF26_PLAN.md`](../../../ABF26_PLAN.md), which now contains:

- a nine-phase ordering with prerequisites,
- per-PR scopes,
- a per-item ledger with sub-tasks, dependencies, acceptance criteria, and
  open questions, and
- a conjecture/external-result ledger covering the 18 items the paper
  itself states without full proof.

Future updates to status, scope, or sequencing belong in `ABF26_PLAN.md`.
This audit doc is updated row-by-row as PRs land.
