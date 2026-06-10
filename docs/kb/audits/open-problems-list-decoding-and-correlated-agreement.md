# Paper Audit: Open Problems in List Decoding and Correlated Agreement

Paper-to-ArkLib audit for *Open Problems in List Decoding and Correlated
Agreement* (Arnon, Boneh, Fenzi; April 8, 2026). Lists the paper's named
formal items and records whether each one is currently present in ArkLib,
missing, or present in a materially different form.

This audit is the **status snapshot** — the canonical paper-to-Lean map. The
forward-looking phased plan and review logs are kept as local working notes
(out of the PR by design); this document records only what is present in the
tree.

Every per-item PR is expected to update this audit row in the same
commit.

The **canonical reference** for this work is the upstream LaTeX source,
`ef-millenium/ef-millenium.tex` (the authors' repo, kept as a local clone and
refreshed with `git -C ef-millenium pull`), **not** the static `ABF26.pdf`
snapshot — the `.tex` tracks edits the PDF predates (e.g. the §4.5 MCA
conjecture and Appendix C). Cited works are tracked against the authoritative
`ef-millenium/references.bib`; the audit refers to the paper by its short name
`ABF26` (eprint 2026/680).

## Metadata

- **Paper**: ABF26 — *Open Problems in List Decoding and Correlated Agreement* (eprint 2026/680)
- **Canonical source**: `ef-millenium/ef-millenium.tex` (upstream author repo, local clone; `git -C ef-millenium pull` to refresh)
- **Bibliography of record**: `ef-millenium/references.bib`
- **Audit owner**: ABF26 formalization (PR #505)

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
- The **ABF26 ID** column matches the `ABF26-*` identifiers used in the
  tagged-`sorry` comments throughout the Lean sources (e.g. `D2.13`, `T4.13`,
  `L4.6`).
- The **Lean target** column gives the canonical declaration name. For
  `present` rows this is the existing name; for other rows it is the proposed
  name.
- The **Lean refs** column lists existing declarations and the files
  containing them.
- "External" Lean target rows reference results the paper itself states
  without proof; they are admitted with tagged `sorry`s carrying the
  `-- ABF26-X.Y; external admit [Citation]` convention.

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
| `GC1` | Grand MCA Challenge (page 5): "determine the largest `δ*_C ∈ [0, 1]` such that `ε_mca(C, δ*_C) ≤ ε*`" | present (as predicate) | `ProximityGap.grandMCAChallenge` in [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean) | existing | Stated as a generic `Prop`-valued predicate over a `LinearCode ι F` and a threshold `ε* : ℝ≥0`. **Phase-1 instantiation framework (2026-06-03):** RS targets `grandMCAChallengeRS` / `grandMCAChallengeRSrate`, prize regime `prizeRates` (= {1/2,1/4,1/8,1/16}) + `epsStar` (= 2^-128) + `mcaPrize`, witness-carrying `GrandMCAResolution` with one-sided `MCALowerWitness`/`MCAUpperWitness` (bound any resolution's `δ*` via `epsMCA_mono`), and bridges from `CapacityBounds` (`MCALowerWitness.ofLe`/`ofJohnsonBCHKS25`, `MCAUpperWitness.ofGt`/`ofEpsCAGt`). Statement corrected 2026-06-10: the RS wrappers (`grandMCAChallengeRS`/`grandMCAChallengeRSrate`/`mcaPrize`) now require the prize box's smooth evaluation domain via a `ReedSolomon.Smooth domain` instance argument. Resolution is open. |
| `GC2` | Grand List Decoding Challenge (page 5): "determine the largest `δ*_C ∈ [0, 1]` such that `\|Λ(C^≡m, δ*_C)\| ≤ ε* · \|F\|`" | present (as predicate) | `ProximityGap.grandListDecodingChallenge` in [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean) | existing | Stated as a generic `Prop`-valued predicate. Uses `ListDecodable.Lambda` for `\|Λ(C^≡m, ·)\|` (ABF26 D2.8). **Phase-1 mirror (2026-06-03):** `grandListDecodingChallengeRS` + `listDecodingPrize`, witness-carrying `GrandListResolution` with `ListLowerWitness`/`ListUpperWitness` (bound `δ*` via `lambda_coe_mono` from `Lambda_mono`). Statement corrected 2026-06-10: `grandListDecodingChallengeRS`/`listDecodingPrize` now require the prize box's smooth evaluation domain via a `ReedSolomon.Smooth domain` instance argument. Resolution is open. |

## Section 2 — Preliminaries

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `L2.1` | Polynomial identity lemma | present | `prob_polynomial_identity_le`, `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le`, `MvPolynomial.totalDegree_le_of_degreeOf_lt` in [Instances.lean](../../../ArkLib/Data/Probability/Instances.lean); `schwartz_zippel_of_fintype` in [Interpolation.lean](../../../ArkLib/Data/MvPolynomial/Interpolation.lean) | `prob_polynomial_identity_le` | Paper bound `m·(d-1)/|F|` for individual-degree-`<d` polynomials, realised as `prob_polynomial_identity_le`. Derived from the generalised Schwartz-Zippel wrapper `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le` (which takes any `d ≥ totalDegree P`) via the `MvPolynomial.totalDegree_le_of_degreeOf_lt` helper. The legacy specialisation `prob_schwartz_zippel_mv_polynomial` (bound `≤ n / \|F\|` when `totalDegree ≤ n`) is preserved as a one-line wrapper. |
| `D2.2` | q-entropy function `H_q` | present | `CodingTheory.qEntropy` in [Entropy.lean](../../../ArkLib/Data/CodingTheory/Basic/Entropy.lean) | existing | `noncomputable def`; uses Mathlib's `Real.logb`. Boundary case `qEntropy q 0 = 0` is a `@[simp]` lemma. |
| `D2.3` | Restricted Hamming distance `Δ_T` | present | `CodingTheory.restrictedRelHammingDist` in [RelativeDistance.lean](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean); existing full-domain `Δ₀`/`δᵣ` in [Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean) and [RelativeDistance.lean](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean) | existing | `ℝ≥0`-valued; `T = ∅` gives `0` via `NNReal`'s `0/0 = 0`. |
| `D2.4` | Hamming-ball volume `Vol_q(δ,n)` | present | `CodingTheory.hammingBallVolume` in [HammingBallVolume.lean](../../../ArkLib/Data/CodingTheory/HammingBallVolume.lean); supporting `hammingBall`/`relHammingBall` sets in [ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean) | existing | `noncomputable def` (depends on `Nat.floor` over `ℝ`). Boundary case `Vol_q(0, n) = 1` is a `@[simp]` lemma. |
| `D2.5` | ECC, `δ_min`, rate | present-but-different | `Code.dist`, `Code.minDist` in [Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean); `LinearCode.rate` in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean); bridge `minDist_div_card_eq_minRelHammingDistCode` and supporting `minRelHammingDistCode` in [RelativeDistance.lean](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean) linking the raw `Code.minDist C / n` form to `δᵣ C` (proved, via `Set.Finite.toFinset` refactor of `minRelHammingDistCode`) | existing | Paper uses `C ⊆ Σ^n`; ArkLib uses function spaces. Mathematically equivalent. Paper-style `δ_min` / `ρ` scoped-notation file was once planned but never materialised — call sites use `Code.minDist C / Fintype.card ι` and `LinearCode.rate` directly. |
| `L2.6` | Singleton bound | present | `singleton_bound`, `singleton_bound_linear`, `IsMDS` predicate (from PR #430), and `IsMDS_iff_rate_distance` bridge in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | existing | `IsMDS LC` encodes the additive Nat Singleton-tight condition `Code.dist LC.carrier = length LC - dim LC + 1`; the bridge `IsMDS_iff_rate_distance` connects it to the rate-distance form `δ_min(LC)/n = 1 - dim/n + 1/n` used by ABF26 §2-§3. |
| `D2.7` | F-additive code | present-but-different | `ModuleCode`, `LinearCode` in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | use `ModuleCode ι F (Fin s → F)` directly | `ModuleCode` / `LinearCode` *bake in* F-linear subspace structure — the paper's "F-additive" notion is realised by these existing types. Theorems quantifying over a paper-style "F-additive `Set`-coded code `C`" can write `∃ MC : Submodule F (ι → A), (MC : Set _) = C` inline rather than via a dedicated paper-shape predicate; ArkLib convention avoids alias-style wrappers for items already realised by existing types. |
| `D2.8` | `Λ(C,δ,f)` and `\|Λ(C,δ)\|` | present | `ListDecodable.closeCodewordsRel` (= point list `Λ(C,δ,f)`), `ListDecodable.Lambda`, `closeCodewordsRel_subset_of_le`, `Lambda_mono`, `Lambda_le_ncard` in [ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean) | existing | The point list `Λ(C,δ,f)` is the pre-existing `closeCodewordsRel C f δ` (no paper-shape alias: the `Lambda_at` abbrev was removed 2026-05-31). `Lambda` is the new `ℕ∞`-valued maximised list size `\|Λ(C,δ)\|`. |
| `D2.9` | `m`-interleaved code `C^≡m` | present-but-different | `interleavedCodeSet`, `codewordStackSet` in [InterleavedCode.lean](../../../ArkLib/Data/CodingTheory/InterleavedCode.lean) | existing + `scoped notation "_^≡_"` | Matrix-based API; paper uses tuple notation. |
| `L2.10` | `\|Λ(C^≡m,δ)\| ≤ binom(b+r,r)·\|Λ\|^r` | present-but-incomplete | `InterleavedCode.lambda_le_ggr11` in [InterleavedCode.lean](../../../ArkLib/Data/CodingTheory/InterleavedCode.lean) | same | External admit `[GGR11]`. Statement binds `η := δ_C − δ`, `b := ⌈δ/η⌉`, `r := ⌈log₂(δ_C/η)⌉` and shows `|Λ(C^{≡m}, δ)| ≤ (b+r choose r) · |Λ(C, δ)|^r` for all `m ≥ 1`. |
| `D2.11` | Reed-Solomon code `RS[F,L,k]` | present-but-different | `ReedSolomon.code` in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) | existing + `scoped notation "RS[" F ", " L ", " k "]"` | Parameterised by injection `ι ↪ F` rather than `L ⊆ F`. Strictly more general. |
| `D2.12` | Smooth domain | present | `ReedSolomon.Smooth` in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) | existing | Verified: typeclass requires multiplicative coset of a subgroup with order a power of two. New companion file [FftDomain.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean) provides FFT-domain machinery; not a paper-item match but noted here for completeness. |
| `D2.13` | s-interleaved RS `IRS[F,L,k,s]` | present | [ReedSolomon/Interleaved.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Interleaved.lean) | `ReedSolomon.Interleaved.irsCode`, plus `dim_irsCode` (proved) | Defined as `interleavedCodeSet (RS[F, L, ⌊k/s⌋])`. Dimension formula `dim(IRS) = s · (k/s)` proved via injective F-linear `(Fin s → ↥RS) → (ι → Fin s → F)` + `finrank_pi_fintype`. |
| `D2.14` | `(L,s)`-admissible field element | present | [ReedSolomon/Folded.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean) | `ReedSolomon.Folded.Admissible` | Required by D2.15. |
| `D2.15` | Folded RS `FRS[F,L,k,s,ω]` | present | [ReedSolomon/Folded.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean) | `ReedSolomon.Folded.frsCode` | Used pervasively in §3, §4, §6.3.2. |
| `D2.16` | τ-subspace-design code | present | [SubspaceDesign.lean](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean) | `CodingTheory.IsSubspaceDesign` | GX13 definition; uses `LinearMap.proj` for `A_i`. |
| `L2.17` | `min τ(r) ≥ ρ − 1/n` | stated (external admit) | [SubspaceDesign.lean](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean) | `CodingTheory.subspaceDesign_tau_lower` | GG25 lemma; tagged sorry. Statement corrected 2026-06-10: rate is `finrank/(s·n)` (D2.5 alphabet `F^s`), not `finrank/n` — previous form was false (C = ⊤ counterexample). |
| `T2.18` | FRS and UM are subspace-design | stated (external admit; FRS half only) | [SubspaceDesign.lean](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean) | `CodingTheory.frs_is_subspaceDesign_gk16` | GK16 theorem; tagged sorry. UM half deferred pending D2.19. Statement corrected 2026-06-10: with `ρ = k/(s·n)` the profile is `τ(r) = s·ρ/(s−r+1) = (k/n)/(s−r+1)`; previous spelling was `s`-fold too large. |
| `D2.19` | Extension field presentation `(B,F,e,ψ,φ)` | present | [ExtensionCodes.lean](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean) | `CodingTheory.ExtensionFieldPresentation` (structure wrapping `[Algebra B F]` + `Basis (Fin e) B F`), plus `IsSystematic` for the systematic variant. | Refactored to wrap Mathlib's `Algebra B F` + `Basis (Fin e) B F` directly (no parallel implementation of the field embedding / coordinate iso). `ψ := algebraMap B F`, `φ := basis.equivFun`, `coord j := proj j ∘ φ`. Univariate-multiplicity code (paper's namesake `DA.7`) is a *different* item, despite sharing a number. |
| `D2.20` | Extension code `C_F` | present | [ExtensionCodes.lean](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean) | `CodingTheory.extensionCode` (Set form) + `CodingTheory.extensionCodeSubmodule` (Submodule form, mirroring `ReedSolomon.code`'s shape in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean)) | Set-level definition; uses coordinate-projections `P.coord j` of D2.19. **All closure laws proven**: `extensionCode_add_mem` (addition), `extensionCode_psi_smul_mem` (B-side scalar via `ψ`), and `extensionCode_smul_mem` (F-scalar closure, paper's D2.20 F-linearity claim, closed via basis-expansion through `Basis.sum_equivFun` + `Finset.sum_induction`). The Submodule packaging `extensionCodeSubmodule` bundles all three into a `Submodule F (ι → F)` (consumed by downstream code that wants a linear-code type; `coe_extensionCodeSubmodule` is the carrier bridge). Distance equality `δ_min(C_F) = δ_min(C_B)` from DP25 not formalised — separate paper item. |
| `L2.21` | `\|Λ(C_F,δ)\| = \|Λ(C_B^e,δ)\|` | stated (external admit) | [ExtensionCodes.lean](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean) | `CodingTheory.lambda_extensionCode_eq_lambda_interleaved` | BCFW25 Lemma D.3; tagged sorry. |

## Section 3 — List Decoding

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `D3.1` | Johnson functions `J_{q,ℓ}`, `J_q`, `J` | present | existing `J` in [JohnsonBound/Basic.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean) (which matches paper's `J_q`); new `JohnsonBound.Jqℓ` and `JohnsonBound.Jcap` in [JohnsonBound/Family.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Family.lean) | `JohnsonBound.Jqℓ`, `JohnsonBound.J` (= paper `J_q`), `JohnsonBound.Jcap` | All three functions present. Limit relationships documented in docstrings; not formalised (paper does not prove them either). |
| `T3.2` | Johnson bound (Joh62) | stated (external admit; in-tree proof available) | absolute-distance form `johnson_bound`, `johnson_bound_alphabet_free` in [JohnsonBound/Basic.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean); paper-shaped `johnson_bound_lambda_le_ell` in [JohnsonBound/Family.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Family.lean) | `CodingTheory.johnson_bound_lambda_le_ell` | Statement closed; porting the existing absolute-distance proof to `Lambda`-form is tracked separately. Statement corrected 2026-06-10: added radicand-nonnegativity hypothesis `q/(q−1)·ℓ/(ℓ−1)·δ_min ≤ 1` (Real.sqrt truncation of a negative radicand silently inflated the radius, making the bound false). |
| `C3.3` | MDS coarse Johnson | stated (external admit) | [JohnsonBound/Family.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Family.lean) | `CodingTheory.mds_johnson_lambda_le` | Derivable from L2.6 + T3.2 via `Jcap` form. |
| `T3.4` | τ-subspace-design list decoding | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.subspaceDesign_list_decoding_cz25` | CZ25 Thm B.5; tagged sorry. Uses `IsSubspaceDesign` from `SubspaceDesign.lean`. Rounding documented 2026-06-10: paper evaluates `τ` at real `1/η`; encoded as radius at `τ(⌈1/η⌉)` and list bound at `τ(⌊1/η⌋)` (weakest faithful integer reading for non-decreasing profiles). |
| `C3.5` | Folded RS up to capacity | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.frs_list_decoding_capacity_cz25` | CZ25 Cor 2.21; tagged sorry. Uses `frsCode` from `ReedSolomon/Folded.lean`. Statement corrected 2026-06-10: FRS rate fixed to `ρ = k/(s·n)` (was `k/n`; radius and RHS were both wrong). |
| `T3.6` | Random RS near capacity | deferred | none | `ABF26.random_rs_list_decoding` (external) | AGL24 Thm 1.1. **Blocker (shared with T4.15): the statement bounds `Pr_{L ←$ (F choose n)}[…]`, requiring a uniform-subset distribution over `F`. ArkLib's `Data/Probability/` doesn't yet have this primitive; without it the type signature can't even be written. Once that infrastructure lands, the bound itself is a paper-cited external admit.** |
| `L3.7` | Elias volume bound | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.linear_lambda_ge_elias_volume_eli57` | Eli57; tagged sorry. Uses `hammingBallVolume` from `HammingBallVolume.lean`. |
| `C3.8` | Volume-based lower bound | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.linear_lambda_ge_entropy_volume` | Uses `qEntropy`; tagged sorry. |
| `T3.9` | Generalized Singleton bound | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.linear_C_le_generalized_singleton_st20` | ST20 Thm 1.2; tagged sorry. |
| `T3.10` | Large-alphabet lower bound | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.large_alphabet_barrier_bdg24_agl23` | BDG24, AGL23; tagged sorry. |
| `T3.11` | Random linear code lower bound | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.random_linear_lambda_lower_glmrsw22` | GLMRSW22 Thm 4.1; tagged sorry. Probability over linear codes existentially packaged as "exists a witness code". Statement corrected 2026-06-10: one-sided `rate ≥ ρ` (vacuous via `C = ⊤`) replaced by the two-sided pin `ρ ≤ finrank/n ≤ ρ + 1/n`. |
| `T3.12` | RS superpoly over extensions | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.rs_lambda_superpoly_extension_bkr06` | BKR06 Cor 2.2; tagged sorry. "Infinitely many q" captured as `∃ qs : ℕ → ℕ, StrictMono qs ∧ ...`. Statement corrected 2026-06-10: exponent log is base 2 (`Real.logb 2 q`; was natural `Real.log`). |
| `T3.13` | RS large list over prime fields | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.rs_lambda_large_prime_ghsz02` | GHSZ02 Cor 20; tagged sorry. |
| `T3.14` | Large-rate RS lower bound | stated (external admit) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.rs_lambda_high_rate_jh01` | JH01 Thm 2; tagged sorry. Statement corrected 2026-06-10: dropped the unsatisfiable `\|C\| = j+1` conjunct (misread of the paper's block length `\|L\| = j+1`, already encoded) and pinned the dimension `k := j−1` (rate `(j−1)/(j+1)`). |
| `T3.15` | CW07 hardness barrier | out of scope | none | `CodingTheory.rs_dlog_barrier` (external; not stated) | Algorithmic hardness (discrete-log reduction); we formalise combinatorial statements only. |

## Section 4 — Correlated Agreement Conjectures

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `D4.1` | `ε_ca(C,δ_fld,δ_int)` | present | `ProximityGap.epsCA`, `epsCA'`, `epsCA_curves`, `epsCA_affineSpaces`, `epsCA_mono_δ_fld`, `epsCA_antitone_δ_int`, three bridges `δ_ε_correlatedAgreement{AffineLines,Curves,AffineSpaces}_iff_epsCA{_,_curves_,_affineSpaces_}le` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean); coexisting predicate API in [Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean) | existing | Definition, monotonicity in both arguments, and bridges to all three predicate-style API variants (`AffineLines`, `Curves`, `AffineSpaces`) closed. |
| `R4.2` | ε_ca discretization | present | `ProximityGap.epsCA_eq_of_floor_eq` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) | existing | General "level set" form proved (`⌊δ_int · n⌋ = ⌊δ_int' · n⌋ → ε_ca's agree`). The paper's `β`-shift idiom is a corollary when `δ_int` is a multiple of `1/n`. |
| `D4.3` | `ε_mca(C,δ)` | present | `ProximityGap.epsMCA`, helper preds `ProximityGap.pairJointAgreesOn`, `ProximityGap.mcaEvent` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean); WHIR-specific `hasMutualCorrAgreement` still in [Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean) | existing | Code-theory MCA definition closed. The WHIR `hasMutualCorrAgreement` re-expression as a specialization of `epsMCA` is a follow-up commit. |
| `R4.4` | MCA with proximity loss intentionally undefined | present | file docstring in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) | docstring | Documentation only; documented in the "Note on MCA with proximity loss" subsection of the file docstring. |
| `F4.5` | `ε_pg ≤ ε_ca ≤ ε_mca` | present | `ProximityGap.epsPG`, `ProximityGap.epsPG_le_epsCA`, `ProximityGap.epsCA_le_epsMCA`, `ProximityGap.epsPG_le_epsCA_le_epsMCA`, plus helper `ProximityGap.jointProximity_imp_line_close` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) | existing | Closed in stages; proved for `Submodule F (ι → A)`. |
| `L4.6` | `ε_mca = ε_ca` below `δ_min/2` | present-but-incomplete | `ProximityGap.epsMCA_eq_epsCA_below_udr` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) (admitted) | existing | Stated with a tagged external `sorry` referring to ACFY25 Lemma 4.10. Proof is non-trivial — not the obvious `δ < δ_min/2` uniqueness, but a dominance argument over `u`. Tracked in the local conjecture ledger. |
| `L4.7` | `ε_mca(C^≡t,δ) = ε_mca(C,δ)` (canonical `.tex` equality; legacy inequality `≤ t·ε_mca(C,δ)`) | present-but-incomplete (inequality proven; equality stated, external admit) | `ProximityGap.epsMCA_interleaved_le` plus local helper `ProximityGap.Pr_exists_Fin_le_sum` (union-bound for finitely-indexed existentials) in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean); equality `ProximityGap.epsMCA_interleaved_eq` (tagged sorry) | existing | Proved via row-decomposition of the interleaved `mcaEvent` plus the `Pr_exists_Fin_le_sum` union bound. 2026-06-10: canonical `.tex` (`lemma:interleaving-mca`, ≈ lines 1718–1724) upgraded this to the equality `ε_mca(C^≡t,δ) = ε_mca(C,δ)` [Jo26], resolving a previously-open question; added as `epsMCA_interleaved_eq` (external admit, supersedes the inequality, which stays as it is proven). `[Jo26]` still needs a `references.bib` entry (TODO in file). |
| `T4.8` | AHIV17 general-code unique-decoding | present-but-different | [`ProximityGap/AHIV22.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean) (sorry-free as of `05a010e3`) | `ABF26.ahiv17_epsCA_bound` (ε-wrapping of existing AHIV22 result) | Previously `present-but-incomplete`; PR #385 closed all sorries. Awaiting Phase 1 ε-interface to restate. |
| `T4.9.1` | RS unique-decoding Item 1 (BCIKS20 Thm 1.4) | present-but-incomplete | [`BCIKS20/AffineLines/UniqueDecoding.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/UniqueDecoding.lean), [`AffineLines/Main.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean) | `ABF26.rs_epsMCA_uniqueDecoding` | `AffineLines/Main.lean:40` has one `sorry` in the non-unique-decoding branch of `RS_correlatedAgreement_affineLines`. New supporting file [JointAgreement.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/JointAgreement.lean) provides bivariate existence machinery for closing this. |
| `T4.9.2` | RS unique-decoding Item 2 (BCHKS25 Thm 1.3) | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_bchks25_item2` | BCHKS25 Thm 1.3; tagged sorry. Tighter than T4.8 in the `δ_min/3`-to-Johnson regime. Statement corrected 2026-06-10: added the enclosing `thm:ud-rs` hypothesis `δ_fld ≤ (1−ρ)/2` (both items of the paper theorem are scoped under it; without it the bound is likely false in the CS25 breakdown band). |
| `R4.10` | Small proximity-loss simplification | stated (derived; external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_small_loss_r4_10` | Tagged sorry; derives from R4.2 + T4.9.2 once both are proved. Statement corrected 2026-06-10: added the enclosing `thm:ud-rs` hypothesis `δ_fld ≤ (1−ρ)/2` (inherited from T4.9.2). |
| `T4.11` | 1.5-Johnson regime general linear | stated (external admit, 2 items) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.linear_epsMCA_1_5_johnson_gkl24`, `CodingTheory.linear_epsCA_1_5_johnson_bgks20` | Both Items stated with tagged sorries (GKL24 Thm 3 and BGKS20 Lem 3.2). |
| `T4.12` | Johnson-range RS MCA | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsMCA_johnson_range_bchks25` | BCHKS25 Thm 4.6; tagged sorry. Existing WHIR conjecture is a different shape. |
| `T4.13` | MCA from τ-subspace-design | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.subspaceDesign_epsMCA_gg25` | GG25 Cor 4.9; tagged sorry. Uses `IsSubspaceDesign`. |
| `T4.14` | Folded RS MCA up to capacity | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.frs_epsMCA_capacity_gg25` | GG25 Cor 4.10; tagged sorry. Uses `frsCode`. Statement corrected 2026-06-10: FRS rate fixed to `ρ = k/(s·n)` (was `k/n`; radius `1−ρ−η` missed capacity by a factor-`s` error). |
| `BCGM25` (extends T4.13/T4.14) | Polynomial-generator MCA | stated (external admit; defers to PR #489) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.subspaceDesign_epsCA_curves_polynomial_generators_bcgm25` | BCGM25/BSGM25 (footnote 2 of ABF26 intro). **Canonical formalization is PR #489** (`Katy/MCAgens`: `Generator`/`IsMCAGenerator`/`IsMCA` in `ProximityGap/MCAGenerator.lean`, formalizing BSGM25 Lem 4.1/4.2 + Def 4.3). This CapacityBounds entry is the ε-error survey shadow only: it uses the *curve* CA error `epsCA_curves … k` (genuine power-curve combinations `∑ γ^i·uᵢ`, distinct from T4.13's affine-line `epsMCA`), pending reconciliation with / removal in favour of #489's `IsMCAGenerator` once that merges. Was a byte-for-byte copy of T4.13 before 2026-05-31; restated. Tagged sorry. |
| `T4.15` | Random RS MCA up to capacity | deferred | none | `CodingTheory.random_rs_mca` (external) | GG25 Thm 5.15. **Blocker (shared with T3.6): needs `Pr_{L ←$ (F choose n)}[…]`. Same uniform-subset-distribution gap.** |
| `T4.16` | CA lower bound near capacity | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_lower_capacity_kkh26` | [KKH26]; tagged sorry. Attribution corrected 2026-06-10: the canonical `.tex` (`thm:ca-lower-bound`) now attributes the *proven* bound to KKH26 (the old "BCHKS25 + KK25 under conjecture" cite was stale); theorem renamed accordingly. Statement corrected same date: exact `k/n = ρ` (unsatisfiable for irrational ρ) → band `ρ ≤ k/n ≤ ρ + 1/n`; unconstrained `slack` now pinned to `Θ(1/log₂ n)` with uniform constants over an arbitrarily-large-`n` family (`∀ n₀ ∃ n ≥ n₀`), with `\|F\| = poly(n)` exponents shared across the family. |
| `T4.17` | Complete CA breakdown | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_breakdown_cs25` | CS25 Cor 1; tagged sorry. Uses `qEntropy` from `Basic/Entropy.lean`. |
| `T4.18` | CA jump at Johnson bound | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_johnson_jump_bchks25` | BCHKS25 Cor 1.7; tagged sorry. Johnson radius `J(δ) := 1 - √(1-δ)` inlined. (Sits at position T4.19 after the 2026-06 `.tex` renumbering.) Statement corrected 2026-06-10: additive window `\|F\|^{(1+ε)/2} ± 1` was unsatisfiable together with `16 ∣ n` for almost all char-2 fields; replaced by the multiplicative window `x/2 ≤ n ≤ 2x` plus guards `ε < 1`, `\|F\| ≥ 1024`. |
| `L4.19` | CA bounded below by sampling probability | stated (external admit) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean), related DG25 work in [DG25/MainResults.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean) (contains 2 sorries) | `CodingTheory.linear_epsCA_ge_sampling_dg25` | DG25 Thm 2.5; tagged sorry. |
| `D4.20` | Line-decoding | present | [ProximityGap/LineDecoding.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecoding.lean) | `CodingTheory.LineDecodable` | GG25 Def 3.1. |
| `T4.21` | Line-decoding implies MCA | stated (external admit) | [ProximityGap/LineDecoding.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecoding.lean) | `CodingTheory.lineDecodable_imp_epsMCA_le` | GG25 Thm 3.5. Proof admitted as external; tagged sorry. |
| `C4.5` | §4.5 MCA conjecture (`conj:mca-conjecture`): `ε_mca(C,δ) ≤ (1/\|F\|)·\|L\|^{c₁}/(ρ^{c₂}·η^{c₃})`, `η := 1−ρ−δ`, `δ < 1−ρ` | present (as `Prop`) | `ProximityGap.GrandChallenges.mcaConjecture`, `ProximityGap.GrandChallenges.mcaConjectureBound`, `ProximityGap.GrandChallenges.nonempty_mcaLowerWitness_of_mcaConjecture` in [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean) | new (Phase 1, 2026-06-03) | Stated as a `Prop` (∃ constants `c₁ c₂ c₃`, ∀ RS code & `δ<1−ρ`), term-by-term faithful to the source. Conjecture⇒`MCALowerWitness` link proven and axiom-clean. **Source caveat (verified 2026-06-03): this conjecture sits inside an `\ignore{…}` block in the current `.tex` (≈line 2030) — a *draft*, not a statement rendered in the compiled paper; the Lean docstring flags this.** |

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
| `D6.1` | Toy problem relation `R_C^ℓ` | present | `ToyProblem.relationFor` in [Definitions.lean](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean) | `ToyProblem.relationFor` | **Fixed-encoding** form (2026-06-10): the pre-image is taken under the code's pinned `F`-linear `encode` — the paper's "code as the injective map" (`.tex` ~1133). The earlier existential-encoding `ToyProblem.relation` (`∃ encode, …`) was **deleted**: it is defectively permissive (constraint reparameterisable through another encoding with the same image), which falsified the §6.4 violation conjuncts and the C6.2 completeness statement. |
| `C6.2` | Construction 6.2 | present | `ToyProblem.Spec.pSpec`, `Statement`, `OracleStatement`, `Witness`, `accepts`, `inputRelationFor`, `outputRelationFor`, `prover`, `verifier`, `reduction`, `oracleProver`, `oracleVerifier`, `oracleReduction`, `queryG`, `queryF`, `accepts_of_inputRelation` in [Spec/General.lean](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean) | same | Three-round `ProtocolSpec` (γ / g / spot-checks) with `OracleInterface` / `SampleableType` instances. Full honest `Prover` / `Verifier` / `Reduction` triple (computable, non-oracle) **and** `OracleProver` / `OracleVerifier` / `OracleReduction` flavour with real query-based verify body (`queryG`, `queryF` mirroring FRI's `getConst`/`queryCodeword`; query complexity `2t+1`). Honest-completeness point form `accepts_of_inputRelation` **proven** (ring + linearity). The protocol-level `oracleReduction_perfectCompleteness` stub lives in the same file (depends on `accepts_of_inputRelation` plus `OracleReduction.toReduction` plumbing — tagged sorry, tracked under the roadmap query's Phase 2, not in the audit table since it is a Lean-side strengthening rather than a separate paper item). IRS instantiation in `Impl/IRS.lean`. (Note: the 1-arity relaxed relation lives in `SimplifiedIOR.outputRelationFor`.) **Faithfulness fix (2026-06-05):** the IOR relations are now **fixed-encoding** (`inputRelationFor`/`outputRelationFor` over the verifier's own `encode`, witness tied), replacing the earlier existential-encoding `ToyProblem.relation` form under which honest completeness is unprovable/false (an adversary reparameterises the encoding — the same defect as the L6.12 attack). `oracleReduction_perfectCompleteness` is now statement-faithful; its sole residual is the ~250-line `OptionT`/`StateT`/`simulateQ` support-peel (blocker lemmas `simulateQ_list_forIn`, `simulateQ_addLift_add_liftM_*` landed in `ArkLib/ToVCVio/`). |
| `D6.3` | Relaxed toy relation `R̃_C,δ^ℓ` | present | `ToyProblem.relaxedRelationFor` in [Definitions.lean](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean) | `ToyProblem.relaxedRelationFor` | Existence of a valid instance `W*` (fixed-encoding `relationFor`, 2026-06-10 — existential family deleted, see D6.1) with at least `(1−δ)·\|ι\|` columns agreeing on every row. |
| `D6.4` | Erasure correction | present | `CodingTheory.SupportsErasureCorrection` in [Erasure.lean](../../../ArkLib/Data/CodingTheory/Erasure.lean) | `CodingTheory.SupportsErasureCorrection` | Predicate is generic (lives under `CodingTheory/`); use the in-tree name directly rather than a paper-shape `ToyProblem` alias. Both clauses of the paper's definition are encoded — (i) recovery when erasures `< δ_min·n` ∧ matching codeword, (ii) `E f = none` otherwise. The paper's correction-time parameter `ecor` is **not carried** (dropped 2026-06-10, finding A-F5): ArkLib's extractors are uniformly cost-free, so a phantom `ℕ` parameter only faked cost content. |
| `L6.5` | Every additive code supports erasure correction | present | `CodingTheory.additive_code_supports_erasure_correction_grs25`, `CodingTheory.eq_of_consistent_with_erased` in [Erasure.lean](../../../ArkLib/Data/CodingTheory/Erasure.lean) | same | **PROVEN sorry-free + axiom-clean 2026-06-10** (moved next to D6.4 — zero toy-problem content). The corrector is built classically: below `minDist C` erasures the consistent codeword is unique (`eq_of_consistent_with_erased`, Hamming-distance pigeonhole), so `Classical` choice yields the decoder; the failure clause is by construction. The paper's `O((s·n)³)` field-operation bound is out of ArkLib's cost-free model (extractors are unclocked library-wide); only existence is formalized. |
| `L6.6` | Knowledge soundness of Construction 6.2 | present-but-incomplete | `ToyProblem.Spec.protocol62_knowledgeSound` in [Spec/General.lean](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean) | same | Stated against `Verifier.knowledgeSoundness` with `relIn := outputRelationFor k encode δ` (the fixed-encoding relaxed relation `R̃²_{C,δ}`, checked against the extracted witness) and `relOut := Set.univ`. The theorem takes a linear `encode` with `Set.range encode = C`, so the code set used by `ε_mca`, `Λ`, and `δ_min` is tied to the verifier relation. Knowledge error is the **concrete** paper formula `max (ε_mca(C,δ) + \|Λ(C^{≡2},δ)\| / \|F\|) ((1−δ)^t)` (de-vacuified 2026-05-31: was an empty `∃ knowledgeError` before). Carries the paper's load-bearing `δ < δ_min(C)` hypothesis (`δ < (minRelHammingDistCode C : ℝ≥0)`, added 2026-06-02) + `[Nonempty ι]`. **`paper-proof-owed`** (ABF26's OWN §6.2 result, not an external import — re-tagged 2026-06-02); sorry on the proof only. |
| `R6.7` | CA insufficient for L6.6 proof | present | `ToyProblem.Spec.remark67` (narrative; sits in L6.6 docstring) in [Spec/General.lean](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean) | same | Encoded as a docstring + a `Unit`-valued marker definition. |
| `L6.8` | Round-by-round knowledge soundness of Construction 6.2 | present-but-incomplete | `ToyProblem.Spec.protocol62_rbrKnowledgeSound` in [Spec/General.lean](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean) | same | Stated against `Verifier.rbrKnowledgeSoundness` (paper Def A.5 ≡ ArkLib's `KnowledgeStateFunction`) with `relIn := outputRelationFor k encode δ` (checked against the extracted witness), `relOut := Set.univ`, and a linear `encode` satisfying `Set.range encode = C`. Per-challenge error is the **concrete** function (round 0 ↦ `ε_mca + \|Λ(C^{≡2},δ)\|/\|F\|`, round 2 ↦ `(1−δ)^t`); de-vacuified 2026-05-31. Carries `δ < δ_min(C)` + `[Nonempty ι]` (2026-06-02). **`paper-proof-owed`** (ABF26's OWN §6.2 result; re-tagged 2026-06-02); sorry on the proof only. |
| `C6.9` | Construction 6.9 (attack target) | present | `ToyProblem.SimplifiedIOR.pSpec`, `OutputStatement`, `OutputOracleStatement`, `OutputWitness`, `outputRelationFor`, `prover`, `verifier`, `reduction` in [Spec/SimplifiedIOR.lean](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean) | same | One-round V→P γ reducing IOR, mapping `(v, μ₁, μ₂, f₁, f₂) ↦ (v, μ₁+γ·μ₂, f₁+γ·f₂)`. Sibling file to `Spec/General.lean` (C6.2). **Only the non-oracle flavour is shipped**: an `OracleReduction` version would require declaring the combined output oracle `f_new := f₁ + γ·f₂` as an arbitrary function of `(f₁, f₂, γ)`, but the current `OracleVerifier.embed` machinery in [`OracleReduction/Basic.lean`](../../../ArkLib/OracleReduction/Basic.lean) only allows the output oracle family to be a *verbatim subset* of input oracles + prover messages. A `simOStmt`-based refactor of the framework (sketched in `Basic.lean:278, 293`) is needed before the oracle flavour can be added. The bundled-input non-oracle `reduction` captures full semantics in the meantime. |
| `L6.10` | Soundness of Construction 6.9 | present-but-incomplete | `ToyProblem.SimplifiedIOR.simplifiedIOR_knowledgeSound` in [Spec/SimplifiedIOR.lean](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean) | same | Stated against `Verifier.knowledgeSoundness` with `relIn := ToyProblem.Spec.outputRelationFor encode δ` (= witness-bearing `R̃²_{C,δ}`) and `relOut := ToyProblem.SimplifiedIOR.outputRelationFor encode δ` (= witness-bearing `R̃¹_{C,δ}`). The theorem takes a linear `encode` with `Set.range encode = C`, tying the verifier relations to the code used by the error terms. Knowledge error is the **concrete** `ε_mca(C,δ) + \|Λ(C^{≡2},δ)\|/\|F\|` (no `(1−δ)^t` term; de-vacuified 2026-05-31). Carries `δ < δ_min(C)` + `[Nonempty ι]` (2026-06-02). **`paper-proof-owed`** (ABF26's OWN §6.4 result, the 1-round form of L6.8; re-tagged 2026-06-02); sorry on the proof only. The **error-bound content** of L6.10 is separately stated as the leaderboard bridge `ToyProblem.winningSetSoundness_le_epsMCA_add` in [Leaderboard.lean](../../../ArkLib/ProofSystem/ToyProblem/Leaderboard.lean) (`winningSetSoundness enc δ ≤ ε_mca + \|Λ\|/\|F\|`, tagged sorry; relabeled 2026-06-10 — an earlier revision mislabeled that inequality itself as "L6.10", finding F4). |
| `D6.11` | Winning set `Ω` | present | `ToyProblem.winningSetFor` in [Definitions.lean](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean) | `ToyProblem.winningSetFor` | `Set F` of challenges, **fixed-encoding** (2026-06-10; existential `winningSet` deleted, see D6.1); cardinality bounds drive L6.12 / L6.13. The Def-6.11 *soundness error* `sup_{violating}\|Ω\|/\|F\|` is realised as `ToyProblem.winningSetSoundness` (per-δ, over `ViolatingInstance enc δ`) in [Leaderboard.lean](../../../ArkLib/ProofSystem/ToyProblem/Leaderboard.lean); the leaderboard's common quantity is the **δ-swept** `ToyProblem.bestProvableError` (`⨅ δ ∈ (0, δ_min), max (winningSetSoundness enc δ) ((1−δ)^t)`, redesigned 2026-06-10, finding F2 — per-side δ per the §6.3 frontier; Lean-side framework over D6.11, off the parsed table like the C6.2 completeness stub). Proven attack hooks: `epsCA_le_winningSetSoundness` (L6.13) and `listDecoding_le_winningSetSoundness` (L6.12, added 2026-06-10, finding F1.2) — both axiom-clean. |
| `L6.12` | List-decoding lower-bound attack | **present** | `ToyProblem.simplified_iop_soundness_listDecoding_lb` in [SoundnessBounds.lean](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean) | same | **PROVEN sorry-free + axiom-clean 2026-06-04** (`#print axioms` → only `propext`/`Classical.choice`/`Quot.sound`). **Statement corrected 2026-06-04 (finding S5):** conclusion `\|Ω\|.ncard ≥ N·\|F\|/(\|F\|+2N)` (canonical `.tex` final bound), against the fixed-encoding `relaxedRelationFor enc` / `winningSetFor enc`; carries `[Nonempty ι]`, linearity (`enc` injective, `range enc = C`), and certifies the violation (`¬ R̃²` conjunct). Proof completed via the message-pair reconciliation lemma `encStack_mem_closeCodewordsRel_iff` (close-codeword stack ↔ agreement set, both directions; reuses the coercion handling of `mem_winningSetFor_zero_of_relClose`): (i) Λ-enumeration as the `encStack`-bijection `Smsg ≃ Λ(C^{≡2},δ,fStar)`, (ii) the violation `(μ₁,μ₂) ∉ S_v`, (iii) membership `winImg ⊆ Ω` via `mem_winningSetFor_of_agree`. The two Claim-B.1 applications + denominator algebra were already proven (`exists_dotProduct_image_lb`, `exists_affine_image_lb`, `claimB1_bound_to_real`, `listDecoding_winning_lb`). Hosted on the leaderboard 2026-06-10 as the proven, axiom-clean corollary `ToyProblem.listDecoding_le_winningSetSoundness` (`N/(\|F\|+2N) ≤ winningSetSoundness enc δ`). |
| `L6.13` | CA lower-bound attack | **present** | `ToyProblem.simplified_iop_soundness_ca_lb` in [SoundnessBounds.lean](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean) | same | **PROVEN sorry-free + axiom-clean** (2026-06-04; **restated 2026-06-10** against the fixed-encoding `relaxedRelationFor enc` / `winningSetFor enc`, same hypothesis shape as L6.12: explicit `enc` injective with `range enc = C`, replacing the existential `∃ enc` linearity hyp — `#print axioms` re-verified, only `propext`/`Classical.choice`/`Quot.sound`). Carries `[Nonempty ι]`, `0 < ε_ca` guard (paper's "if not, vacuous"), and certifies the violation (`¬ R̃²` conjunct, via `jointAgreement_iff_jointProximity`). Helper `mem_winningSetFor_zero_of_relClose` (the `S ⊆ Ω` inclusion; the all-zero instance satisfies the pinned constraint trivially). The bound is in terms of `ε_ca`, not `ε_mca` (cf. R6.14). The attack→soundness chain `epsCA_le_winningSetSoundness` (Leaderboard.lean) is likewise real + axiom-clean. |
| `R6.14` | Attack reaches `ε_ca` not `ε_mca` | deferred | docstring on `simplified_iop_soundness_ca_lb` | docstring | Already noted in L6.13's docstring. |

## Appendix A — Additional Preliminaries

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `A.1` | IOR completeness | present-but-different | `Reduction.completeness`, `Reduction.perfectCompleteness` in [Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | use `Reduction.perfectCompleteness` directly | Paper's A.1 is realised by the existing definition (which is more general — richer execution / log model). ArkLib convention: use the in-tree name; the paper↔Lean name map lives in this Notes column rather than in an `alias` wrapper. |
| `A.2` | IOP as IOR to trivial relation | present-but-different | same framework in [Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | docstring on `Reduction.completeness` | Conceptually supported. |
| `A.3` | IOR knowledge soundness | present-but-different | `Verifier.knowledgeSoundness` in [Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | use `Verifier.knowledgeSoundness` directly | ArkLib's richer execution/log model captures the paper's narrative `(E, et, κ)` extractor presentation. No paper-shape wrapper — use the in-tree name. |
| `A.4` | Knowledge state function | present | [Security/RoundByRound.lean](../../../ArkLib/OracleReduction/Security/RoundByRound.lean) | existing | Aligned with paper. |
| `A.5` | Round-by-round knowledge soundness | present-but-different | `Verifier.rbrKnowledgeSoundnessOneShot`, `Verifier.rbrKnowledgeSoundness` in [Security/RoundByRound.lean](../../../ArkLib/OracleReduction/Security/RoundByRound.lean) | use `Verifier.rbrKnowledgeSoundness` directly | The paper's `KnowledgeStateFunction` machinery and per-round error tuple `(ε_1, …, ε_k)` map directly to the in-tree definition. No paper-shape wrapper. |
| `A.6` | Formal derivative `f^(s)` | present-but-different | Mathlib `Polynomial.derivative` | use `Polynomial.derivative` directly | Iterated `f^(s)` form is `Polynomial.derivative^[s]` (used in `ReedSolomon/Multiplicity.lean`). No paper-shape wrapper — use Mathlib's name. |
| `A.7` | Univariate multiplicity code `UM[F,L,k,s]` | present | `ReedSolomon.Multiplicity.umEvalOnPoints`, `ReedSolomon.Multiplicity.umCode`, `ReedSolomon.Multiplicity.mem_umCode_one_iff_mem_rsCode` in [ReedSolomon/Multiplicity.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean) | same | Submodule form `(Polynomial.degreeLT F k).map (umEvalOnPoints domain s)`, mirroring `ReedSolomon.code` and `ReedSolomon.Folded.frsCode`. Encoder packages `s` formal-derivative evaluations per domain point. `mem_umCode_one_iff_mem_rsCode` provides the `s = 1` collapse to plain RS (hoisted out of the `[CommRing F]` namespace to a `[Field F]` scope so the `Polynomial F` instance paths align with `ReedSolomon.code`'s). Paper requirement `char(F) ≥ k` is documented but not baked into the bare definition. |

## Appendix B

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `B.1` | Collision bound for random functions | present | `Probability.exists_large_image_of_pairwise_collision_bound` in [Combinatorial.lean](../../../ArkLib/Data/Probability/Combinatorial.lean) | `Probability.exists_large_image_of_pairwise_collision_bound` | Closed 2026-05-20. Proof route: helper lemmas `sum_fiber_sq_eq` (fiber-partition + diagonal decomposition) and `cauchy_schwarz_fiber` (`sq_sum_le_card_mul_sum_sq` over `ℝ` via cast); main theorem by contradiction (avoids Jensen): `PMF.bind`-unfolded linearity gives `E[numColls] ≤ N(N-1)ε`, while per-`φ ∈ supp` Cauchy-Schwarz + ENNReal cross-multiplication gives `numColls φ > N(N-1)ε`; `ENNReal.tsum_lt_tsum` strict-averaging closes the loop. |

## Existing Inconsistencies

The largest mismatches between the paper and ArkLib are structural rather
than mathematical. These drive the grand-challenge instantiation phase.

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

5. ~~**Several code families used centrally by the paper are absent.**~~
   *(Resolved 2026-05.)* All four families are now present in-tree, each
   reachable from a `present` or `present-but-incomplete` row above:
   Folded Reed-Solomon (D2.14, D2.15) in
   [`ReedSolomon/Folded.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean);
   univariate multiplicity codes (A.7) in
   [`ReedSolomon/Multiplicity.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean);
   subspace-design codes (D2.16, L2.17, T2.18) in
   [`SubspaceDesign.lean`](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean);
   and extension-field codes (D2.19, D2.20, L2.21) in
   [`ExtensionCodes.lean`](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean).

## Forward roadmap

The phased completion plan (grand-challenge instantiation framework, the
toy-protocol bits-of-security leaderboard, the §6 proofs, the concrete
parametrization tables, and the integration cleanups) and the per-finding
review logs are maintained as local working notes, kept out of the PR by
design. This audit doc is the in-tree status snapshot and is updated
row-by-row as PRs land.
