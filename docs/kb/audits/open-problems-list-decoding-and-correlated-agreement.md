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

## Section 1 — Grand Challenges (introduction)

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `GC1` | Grand MCA Challenge (page 5): "determine the largest `δ*_C ∈ [0, 1]` such that `ε_mca(C, δ*_C) ≤ ε*`" | present (as predicate) | `ProximityGap.grandMCAChallenge` in [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean) | existing | Stated as a generic `Prop`-valued predicate over a code `C : Submodule F (ι → F)` and a threshold `ε* : ℝ≥0`. Specialisation to the paper's RS parameter regime (ρ ∈ {1/2, 1/4, 1/8, 1/16}, ε* = 2^(-128)) is a call-site instantiation. Resolution is open. |
| `GC2` | Grand List Decoding Challenge (page 5): "determine the largest `δ*_C ∈ [0, 1]` such that `\|Λ(C^≡m, δ*_C)\| ≤ ε* · \|F\|`" | present (as predicate) | `ProximityGap.grandListDecodingChallenge` in [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean) | existing | Stated as a generic `Prop`-valued predicate. Uses `ListDecodable.Lambda` for `\|Λ(C^≡m, ·)\|` (ABF26 D2.8). Resolution is open. |

## Section 2 — Preliminaries

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `L2.1` | Polynomial identity lemma | present-but-different | `prob_schwartz_zippel_mv_polynomial` in [Instances.lean](../../../ArkLib/Data/Probability/Instances.lean); `schwartz_zippel_of_fintype` in [Interpolation.lean](../../../ArkLib/Data/MvPolynomial/Interpolation.lean) | `ABF26.polyIdentity_le` (alias) | Paper bound is `m(d-1)/|F|` for individual-degree-`<d` polynomials; ArkLib's Schwartz-Zippel gives the equivalent bound, but no paper-shaped alias yet. |
| `D2.2` | q-entropy function `H_q` | missing | none | `CodingTheory.qEntropy` in `ArkLib/Data/CodingTheory/Prelims/Entropy.lean` (new) | Needed by C3.8, T3.11, T4.17. |
| `D2.3` | Restricted Hamming distance `Δ_T` | present-but-different | `Δ₀`, `δᵣ`, `distFromCode`, `relDistFromCode` in [Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean) | `Code.restrictedRelHammingDist` | Paper restricts to a subset `T`; ArkLib only has the full-domain variants. |
| `D2.4` | Hamming-ball volume `Vol_q(δ,n)` | present-but-different | `hammingBall`, `relHammingBall` in [ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean) | `CodingTheory.hammingBallVolume` in `Prelims/Volume.lean` (new) | Sets exist; cardinality function does not. |
| `D2.5` | ECC, `δ_min`, rate | present-but-different | `Code.dist`, `Code.minDist` in [Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean); `LinearCode.rate` in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | existing + `scoped notation "δ_min"`, `scoped notation "ρ"` in `ABF26Notation.lean` (new) | Paper uses `C ⊆ Σ^n`; ArkLib uses function spaces. Mathematically equivalent. |
| `L2.6` | Singleton bound | present | `singleton_bound`, `singleton_bound_linear` in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | existing | No action; consider adding an `IsMDS` predicate equal to `ρ = 1 − δ_min + 1/n`. |
| `D2.7` | F-additive code | present-but-different | `ModuleCode`, `LinearCode` in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | `CodingTheory.IsFAdditive` | Same idea modulo `Σ ≃ₗ[F] (Fin s → F)`; no F-additive predicate yet. |
| `D2.8` | `Λ(C,δ,f)` and `\|Λ(C,δ)\|` | present | `ListDecodable.Lambda_at`, `ListDecodable.Lambda`, `Lambda_at_subset_of_le`, `Lambda_mono`, `Lambda_le_ncard` in [ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean) | existing | Closed by the first Phase 1 commit; `Lambda_at` is an `abbrev` over `closeCodewordsRel`, `Lambda` is the `ℕ∞`-valued maximised list size. |
| `D2.9` | `m`-interleaved code `C^≡m` | present-but-different | `interleavedCodeSet`, `codewordStackSet` in [InterleavedCode.lean](../../../ArkLib/Data/CodingTheory/InterleavedCode.lean) | existing + `scoped notation "_^≡_"` | Matrix-based API; paper uses tuple notation. |
| `L2.10` | `\|Λ(C^≡m,δ)\| ≤ binom(b+r,r)·\|Λ\|^r` | missing | none | `InterleavedCode.lambda_le` | GGR11 bound. |
| `D2.11` | Reed-Solomon code `RS[F,L,k]` | present-but-different | `ReedSolomon.code` in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) | existing + `scoped notation "RS[" F ", " L ", " k "]"` | Parameterised by injection `ι ↪ F` rather than `L ⊆ F`. Strictly more general. |
| `D2.12` | Smooth domain | present | `ReedSolomon.Smooth` in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) | existing | Verified: typeclass requires multiplicative coset of a subgroup with order a power of two. New companion file [FftDomain.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean) provides FFT-domain machinery; not a paper-item match but noted here for completeness. |
| `D2.13` | s-interleaved RS `IRS[F,L,k,s]` | present-but-different | `ReedSolomon.code` + `interleavedCodeSet` (compositional) | `ReedSolomon.Interleaved.irsCode` in `ReedSolomon/Interleaved.lean` (new) | No dedicated alias or API. |
| `D2.14` | `(L,s)`-admissible field element | missing | none | `ReedSolomon.Folded.Admissible` | Required by D2.15. |
| `D2.15` | Folded RS `FRS[F,L,k,s,ω]` | missing | none | `ReedSolomon.Folded.frsCode` | Used pervasively in §3, §4, §6.3.2. |
| `D2.16` | τ-subspace-design code | missing | none | `CodingTheory.IsSubspaceDesign` | GX13 definition. |
| `L2.17` | `min τ(r) ≥ ρ − 1/n` | missing | none | `CodingTheory.IsSubspaceDesign.tau_lb` | GG25 lemma. |
| `T2.18` | FRS and UM are subspace-design | missing | none | `ReedSolomon.Folded.isSubspaceDesign`, `ReedSolomon.Multiplicity.isSubspaceDesign` | GK16 theorem. |
| `D2.19` | Extension field presentation `(B,F,e,ψ,φ)` | missing | none | `CodingTheory.ExtensionFieldPresentation` | New structure. |
| `D2.20` | Extension code `C_F` | missing | none | `CodingTheory.extensionCode` | Distance equality `δ_min(C_F) = δ_min(C_B)` from DP25. |
| `L2.21` | `\|Λ(C_F,δ)\| = \|Λ(C_B^e,δ)\|` | missing | none | `CodingTheory.lambda_extensionCode_eq` | BCFW25 Lemma D.3. |

## Section 3 — List Decoding

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `D3.1` | Johnson functions `J_{q,ℓ}`, `J_q`, `J` | present-but-different | `J` in [JohnsonBound/Basic.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean) | `JohnsonBound.Jqℓ`, `JohnsonBound.Jq`, existing `J` | Only the limit `J` is present. |
| `T3.2` | Johnson bound (Joh62) | present-but-different | `johnson_bound`, `johnson_bound_alphabet_free` in [JohnsonBound/Basic.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean) | `ABF26.johnson_bound` (alias using `Lambda`) | Need restatement in terms of the paper's `|Λ(C,δ)| ≤ ℓ` form. |
| `C3.3` | MDS coarse Johnson | missing | related ingredients only | `ABF26.mds_johnson` | Derivable from L2.6 + T3.2. |
| `T3.4` | τ-subspace-design list decoding | missing | none | `ABF26.subspaceDesign_list_decoding` (external) | CZ25 Thm B.5. |
| `C3.5` | Folded RS up to capacity | missing | none | `ABF26.frs_list_decoding_capacity` | Derives from T3.4 + T2.18. |
| `T3.6` | Random RS near capacity | missing | none | `ABF26.random_rs_list_decoding` (external) | AGL24 Thm 1.1. |
| `L3.7` | Elias volume bound | missing | none | `ABF26.elias_volume_bound` | Eli57. Proof in paper short enough to formalize in-tree. |
| `C3.8` | Volume-based lower bound | missing | none | `ABF26.volume_lower_bound` | Depends on D2.2 and D2.4. |
| `T3.9` | Generalized Singleton bound | missing | none | `ABF26.generalized_singleton_bound` (external) | ST20 Thm 1.2. |
| `T3.10` | Large-alphabet lower bound | missing | none | `ABF26.large_alphabet_lower_bound` (external) | BDG24, AGL23. |
| `T3.11` | Random linear code lower bound | missing | none | `ABF26.random_linear_lower_bound` (external) | GLMRSW22 Thm 4.1. |
| `T3.12` | RS superpoly over extensions | missing | none | `ABF26.rs_superpoly_extension` (external) | BKR06 Cor 2.2. |
| `T3.13` | RS large list over prime fields | missing | none | `ABF26.rs_large_list_prime` (external) | GHSZ02 Cor 20. |
| `T3.14` | Large-rate RS lower bound | missing | none | `ABF26.rs_large_rate_lower` (external) | JH01 Thm 2. |
| `T3.15` | CW07 hardness barrier | missing | none | `ABF26.rs_dlog_barrier` (external) | Algorithmic, not combinatorial; admit only. |

## Section 4 — Correlated Agreement Conjectures

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `D4.1` | `ε_ca(C,δ_fld,δ_int)` | present | `ProximityGap.epsCA`, `epsCA'`, `epsCA_curves`, `epsCA_affineSpaces`, `epsCA_mono_δ_fld`, `epsCA_antitone_δ_int`, three bridges `δ_ε_correlatedAgreement{AffineLines,Curves,AffineSpaces}_iff_epsCA{_,_curves_,_affineSpaces_}le` in [EpsilonErrors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/EpsilonErrors.lean); coexisting predicate API in [Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean) | existing | Definition, monotonicity in both arguments, and bridges to all three predicate-style API variants (`AffineLines`, `Curves`, `AffineSpaces`) closed. |
| `R4.2` | ε_ca discretization | present | `ProximityGap.epsCA_eq_of_floor_eq` in [EpsilonErrors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/EpsilonErrors.lean) | existing | General "level set" form proved (`⌊δ_int · n⌋ = ⌊δ_int' · n⌋ → ε_ca's agree`). The paper's `β`-shift idiom is a corollary when `δ_int` is a multiple of `1/n`. |
| `D4.3` | `ε_mca(C,δ)` | present | `ProximityGap.epsMCA`, helper preds `ProximityGap.pairJointAgreesOn`, `ProximityGap.mcaEvent` in [EpsilonErrors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/EpsilonErrors.lean); WHIR-specific `hasMutualCorrAgreement` still in [Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean) | existing | Code-theory MCA definition closed. The WHIR `hasMutualCorrAgreement` re-expression as a specialization of `epsMCA` is a follow-up commit. |
| `R4.4` | MCA with proximity loss intentionally undefined | present | file docstring in [EpsilonErrors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/EpsilonErrors.lean) | docstring | Documentation only; documented in the "Note on MCA with proximity loss" subsection of the file docstring. |
| `F4.5` | `ε_pg ≤ ε_ca ≤ ε_mca` | present | `ProximityGap.epsPG`, `ProximityGap.epsPG_le_epsCA`, `ProximityGap.epsCA_le_epsMCA`, `ProximityGap.epsPG_le_epsCA_le_epsMCA`, plus helper `ProximityGap.jointProximity_imp_line_close` in [EpsilonErrors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/EpsilonErrors.lean) | existing | Closed in stages; proved for `Submodule F (ι → A)`. |
| `L4.6` | `ε_mca = ε_ca` below `δ_min/2` | present-but-incomplete | `ProximityGap.epsMCA_eq_epsCA_below_udr` in [EpsilonErrors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/EpsilonErrors.lean) (admitted) | existing | Stated with a tagged external `sorry` referring to ACFY25 Lemma 4.10. Proof is non-trivial — not the obvious `δ < δ_min/2` uniqueness, but a dominance argument over `u`. Tracked in `ABF26_PLAN.md` §6 conjecture ledger. |
| `L4.7` | `ε_mca(C^≡t,δ) ≤ t·ε_mca(C,δ)` | present | `ProximityGap.epsMCA_interleaved_le` plus local helper `ProximityGap.Pr_exists_Fin_le_sum` (union-bound for finitely-indexed existentials) in [EpsilonErrors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/EpsilonErrors.lean) | existing | Proved via row-decomposition of the interleaved `mcaEvent` plus the `Pr_exists_Fin_le_sum` union bound. |
| `T4.8` | AHIV17 general-code unique-decoding | present-but-different | [`ProximityGap/AHIV22.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean) (sorry-free as of `05a010e3`) | `ABF26.ahiv17_epsCA_bound` (ε-wrapping of existing AHIV22 result) | Previously `present-but-incomplete`; PR #385 closed all sorries. Awaiting Phase 1 ε-interface to restate. |
| `T4.9.1` | RS unique-decoding Item 1 (BCIKS20 Thm 1.4) | present-but-incomplete | [`BCIKS20/AffineLines/UniqueDecoding.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/UniqueDecoding.lean), [`AffineLines/Main.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean) | `ABF26.rs_epsMCA_uniqueDecoding` | `AffineLines/Main.lean:40` has one `sorry` in the non-unique-decoding branch of `RS_correlatedAgreement_affineLines`. New supporting file [JointAgreement.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/JointAgreement.lean) provides bivariate existence machinery for closing this. |
| `T4.9.2` | RS unique-decoding Item 2 (BCHKS25 Thm 1.3) | missing | none | `ABF26.rs_epsCA_bchks25` (external) | BCHKS25 refinement. |
| `R4.10` | Small proximity-loss simplification | missing | none | `ABF26.epsCA_small_loss` | Derives from R4.2 + T4.9.2. |
| `T4.11` | 1.5-Johnson regime general linear | missing | none | `ABF26.linear_1_5_johnson` (external) | GKL24 + BGKS20. |
| `T4.12` | Johnson-range RS MCA | missing | conjectural `mca_johnson_bound_CONJECTURE` in [Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean) | `ABF26.rs_johnson_mca` (external) | BCHKS25 Thm 4.6. Existing WHIR conjecture is a different shape. |
| `T4.13` | MCA from τ-subspace-design | missing | none | `ABF26.subspaceDesign_mca` (external) | GG25 Cor 4.9. |
| `T4.14` | Folded RS MCA up to capacity | missing | none | `ABF26.frs_mca_capacity` (external) | GG25 Cor 4.10. |
| `T4.15` | Random RS MCA up to capacity | missing | none | `ABF26.random_rs_mca` (external) | GG25 Thm 5.15. |
| `T4.16` | CA lower bound near capacity | missing | none | `ABF26.epsCA_lower_capacity` (external) | BCHKS25 + KK25. |
| `T4.17` | Complete CA breakdown | missing | none | `ABF26.epsCA_breakdown` (external) | CS25 Cor 1. |
| `T4.18` | CA jump at Johnson bound | missing | none | `ABF26.epsCA_johnson_jump` (external) | BCHKS25 Cor 1.7. |
| `L4.19` | CA bounded below by sampling probability | missing | related DG25 work in [DG25/MainResults.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean) (contains 2 sorries) | `ABF26.epsCA_ge_sampling` | DG25 Thm 2.5. |
| `D4.20` | Line-decoding | missing | none | `CodingTheory.LineDecodable` in `LineDecoding.lean` (new) | GG25 Def 3.1. |
| `T4.21` | Line-decoding implies MCA | missing | none | `ABF26.lineDecodable_implies_epsMCA` | GG25 Thm 3.5. |

## Section 5 — Connections Between List Decoding and Correlated Agreement

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `T5.1` | List decoding implies MCA | missing | WHIR-specific `mca_list_decoding` in [Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean) (contains `sorry`) | `ABF26.listDecoding_implies_mca` (external) | GCXK25 Thm 3. WHIR variant is at different abstraction layer. |
| `T5.2` | Small ε_ca implies list size < `\|F\|` | missing | none | `ABF26.smallEpsCA_implies_listSmall` (external) | BCHKS25 Thm 1.9. |
| `T5.3` | CA implies list decoding for related RS | missing | none | `ABF26.epsCA_implies_listDec` (external) | CS25 Thm 2. |
| `T5.4` | Separation: list-decoding does not tightly imply CA | missing | none | `ABF26.list_vs_ca_separation` (external) | BGKS20 Lem 3.3. |

## Section 6 — Toy Problem (deferred)

All §6 items are tracked as `deferred` pending the OracleReduction security
framework gaps being closed. Plan Phase 8 holds these.

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `D6.1` | Toy problem relation `R_C^ℓ` | deferred | none | `ABF26.ToyProblem.relation` | New file under `ProofSystem/ToyProblem/`. |
| `C6.2` | Construction 6.2 | deferred | none | `ABF26.ToyProblem.construction62` | Uses oracle-reduction framework. |
| `D6.3` | Relaxed toy relation `R̃_C,δ^ℓ` | deferred | none | `ABF26.ToyProblem.relaxedRelation` | |
| `D6.4` | Erasure correction | deferred | none | `CodingTheory.SupportsErasureCorrection` | |
| `L6.5` | Every additive code supports erasure correction | deferred | none | `ABF26.fAdditive_supports_erasure` | GRS12. |
| `L6.6` | Knowledge soundness of Construction 6.2 | deferred | related framework in [OracleReduction/Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | `ABF26.construction62_knowledgeSound` | Prereq: framework sorries cleared. |
| `R6.7` | CA insufficient for L6.6 proof | deferred | none | docstring on `L6.6` | Documentation. |
| `L6.8` | Round-by-round knowledge soundness of Construction 6.2 | deferred | related framework in [OracleReduction/Security/RoundByRound.lean](../../../ArkLib/OracleReduction/Security/RoundByRound.lean) | `ABF26.construction62_rbr` | Prereq: framework sorries cleared. |
| `C6.9` | Construction 6.9 (attack target) | deferred | none | `ABF26.ToyProblem.construction69` | |
| `L6.10` | Soundness of Construction 6.9 | deferred | none | `ABF26.construction69_sound` | |
| `D6.11` | Winning set `Ω` | deferred | none | `ABF26.ToyProblem.winningSet` | |
| `L6.12` | List-decoding lower-bound attack | deferred | none | `ABF26.listDecoding_attack` | Uses B.1. |
| `L6.13` | CA lower-bound attack | deferred | none | `ABF26.ca_attack` | |
| `R6.14` | Attack reaches `ε_ca` not `ε_mca` | deferred | none | docstring on `L6.13` | Documentation. |

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
| `B.1` | Collision bound for random functions | missing | none | `ABF26.collision_bound` in `Probability/Combinatorial.lean` (new) | Self-contained proof in paper; short. |

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
