# Knowledge Base Log

This file is append-only.
Each entry records a notable KB event: initialization, ingest, audit creation, or major update.

## [2026-04-15] initialize | docs/kb

Created the initial knowledge-base subtree:

- `docs/kb/README.md`
- `docs/kb/index.md`
- `docs/kb/log.md`
- `docs/kb/papers/`
- `docs/kb/concepts/`
- `docs/kb/audits/`
- `docs/kb/queries/`
- `docs/kb/sources/`
- `docs/kb/_generated/`

## [2026-04-15] seed | initial paper pages

Seeded the first repository-local paper pages for currently active or already cited references:

- `ACFY24`
- `ACFY24stir`
- `BCIKS20`
- `BCS16`
- `BBS24`
- `DP24`

## [2026-04-15] seed | citation coverage stubs

Scaffolded paper pages and source metadata for the remaining citation keys currently used in
`ArkLib/**/*.lean`:

- `AHIV22`
- `BSS08`
- `FRI1216`
- `GWZC19`
- `JM24`
- `LFKN92`
- `LPS24`
- `PS94`
- `Poseidon2`
- `STIR2005`
- `Spi95`
- `codingtheory`
- `listdecoding`

## [2026-04-15] generate | bibliography and citation registries

Added initial generated outputs:

- `docs/kb/_generated/references.json`
- `docs/kb/_generated/lean-citations.json`

using the new scripts under `scripts/kb/`.

## [2026-04-15] migrate | list-decoding audit

Promoted the existing paper audit into:

- `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`

and updated tracked wiki navigation to point to the KB copy rather than to a branch-local
untracked file.

## [2026-04-15] refine | high-value paper pages

Replaced initial stubs with ArkLib-specific summaries for:

- `AHIV22`
- `LFKN92`
- `GWZC19`
- `FRI1216`

These are now better landing pages for active review and protocol work in the `InterleavedCode`,
`Sumcheck`, `Plonk`, and `Fri` subtrees.

## [2026-04-15] automate | review context helper

Added:

- `scripts/kb/review_context.py`

to resolve citation keys, KB paper pages, source metadata, and public URLs from explicit keys or
changed Lean files, with output shaped for `.github/workflows/review.yml`.

## [2026-04-15] refine | second paper-page batch

Replaced initial stubs with ArkLib-specific summaries for:

- `JM24`
- `LPS24`
- `Poseidon2`
- `BSS08`
- `STIR2005`
- `listdecoding`
- `codingtheory`

This improves the KB coverage for the `AGM`, `Data/Hash`, `ProofSystem/Stir`, and
`JohnsonBound` areas.

## [2026-04-15] refine | final cited-paper stubs

Replaced the remaining cited-paper stubs with ArkLib-specific summaries for:

- `PS94`
- `Spi95`

and added a concept hub:

- `docs/kb/concepts/polishchuk-spielman-lineage.md`

for the corrected-vs-original Polishchuk-Spielman source lineage.

## [2026-05-03] audit | BCIKS20 Appendix A rational functions

Added:

- `docs/kb/audits/bciks20-appendix-a-rational-functions.md`

to track the rational-function and Hensel-lifting declarations supporting the BCIKS20
list-decoding branch.

## [2026-05-03] prove | BCIKS20 function-field regularity API

Updated `ArkLib/Data/Polynomial/RationalFunctions.lean` with an explicit function-field `T`
variable, regular-element closure lemmas, and a concrete low-degree `ξ` regularity helper.
The Appendix A rational-functions audit now records this as the next denominator-clearing layer
toward `ClaimA2.ξ_regular`.

## [2026-05-19] queries | ABF26 PR roadmap + review findings

Filed two new query pages capturing forward-looking and backward-looking
ABF26 PR state:

- `docs/kb/queries/abf26-pr-roadmap.md` — end-goal levels (A/B/C),
  current coverage snapshot (30 present / 11 present-but-different /
  11 present-but-incomplete / 3 deferred), and a phased work plan for
  taking PR #505 to ready-for-review and beyond.
- `docs/kb/queries/abf26-review-2026-05.md` — promoted from the
  scratch review doc at repo root (`ABF26_REVIEW.md`, now removed).
  Contains the 9 H/M, 9 L cleanup, and 5 ArkLib-integration findings,
  each with a per-item resolution log mapping to the
  2026-05-18 fix commits.

Audit doc `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`
refreshed for the same set of fixes (L2.10 / D2.20 / C6.2 / D6.4 /
C6.9 / L6.10 / A.7 rows). Coverage drift check reports 0 missing / 0
drift.

## [2026-05-19] alias sweep | ABF26 §A IOR notions + A.6

Shipped `ArkLib/ProofSystem/ToyProblem/Aliases.lean` with the
following paper-shaped Lean `alias` declarations (definitionally equal
to existing ArkLib / Mathlib notions):

- `ABF26.IOR.completeness` (A.1) ↔ `Reduction.perfectCompleteness`
- `ABF26.IOR.knowledgeSoundness` (A.3) ↔ `Verifier.knowledgeSoundness`
- `ABF26.IOR.rbrKnowledgeSoundness` (A.5) ↔ `Verifier.rbrKnowledgeSoundness`
- `ABF26.formalDerivative` (A.6) ↔ `Polynomial.derivative`

Audit doc rows for A.1 / A.3 / A.5 / A.6 promoted from
`present-but-different` to `present`. Coverage snapshot moves from
30/11/11/3 to **34/7/11/3** (+4 present, −4 present-but-different).

L2.1 (paper-shape polynomial-identity) and T4.8 (AHIV17 ε-wrapping)
intentionally not aliased here; both need real proof work documented
in [`abf26-pr-roadmap.md`](queries/abf26-pr-roadmap.md) Phase 2.

## [2026-05-19] alias sweep | D2.7 IsFAdditive + harness fixes

Two follow-up items on top of the same-day A.1 / A.3 / A.5 / A.6 alias
sweep:

- Shipped `ABF26.IsFAdditive` (paper Def 2.7) in
  `ArkLib/ProofSystem/ToyProblem/Aliases.lean` (renamed from
  `PaperAliases.lean` to avoid the `paper_ctx` regex bug below). The
  predicate is the `Set`-form proposition "this code IS the carrier of
  some F-`Submodule`", complementing the existing `ModuleCode` /
  `LinearCode` types that bake in the F-linear structure. Audit D2.7
  row promoted from `present-but-different` to `present`.
- `scripts/abf26/coverage.py` got two defensive fixes:
  1. Header detection now requires *all* canonical header keys
     (`ABF26 ID`, `Paper item`, `Status`) on the line, not `any` —
     prevents body prose containing the word "Status" from
     corrupting the table parse.
  2. The `paper_ctx` regex that strips "(paper notation …)"
     parentheticals now skips Markdown `.lean` link targets via a
     look-ahead `(?![./\w]*\.lean\))`, so paths containing the word
     "Paper" are not silently dropped.

Coverage snapshot moves from 30/11/11/3 (2026-05-18) to **35/6/11/3**
this session: +5 present, −5 present-but-different, 0 drift, 0 missing.

## [2026-05-19] revert | alias sweep removed (no-duplication rule)

The same-day alias sweep (4 IOR aliases + `ABF26.formalDerivative` +
`ABF26.IsFAdditive` predicate) has been reverted on review. The
durable rule established with the user:

> Re-use existing ArkLib abstractions / definitions / notations /
> conventions directly. If they need to be improved/generalised then
> do that (safely, without breakage) rather than duplicating things.

Paper-shape `alias` wrappers are anti-integration: they rename without
adding semantics, create a maintenance liability (alias drifts on
rename), and game the audit coverage metric without substantive
change. The right "alignment with ArkLib" story is to use the in-tree
name directly; the paper↔Lean name map is recorded in the audit
doc's *Notes* column rather than in a wrapper.

Concrete changes:
- `ArkLib/ProofSystem/ToyProblem/Aliases.lean` deleted; removed from
  `scripts/abf26/owned-files.txt` and `ArkLib.lean`.
- Audit rows A.1 / A.3 / A.5 / A.6 / D2.7 reverted from `present` to
  `present-but-different` with sharpened Notes pointing at the in-tree
  ArkLib / Mathlib names.
- Coverage snapshot back to **30/11/11/3** (the honest pre-sweep
  number).

What stays: the harness fixes (header-key `all` not `any`, paper_ctx
lean-link skip, `alias` recognition, Mathlib-prefix skip) — those are
defensive improvements to the drift checker independent of the alias
policy.

## [2026-05-20] tooling | declaration extractor + dedup report

Added two reusable KB tools for cross-cutting declaration audits:

- `scripts/kb/extract_declarations.py` — parses a list of ArkLib
  directories, tracking `namespace`/`section`/`end` correctly, and
  writes a JSON catalog of every declaration (name, kind, namespace,
  line, signature, docstring head). Currently 4005 declarations across
  206 files when run over `ArkLib/Data + OracleReduction +
  ProofSystem + CommitmentScheme + AGM + ToMathlib`.
- `scripts/kb/find_dedup_candidates.py` — consumes the JSON and
  surfaces (a) same-short-name groups across multiple files (ranked
  by interestingness — files × namespaces), and (b) near-duplicate
  docstrings via Jaccard similarity ≥ 0.7 on 4+-letter words. Output:
  `docs/kb/_generated/dedup-report.md`.

First-pass findings from the report:

- Single concrete rename: `ReedSolomon.minDist` / `minDist'` →
  `minDist_eq` / `minDist_eq'` (theorems stating an equation about
  `Code.minDist`; should follow the `_eq` convention to avoid the
  short-name collision with `Code.minDist : Set _ → ℕ`). 3 call sites,
  all in `ReedSolomon.lean`; renamed in commit alongside this entry.
- All other large groups (`pSpec`, `prover`, `verifier`,
  `oracleReduction`, `inputRelation`, `outputRelation`, …) are the
  intentional one-per-protocol-module pattern, not duplication.
- The 6-flavour family across `{Prover, Verifier, Reduction,
  OracleProver, OracleVerifier, OracleReduction}.{cast_id,
  seqCompose, …}` is intentional pairing across the parallel security
  hierarchy; typeclass-unifying would be invasive and out of scope.
- 4 paper-specific `disagreementSet` variants (DG25 / Binius / Stir /
  Whir) share a concept but have distinct definitions. Potential
  candidate for a common base, deferred.
- `Prover.processRound{,FS,DSFS}` and `Prover.runToRound{,FS,DSFS}`
  have word-for-word identical docstrings (Jaccard 1.00) but live in
  separate Fiat-Shamir variants of the framework. Worth a docstring
  pass at least.

Generated artefacts under `docs/kb/_generated/`:
`declarations.json` (~860 KB) and `dedup-report.md`. Rebuild via the
two scripts above; both are deterministic.

## [2026-05-20] dedup pass | Code.disagreementCols primitive

Following the dedup-candidate scan, lifted the inline
`Finset.filter (fun i => u i ≠ v i) Finset.univ` pattern (used twice
in `ArkLib/Data/CodingTheory/Basic/Distance.lean`) to a named
`Code.disagreementCols : (ι → R) → (ι → R) → Finset ι` primitive,
plus a `mem_disagreementCols` simp lemma and
`hammingDist_eq_disagreementCols_card` connecting it to Mathlib's
`hammingDist`.

The two existing inline uses (`closeToWord_iff_exists_possibleDisagreeCols`
and `closeToWord_iff_exists_agreementCols`) now call the new primitive
directly.

The 4 paper-specific `disagreementSet` declarations
(`DG25.MainResults`, `Binius.BinaryBasefold`, `Quotienting`,
`BlockRelDistance`) are **not** deduplicated — each has additional
structure (interleaved pairs / polynomial-evaluation comparisons /
block-fibers / Set-valued domain) that the primitive doesn't capture.
Their docstrings now cross-reference `Code.disagreementCols` and
explain the relationship (e.g. DG25 = union of two `disagreementCols`
applications; BlockRelDistance = block-wise variant that coincides
with the primitive at `k = 0`).

Naming: chose `disagreementCols` over `disagreementSet` so paper-
specific modules with `open Code` keep their local `disagreementSet`
name without a resolution clash. Discovered the clash via build
failure; the test pass that initially used `disagreementSet`
collided with DG25's local one.

## [2026-05-20] phase 2 | L2.1 polynomial identity (paper shape)

Closed the paper-shape polynomial identity lemma (ABF26 L2.1) via a
safe two-step generalisation in `ArkLib/Data/Probability/Instances.lean`:

1. **Generalised** `prob_schwartz_zippel_mv_polynomial` to take an
   explicit degree bound `d` (was hard-coded to `n` = variable count):
   new `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le` with
   conclusion `Pr ≤ d / |R|` for `totalDegree P ≤ d`. The legacy
   wrapper is preserved as a one-line `d := n` specialisation (zero
   callers were affected — verified via grep before the rename).
2. **Added helper** `MvPolynomial.totalDegree_le_of_degreeOf_lt` —
   a Mathlib-extension-shape lemma converting per-variable
   `degreeOf < d` into `totalDegree ≤ m * (d - 1)`.
3. **Added paper-shape lemma** `prob_polynomial_identity_le` with the
   ABF26 L2.1 statement `Pr ≤ m·(d-1) / |F|`, derived in one line from
   (1) + (2).

Audit row L2.1 promoted from `present-but-different` to `present`.
Coverage snapshot moves from 30/11/11/3 (post-revert) to **31/10/11/3**.
Per the no-duplication rule, the new declarations all chain through
the same Mathlib base (`MvPolynomial.schwartz_zippel_totalDegree`) —
no parallel implementation.

## [2026-05-20] phase 2 | ExtensionFieldPresentation refactor

Refactored `CodingTheory.ExtensionFieldPresentation` (ABF26 D2.19) to wrap
Mathlib's `[Algebra B F]` + `Basis (Fin e) B F` directly, removing the
custom struct that duplicated this machinery. Net change in
`ExtensionCodes.lean`:

- Structure went from 9 fields (`e`, `ψ`, `ψ_injective`, `φ`, `φ_inv`,
  `φ_left_inv`, `φ_right_inv`, `φ_add`, `φ_smul_psi`) to **2** (`e`,
  `basis : Basis (Fin e) B F`), with `[Algebra B F]` as an instance.
- `ψ` is now `algebraMap B F` (derived via `@[reducible]` alias).
- `ψ_injective` is `FaithfulSMul.algebraMap_injective B F` (Mathlib).
- `φ` is `basis.equivFun` (Mathlib's `B`-linear coordinate iso).
- `coord j` is `LinearMap.proj j ∘ₗ φ` — a `LinearMap`, so `coord_add`
  becomes `LinearMap.map_add` and `coord_psi_smul` becomes a one-liner
  via `Algebra.smul_def` + `LinearMap.map_smul`.

The downstream lemmas `extensionCode_add_mem` and
`extensionCode_psi_smul_mem` are unchanged in shape but now proven via
Mathlib's `LinearMap` API rather than the custom field-by-field proof.

`extensionCode_smul_mem` (F-scalar closure) is still a tagged sorry,
**but the obstruction has shifted from structural to mechanical**:
pre-refactor it required "F-algebra structure constants `γ_{l,m,j}`"
not exposed by the custom struct; post-refactor those constants are
`P.coord j (α * P.basis m)`, directly computable from `P.basis`. The
remaining proof is a routine `Finset.sum_induction` chain through
`hadd + hsmul` (with `hsmul 0 (hv m₀)` giving `0 ∈ C_B` for the
empty-sum case when `e ≥ 1`; `e = 0` is vacuous since `∀ j : Fin 0`
is trivially true).

Audit doc D2.19 promoted to clarify the Algebra/Basis underpinning;
D2.20 status note updated to reflect the unblocked path.

Per the no-duplication rule: this is an *improve/generalise safely*
move (zero external consumers of `ExtensionFieldPresentation` —
verified via grep — so the struct-shape change is local), not a
parallel implementation.

## [2026-05-20] phase 2 | extensionCode_smul_mem closed

Closed the F-scalar closure of `extensionCode` (paper D2.20's F-linearity
claim) following the Algebra/Basis refactor of the prior commit. Proof
structure:

1. **Pointwise identity** via `Basis.sum_equivFun (v i)`:
   `P.coord j (α * v i) = ∑ m, P.coord m (v i) * P.coord j (α * P.basis m)`
   (chain: substitute the basis-expansion of `v i`, distribute via
   `Finset.mul_sum`, push `α *` past `•` with `mul_smul_comm`, then apply
   `B`-linearity of `P.coord j` via `map_sum`/`map_smul`).
2. **Function-level identity**:
   `(fun i ↦ P.coord j (α * v i)) =
     ∑ m, (P.coord j (α * P.basis m)) • (fun i ↦ P.coord m (v i))`.
3. **Membership conclusion** via `Finset.sum_induction`:
   each summand is in `C_B` by `hsmul`; finite sum lies in `C_B` by
   iterated `hadd`. Base case `0 ∈ C_B` derived from `hsmul 0 (hv m₀)`
   for `m₀ : Fin P.e` (non-vacuous since `e ≥ 1` in this branch); the
   `e = 0` branch is dispatched via `Fin.elim0 (h_e_zero ▸ j)`.

Net effect: D2.20 promoted from `present-but-incomplete` to `present`.
Coverage **32/10/10/3** (+1 present, −1 present-but-incomplete).

Together with the prior D2.19 refactor, this is the no-duplication rule
fully landed for the extension-code item: ArkLib's
`ExtensionFieldPresentation` is now a thin wrapper over `[Algebra B F]` +
`Basis (Fin e) B F`, all paper D2.20 closure laws follow from Mathlib's
`Algebra` / `Basis` machinery, and the F-scalar closure proof — which
pre-refactor would have required introducing structure-constant fields
— is a 30-line basis-expansion chain.

## [2026-05-20] coding-theory | extensionCodeSubmodule packaging

Added `CodingTheory.extensionCodeSubmodule` mirroring `ReedSolomon.code`'s
`Submodule F (ι → F)` shape: when `C_B : Submodule B (ι → B)`, the
extension code is itself a `Submodule F (ι → F)`. Built directly from
the three closure lemmas (`extensionCode_add_mem`, `Submodule.zero_mem`,
`extensionCode_smul_mem`); no parallel implementation.

`coe_extensionCodeSubmodule` is the `(extensionCodeSubmodule … : Set _) =
extensionCode P (C_B : Set _)` carrier bridge — `rfl`.

Per the no-duplication rule: this is the natural Mathlib-aligned shape
for downstream consumers ("here is a linear code over F") — the Set-form
remains available for callers that want the more general
non-linear-code variant.

Audit D2.20 row's Lean target column now lists both forms.
