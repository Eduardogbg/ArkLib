# ABF26 Integration Plan

Companion to [`ABF26_PLAN.md`](ABF26_PLAN.md) (the original master plan) and
[`ABF26_POLISH_PLAN.md`](ABF26_POLISH_PLAN.md) (the correctness/polish pass).

**Goal.** Take the substantial body of ABF26 formalisation work currently on the
branch and integrate it cleanly into ArkLib — both in *style* (naming, notation,
type choices, namespaces) and in *location* (file structure, ProofSystem
touchpoints, eventual home of each definition). Also identify what's still
missing for full paper coverage, particularly the path to the **grand MCA
challenge** and **grand list-decoding challenge** of §1.

This plan is the synthesis of four parallel surveys (CodingTheory tree,
Polynomial/Matrix tree, ProofSystem consumers, paper bibliography) plus a
direct re-read of ABF26 §§1, 6, 7, A, B.

## 0. Working principles

- **Additive integration.** No structural change rewrites pre-existing
  ArkLib history. New work integrates by moving / renaming files added on
  this branch; existing files outside this branch's diff stay untouched.
- **One concern per commit.** Each integration step is a single named
  refactor (e.g. "move LineDecoding into ProximityGap/", "alias Lambda
  notation", "introduce Λ scoped notation").
- **Validation gate.** `./scripts/validate.sh` must pass after every step.
- **Reversibility.** Prefer additive bridges (e.g. `epsCA_iff_predicate_eq`)
  over deletions; old call sites keep working.

## 1. Inventory and findings

### 1.1 Existing ArkLib infrastructure (sketch)

Surveyed `ArkLib/Data/CodingTheory/`, `ArkLib/Data/Polynomial/`,
`ArkLib/Data/MvPolynomial/`, `ArkLib/Data/Matrix/`, `ArkLib/Data/Probability/`,
and `ArkLib/ProofSystem/`. Key facts:

- **`CodingTheory/Basic/`** is the foundation: `Code.dist`, `Code.minDist`,
  `δᵣ`, `δᵣ'`, `Δ₀`, `‖C‖₀`, `UDR`, `relUDR`. Notation declared globally
  inside `namespace Code`. Type conventions: `ℕ∞` for absolute distance,
  `ℚ≥0` / `ℝ≥0` / `ENNReal` for relative.
- **`LinearCode`** = `Submodule F (ι → F)`. **`ModuleCode ι F A`** =
  `Submodule F (ι → A)`. Notation `ρ` for rate is scoped, non-reserved.
- **`InterleavedCode`** provides `interleavedCodeSet` plus a
  `CodeInterleavable` typeclass and `^⋈` notation that works for both
  `Set`-based and `Submodule`-based codes.
- **`ProximityGap/Basic`** defines predicate-style CA: `proximityMeasure`,
  `δ_ε_correlatedAgreementAffineLines/Curves/AffineSpaces`.
- **`ProximityGap/BCIKS20`**, **`AHIV22`**, **`DG25/`** contain specific
  proven proximity-gap theorems with their own conventions and a few
  pre-existing sorries.
- **`ReedSolomon.lean`** defines `code domain deg :=
  (Polynomial.degreeLT F deg).map (evalOnPoints domain)` — the pattern that
  `frsCode` should mirror (and does, after refactor).
- **`ListDecodability`** provides `Lambda_at`, `Lambda`, plus `Λ(C, δ, f)`
  and `Λ(C, δ)` global notation. Added on this branch in commit `7c913b3b`.
- **`JohnsonBound/Basic`** defines `J q δ` (paper's `J_q`), `JohnsonDenominator`,
  the strong/weak Johnson conditions.
- **`Polynomial/`** has `Indicator`, `SplitFold`, `FoldingPolynomial`,
  `Bivariate`, `Trivariate`, `RationalFunctions`, `Interface`. Most are
  STIR/FRI-shaped and don't directly overlap with ABF26 work.
- **`Probability/Notation.lean`** defines the `Pr_{...}[...]` and `$ᵖ`
  notation already used throughout my new files.

### 1.2 Branch additions

11 new files (9 Lean + 2 plan docs):

| New file | Paper items | Where it sits today |
|---|---|---|
| `ABF26Prelims.lean` | D2.2, D2.3, D2.4 | `CodingTheory/` top |
| `ABF26CodeFamilies.lean` | D2.13, D2.14, D2.15, D2.16, L2.17, T2.18 | `CodingTheory/` top |
| `ExtensionCodes.lean` | D2.19, D2.20, L2.21 | `CodingTheory/` top |
| `JohnsonBound/ABF26.lean` | D3.1 (`Jqℓ`, `Jcap`), T3.2, C3.3, `IsMDS` | `CodingTheory/JohnsonBound/` |
| `ListDecodingBounds.lean` | L3.7, C3.8, T3.9–T3.14, T3.4, C3.5 | `CodingTheory/` top |
| `LineDecoding.lean` | D4.20, T4.21 | `CodingTheory/` top |
| `Connections.lean` | T5.1–T5.4 | `CodingTheory/` top |
| `ProximityGap/EpsilonErrors.lean` | D4.1, R4.2, D4.3, R4.4, F4.5, L4.6, L4.7 | `CodingTheory/ProximityGap/` |
| `ProximityGap/CapacityBounds.lean` | T4.9.2, R4.10, T4.11–T4.18, L4.19 | `CodingTheory/ProximityGap/` |
| `ProximityGap/GrandChallenges.lean` | §1 grand challenges | `CodingTheory/ProximityGap/` |
| `ABF26_PLAN.md`, `ABF26_POLISH_PLAN.md` | tracking docs | repo root |

Plus modifications:
- `ListDecodability.lean` (+`Lambda_at`, `Lambda`)
- `ProximityGap/Basic.lean` (minor)
- `ArkLib.lean` (umbrella +10 imports)

### 1.3 Paper coverage assessment

Cross-checked against the §§1–7 + A + B structure. **Covered (statement
layer):**

- §1 grand challenges — Prop predicates in `GrandChallenges.lean`.
- §2 all preliminaries — D2.2–D2.20, L2.17, T2.18 (with B-linearity
  caveat for D2.20; multiplicity-codes half of T2.18 deferred).
- §3 list decoding — all positive (T3.2, C3.3) and limitations (T3.9–T3.14)
  results stated. T3.4 / C3.5 stated. T3.15 (algorithmic hardness) out of
  scope.
- §4 correlated agreement — D4.1, R4.2, D4.3, R4.4 present; F4.5 proved;
  L4.6 admitted; L4.7 proved; T4.8 admitted; T4.9.1 admitted; T4.9.2 stated;
  R4.10 stated; T4.11–T4.18 stated; L4.19 stated; D4.20, T4.21 stated.
- §5 connections — T5.1–T5.4 stated.

**Not yet covered:**

- **§6 toy problem.** Deferred per plan Phase 8 but actually central — this
  is the protocol whose soundness proof motivates MCA. Specifically:
  - D6.1 toy problem relation `R_C^ℓ`
  - C6.2 protocol `T[C, t] = (P, V)` (an IOR)
  - D6.3 relaxed relation `R̃_C,δ^ℓ`
  - D6.4 erasure correction predicate `ecor_C`
  - L6.5 [GRS12] every additive code supports erasure correction
  - L6.6 knowledge soundness of C6.2 (uses MCA)
  - R6.7 remark on why MCA (not CA) is needed
  - L6.8 round-by-round knowledge soundness
  - §6.3.1 IRS instantiation, §6.3.2 FRS instantiation, §6.4 attacks
- **§7 related problems and promising directions.** Six open directions
  (MCA for non-poly codes, characterization of degenerate codes, tightness
  of interleaving, subspace-design parameter improvements, curve MCA,
  derandomizing RS). Not statable as theorems; these are research
  directions to track but not formalise.
- **§A.1 IORs.** Definitions A.3 / A.4 / A.5 (IOR knowledge soundness,
  knowledge state function, round-by-round knowledge soundness). ArkLib
  has its own `OracleReduction/` infrastructure — these should *map onto*
  existing definitions there, not be re-introduced.
- **§A.2 univariate multiplicity codes.** D.A.6 (formal derivative) and
  D.A.7 (`UM[F, L, k, s]`). These gate the multiplicity half of T2.18.
- **§B claim B.1.** Coloring lemma for L6.12 — small but standalone.

### 1.4 What's missing for the grand challenge path?

The paper's "grand MCA challenge" is concretely:

> Given `RS[F, L, k]` with smooth `L`, `ρ ∈ {1/2, 1/4, 1/8, 1/16}`,
> `ε* = 2^{-128}`: find the largest `δ*_C ∈ [0, 1]` such that
> `ε_mca(C, δ*_C) ≤ ε*`.

For this we have:

- ✅ The challenge predicate (`grandMCAChallenge` in `GrandChallenges.lean`).
- ✅ `ε_mca` definition (D4.3).
- ✅ The upper-bound theorems that produce candidate witnesses
  (T4.8, T4.9.1, T4.9.2, T4.11.1/2, T4.12, T4.13, T4.14, T4.15 — all
  stated, mostly admitted).
- ✅ The lower-bound theorems that rule out witnesses (T4.16–T4.18).
- ⚠ The Reed-Solomon-with-smooth-domain specialisation is *not* spelled
  out as a separate type or predicate. `ReedSolomon.code domain k` allows
  arbitrary domain; `Smooth` is in `ReedSolomon.lean` (line 571) as a
  predicate.
- ⚠ The rate constraints `ρ ∈ {1/2, 1/4, 1/8, 1/16}` and the threshold
  `ε* = 2^{-128}` are paper-level parameter choices; my predicate leaves
  them generic. Probably fine — at the call site, the user instantiates.

For the **grand list-decoding challenge** (`|Λ(C^≡m, δ*_C)| ≤ ε* · |F|`):

- ✅ `Lambda` is defined on `C^≡m` via the `^⋈` operator.
- ✅ The predicate is stated.
- ✅ The relevant upper bounds (T3.2, C3.3 via Johnson; T3.4 via
  subspace-design; T3.6 via random RS) and lower bounds (T3.10, T3.11,
  T3.12–T3.14) are all stated.

So **the statement layer for both grand challenges is complete.** What
remains is *proving* the admitted theorems — each is paper-cited
external content.

## 2. Style integration plan

### 2.1 Naming conventions

| Concern | Current state | Recommendation |
|---|---|---|
| Theorem naming | Mostly `<code>_<epsType>_<regime>_<authors><year>` (e.g. `rs_epsMCA_johnson_range_bchks25`) | Keep — informative and de-duplicating. Document the pattern in `CONTRIBUTING.md` or a CodingTheory README. |
| Definition naming | Mix: paper-letter (`epsCA`, `epsMCA`, `Lambda`), paper-named (`qEntropy`, `Jqℓ`), descriptive (`restrictedRelHammingDist`, `hammingBallVolume`, `LineDecodable`) | Acceptable mix. Promote `IsX` predicate names where applicable (`IsMDS`, `IsSubspaceDesign`, `IsFAdditive`). |
| File naming | `ABF26Prelims`, `ABF26CodeFamilies`, `ListDecodingBounds`, `Connections` | "ABF26" prefix mirrors plan-ledger names but is paper-specific. **Recommend renames** (see §3.1). |
| Submodule field names | `frsEvalOnPoints`, `IsMDS`, `coord_add`, `coord_psi_smul` | Consistent. Keep. |

### 2.2 Notation alignment

| Notation | Existing | New work | Recommendation |
|---|---|---|---|
| `Δ₀(u, v)`, `Δ₀(u, C)` | Hamming distance (global, `Code` namespace) | Used unchanged | ✅ no action |
| `‖C‖₀` | absolute min distance | Not used in new work | ✅ no action |
| `δᵣ(u, v)`, `δᵣ(u, C)` | relative distance (global) | Used unchanged | ✅ no action |
| `Λ(C, δ, f)`, `Λ(C, δ)` | list sizes (added in commit `7c913b3b`) | Used unchanged | ✅ no action |
| `^⋈` | interleave (`Set` + `ModuleCode` instances) | Used in `irsCode` (after refactor) | ✅ no action |
| `ρ C` | rate (scoped, non-reserved) | Not used in new statements | Consider using in statements where rate appears (T4.12, T4.16, etc.) |
| `Pr_{let γ ← $ᵖ F}[…]` | probability (existing) | Used unchanged | ✅ no action |
| `Δ_T(f, g)` | restricted Hamming distance | Defined as `restrictedRelHammingDist` without notation | **Add scoped notation** `notation "Δ[" T "]" "(" f ", " g ")" => restrictedRelHammingDist T f g` (in `ABF26Prelims.lean`). |
| `δ_min(C)` | relative minimum distance | Not declared; raw `Code.minDist C / Fintype.card ι` | **Decision: keep raw form.** Adding a `δ_min` scoped notation collides with `δᵣ C` (which is the same thing) and confuses readers. Document the equivalence in `Basic/RelativeDistance.lean`. |
| `RS[F, L, k]`, `IRS[F, L, k, s]`, `FRS[F, L, k, s, ω]`, `UM[F, L, k, s]` | none | Used in docstrings, not as Lean notation | **Decision: keep names (`ReedSolomon.code`, `Interleaved.irsCode`, `Folded.frsCode`).** Per polish-plan D2 (descriptive names preferred). Revisit when a downstream proof needs the paper notation for cognitive ergonomics. |
| `H_q(x)` | none | Defined as `qEntropy q x` | Keep. Mathlib has `Real.binEntropy` but no q-ary analog. |

### 2.3 Type conventions

| Quantity | Existing convention | New-work convention | Recommendation |
|---|---|---|---|
| Codes | `Submodule F (ι → A)` (linear), `Set (ι → A)` (general) | Same — refactored to align (irsCode, frsCode are Submodule) | ✅ done |
| Absolute distance | `ℕ` (`Code.minDist`), `ℕ∞` (`distFromCode`) | Same | ✅ no action |
| Relative distance | `ℚ≥0` (`relHammingDist`), `ENNReal` (`relDistFromCode`), `ℝ` (paper bounds) | `ℝ≥0` for `restrictedRelHammingDist`, `ℝ` for thresholds | **Document the spread** in `Basic/Distance.lean` and `Basic/RelativeDistance.lean` docstrings: "we use ℚ≥0 for the computable form and ℝ for paper-style bounds; bridges via `*_toReal` / `*_toNNReal`." |
| Probabilities / ε-errors | `ENNReal` (existing in BCIKS20, AHIV22) | `ENNReal` (`epsCA`, `epsMCA`, etc.) | ✅ aligned |
| Bound expressions | `ℝ`-valued real expressions wrapped in `ENNReal.ofReal` | Same | ✅ aligned (documented in `CapacityBounds.lean` header) |
| Cardinalities of codes | `ℕ∞` (`Lambda`) | Same | ✅ aligned |
| Rate | `ℚ≥0` (`LinearCode.rate`) | `ℝ` in statements | Bridge via `(rate C : ℝ)`. Acceptable. |
| Polynomial degree-bound | `Polynomial.degreeLT F k` (`Submodule F F[X]`) | Same (after A7 refactor) | ✅ aligned |

### 2.4 Namespace organization

Current scattered state:

- `CodingTheory.qEntropy`, `CodingTheory.hammingBallVolume` — top-level `CodingTheory`.
- `CodingTheory.restrictedRelHammingDist` — top-level `CodingTheory`.
- `ReedSolomon.Interleaved.irsCode` — under existing `ReedSolomon`.
- `ReedSolomon.Folded.frsCode`, `Admissible` — under existing `ReedSolomon`.
- `CodingTheory.IsSubspaceDesign` — top-level `CodingTheory`.
- `CodingTheory.ExtensionFieldPresentation`, `extensionCode` — top-level.
- `CodingTheory.LineDecodable` — top-level.
- `CodingTheory.IsMDS` — `JohnsonBound`.
- `JohnsonBound.Jqℓ`, `Jcap` — `JohnsonBound`.
- `ProximityGap.epsCA`, `epsMCA`, `epsPG` — `ProximityGap`.
- `ProximityGap.grandMCAChallenge`, `grandListDecodingChallenge` — `ProximityGap`.

**Recommendation: collapse to three namespaces:**

- `CodingTheory.*` for non-RS-specific defs (`qEntropy`, `hammingBallVolume`,
  `restrictedRelHammingDist`, `IsSubspaceDesign`, `IsMDS`, `LineDecodable`,
  `ExtensionFieldPresentation`, `extensionCode`).
- `ReedSolomon.*` for RS variants and sub-namespaces
  (`ReedSolomon.Interleaved.irsCode`, `ReedSolomon.Folded.frsCode`,
  `ReedSolomon.Folded.Admissible`, `ReedSolomon.Multiplicity.umCode` when added).
- `ProximityGap.*` for ε-errors, grand challenges, and any predicate-style
  proximity material.

Theorems (admitted external results) stay in `CodingTheory.*` where they
operate on general codes, `ReedSolomon.*` where RS-specific, or
`ProximityGap.*` where they bound an `ε`-error.

## 3. Location integration plan (per file)

### 3.1 Files that should move/rename

| Current path | Recommended path | Rationale |
|---|---|---|
| `CodingTheory/ABF26Prelims.lean` | `CodingTheory/Basic/Entropy.lean` (for `qEntropy`) + extend `Basic/RelativeDistance.lean` (for `restrictedRelHammingDist`) + new `CodingTheory/HammingBallVolume.lean` (for `hammingBallVolume`) | "ABF26" prefix is paper-ledger; topical names are more discoverable. Each def is general (not paper-specific) and belongs near its peer concept. |
| `CodingTheory/ABF26CodeFamilies.lean` | split into `CodingTheory/ReedSolomon/Interleaved.lean`, `CodingTheory/ReedSolomon/Folded.lean`, `CodingTheory/SubspaceDesign.lean` | Three topically distinct families currently bundled. Each has natural neighbours: IRS and FRS belong with RS; subspace-design is its own concept. |
| `CodingTheory/ExtensionCodes.lean` | `CodingTheory/ExtensionCodes.lean` (rename to `Extensions/Basic.lean` if more extension content is added later) | Self-contained; current path is OK. |
| `CodingTheory/LineDecoding.lean` | `CodingTheory/ProximityGap/LineDecoding.lean` | §4 content; belongs alongside other §4 material in `ProximityGap/`. |
| `CodingTheory/ListDecodingBounds.lean` | `CodingTheory/ListDecoding/Bounds.lean` (or split: per-paper subdirs) | Distinguishes from `ListDecodability.lean` (definitions). Optionally split T3.4/C3.5 into `ListDecoding/SubspaceDesign.lean`, T3.12-T3.14 into `ListDecoding/ReedSolomon.lean`. |
| `CodingTheory/Connections.lean` | `CodingTheory/Connections/ListDecodingAndCA.lean` (under a new `Connections/` subdir if more cross-cutting material lands) | Acceptable to keep where it is for now; consider subdir if §5-like content grows. |
| `CodingTheory/JohnsonBound/ABF26.lean` | `CodingTheory/JohnsonBound/Family.lean` (for `Jqℓ`, `Jcap`) + theorems folded into adjacent files | "ABF26" prefix in a subdirectory is awkward. Renaming to `Family.lean` keeps the topic anchor without paper branding. |
| `CodingTheory/ProximityGap/EpsilonErrors.lean` | `CodingTheory/ProximityGap/Errors.lean` (shorten) | "EpsilonErrors" is a bit verbose; `Errors.lean` reads more naturally. |
| `CodingTheory/ProximityGap/CapacityBounds.lean` | (consider splitting: `CapacityBounds/Upper.lean` for §4.2, `CapacityBounds/Lower.lean` for §4.3) | Only if file exceeds ~500 lines. Currently ~400; can wait. |
| `CodingTheory/ProximityGap/GrandChallenges.lean` | `CodingTheory/ProximityGap/GrandChallenges.lean` | Stays; clean topical anchor. |

### 3.2 Files that should merge into existing files

- `qEntropy` → consider folding into `ArkLib/Data/Misc/` or a new
  `ArkLib/Data/Entropy.lean` if Mathlib's `Real.binEntropy` is its peer.
- `IsMDS` → `Basic/LinearCode.lean` (it's a property of any linear code,
  not specifically Johnson-related). Currently in `JohnsonBound/ABF26.lean`.
- `restrictedRelHammingDist` → `Basic/RelativeDistance.lean` (peer of
  `relHammingDist` and `δᵣ`).

### 3.3 Files that stay where they are

- `ProximityGap/Basic.lean`, `BCIKS20/*`, `AHIV22.lean`, `DG25/*` — untouched.
- `Basic/Distance.lean`, `RelativeDistance.lean`, `LinearCode.lean`,
  `DecodingRadius.lean` — touched only by additive bridges.
- `ReedSolomon.lean` — touched only by adding `Smooth`-domain-specialised
  forms if needed for grand-challenge instantiation.
- `JohnsonBound/Basic.lean`, `Lemmas.lean` — untouched.

### 3.4 Proposed final tree (CodingTheory subset)

```
CodingTheory/
├── Basic/
│   ├── Distance.lean
│   ├── RelativeDistance.lean       (+ restrictedRelHammingDist)
│   ├── DecodingRadius.lean
│   ├── LinearCode.lean             (+ IsMDS)
│   └── Entropy.lean                (new — qEntropy)
├── HammingBallVolume.lean          (new — hammingBallVolume)
├── ListDecodability.lean           (Lambda_at, Lambda)
├── ListDecoding/
│   └── Bounds.lean                 (L3.7, C3.8, T3.9-T3.14, T3.4, C3.5)
├── JohnsonBound/
│   ├── Basic.lean
│   ├── Lemmas.lean
│   └── Family.lean                 (new — Jqℓ, Jcap, T3.2, C3.3)
├── InterleavedCode.lean
├── ReedSolomon.lean
├── ReedSolomon/
│   ├── Interleaved.lean            (new — irsCode)
│   ├── Folded.lean                 (new — Admissible, frsCode, frsEvalOnPoints)
│   ├── Multiplicity.lean           (new — A.2 univariate multiplicity codes)
│   └── (existing files)
├── SubspaceDesign.lean              (new — IsSubspaceDesign, L2.17, T2.18)
├── ExtensionCodes.lean              (D2.19, D2.20, L2.21)
├── ProximityGap/
│   ├── Basic.lean
│   ├── Errors.lean                  (renamed from EpsilonErrors — D4.1, D4.3, F4.5, L4.6, L4.7)
│   ├── CapacityBounds.lean          (T4.x, L4.19, R4.10)
│   ├── LineDecoding.lean            (moved from top — D4.20, T4.21)
│   ├── GrandChallenges.lean
│   ├── BCIKS20/
│   ├── AHIV22.lean
│   └── DG25/
└── Connections/
    └── ListDecodingAndCA.lean       (renamed/moved from Connections.lean — T5.1-T5.4)
```

## 4. New content needed for full coverage

### 4.1 §6 toy problem (high priority — central to MCA motivation)

Even though deferred per plan Phase 8, §6 is *the example that motivates
MCA in the first place*. The protocol soundness proof (L6.6) is the
canonical reason to care about MCA over CA (R6.7 spells this out).
Recommended new file layout:

```
CodingTheory/ToyProblem/
├── Definitions.lean        — D6.1 R_C^ℓ, D6.3 R̃_C,δ^ℓ, D6.4 ecor
├── Protocol.lean           — C6.2 protocol as IOR
├── Soundness.lean          — L6.5 [GRS12], L6.6, R6.7, L6.8
└── Parametrizations.lean   — §6.3.1 IRS, §6.3.2 FRS, §6.4 attacks
```

These would live under `CodingTheory/` since the protocol is purely a
code-theoretic construction; or alternatively under
`ProofSystem/ToyProblem/` since it's a proof system. Recommend the
latter — it's an IOR, so `ProofSystem/` is its natural home, and
`ProofSystem/` is where ArkLib's `OracleReduction/` infrastructure lives.

**Blockers:** §6 requires IOR machinery from `ArkLib/OracleReduction/`.
Check whether ArkLib's existing OracleReduction infrastructure supports
the round-by-round knowledge soundness `Definition A.5` shape. If not,
that's a prerequisite refactor.

### 4.2 §7 related problems (no formalization; tracking only)

Six open research directions. Track in `ABF26_PLAN.md` §7 as known
follow-ups but do not formalise — they're not theorems.

### 4.3 §A.2 univariate multiplicity codes

Two definitions:

- D.A.6 formal derivative polynomial `f̂'`.
- D.A.7 `UM[F, L, k, s] := {f : L → F^s | ∃ f̂ ∈ F^{<k}[X], f(x) = (f̂(x), f̂'(x), …, f̂^{(s-1)}(x))}`.

Required for the multiplicity half of T2.18 (FRS + UM are both
subspace-design). Recommended location:
`CodingTheory/ReedSolomon/Multiplicity.lean`.

**Mathlib note:** formal derivative of polynomials is
`Polynomial.derivative`. The iterated version `Polynomial.derivative^[k]`
or `Polynomial.iteratedDeriv` should suffice.

### 4.4 §B claim B.1

Coloring lemma. Small, self-contained. Recommended location: inline
inside §6 soundness proofs, or a one-off lemma in
`Data/Combinatorics/` if it has independent uses.

### 4.5 Bridge lemmas to existing ProofSystem (high-leverage)

From the ProofSystem survey, the highest-leverage integration targets are:

#### Whir/MutualCorrAgreement.lean

- Add `hasMutualCorrAgreement_iff_epsMCA_le`: bridges WHIR's
  predicate-style API to ABF26's numeric `epsMCA`.
- Note: this is **one-way only** (`epsMCA ≤ err → hasMutualCorrAgreement`),
  per the recorded WHIR-MCA / ABF26-MCA predicate-mismatch
  (commit `d01117c8`).
- Open sorries at lines 83, 108, 195 of `MutualCorrAgreement.lean` may
  benefit from the numeric API (clarifying the ε-target rather than
  proving the bound).

#### Stir/ProximityGap.lean

- Add `proximity_gap_iff_epsPG_le`: predicate ↔ numeric for the
  proximity-gap claim. Line 47 sorry may collapse to one direction of
  this iff plus the existing BCIKS20 bound.

#### Whir/Folding.lean, RBRSoundness.lean

- Lemmas 4.21–4.23 (folding-preserves-list-decodability) are sorry'd.
  Don't *prove* these in this PR; instead, add comments documenting
  which ABF26-stated theorem each currently-deferred lemma corresponds
  to (e.g., "Whir/Folding L4.22 ≡ ABF26-T4.13 specialized to FRS").

## 5. Sequencing

Recommend four phases. Each phase is a self-contained set of commits and
should leave validation green at every step.

### Execution status (as of 2026-05-15)

- **Phase 1 — ✅ DONE.** Style & convention alignment (commits `b7dc0e08`,
  `5a19b29a`).
- **Phase 2 — ✅ DONE.** File moves split into 2a/2b/2c (commits `b66d50c6`,
  `bc57d712`, `8579e3d1`, `56a7a94a`, `0eb52857`).
- **Phase 3 — ✅ DONE** (bridges) **+ proof discharges.** Both bridges added
  (commit `bf18164b`); the Set/Finset card sub-sorry in
  `hammingBallVolume_eq_ncard_hammingBall` discharged (`13f02444`);
  `IsMDS_iff_singleton_bound_tight` fully proven;
  `minDist_div_card_eq_minRelHammingDistCode` fully proven via a
  `Set.Finite.toFinset` refactor of `minRelHammingDistCode` (commit
  `3f344a00`), which dodges the previous `Fintype.ofFinite` instance
  diamond.
- **Phase 4 — ✅ DONE.** All three touchpoints (MutualCorrAgreement,
  Stir/ProximityGap, Folding/RBRSoundness) addressed; predicate-level and
  probability-level WHIR↔ABF26 MCA bridges added and proved (`32d12508`,
  `aaf85825`).
- **Bonus: `dim_irsCode` proof discharge** (`3b0cfc99`) — closed one of the
  in-tree sorries previously tracked under Pass E1 of the polish plan.
- **Phase 5 — deferred.** §6 toy problem; multi-session effort.
- **Phase 6 — ✅ in-tree sorries closed.** All previously-pending in-tree sorries
  in the ABF26 files are now discharged: `card_filter_hammingDist_eq`
  (`c01232f3`, combinatorial fiberwise count) and
  `minDist_div_card_eq_minRelHammingDistCode` (`3f344a00`, via the
  `Set.Finite.toFinset` refactor of `minRelHammingDistCode`). The 30 external
  admits (T3.2, C3.3, L2.17, T2.18, T3.4-T3.14, T4.11-T4.18, T5.1-T5.4, etc.)
  remain by design — these are paper-cited results, not in scope to reprove.

### Phase 1 — Style & convention alignment (low risk)

1. Document the theorem-naming pattern in a new
   `docs/wiki/coding-theory-conventions.md` and link from
   `docs/wiki/README.md`.
2. Add the `Δ_T(f, g)` scoped notation in `Basic/RelativeDistance.lean`
   (or `ABF26Prelims.lean` if it stays there).
3. Add a "type conventions" docstring to
   `Basic/Distance.lean` and `Basic/RelativeDistance.lean`.
4. Move `IsMDS` from `JohnsonBound/ABF26.lean` to `Basic/LinearCode.lean`.

**Risk:** none — purely additive.

### Phase 2 — File moves (medium risk)

For each rename/move:

1. Create the new file with the old content.
2. Update imports across the tree (`ArkLib.lean` umbrella, any direct
   importers).
3. Delete the old file.
4. `./scripts/validate.sh` after each rename.

Order:

1. `ABF26Prelims.lean` → split into `Basic/Entropy.lean`, extend
   `Basic/RelativeDistance.lean`, new `HammingBallVolume.lean`.
2. `LineDecoding.lean` → `ProximityGap/LineDecoding.lean`.
3. `ABF26CodeFamilies.lean` → split into
   `ReedSolomon/Interleaved.lean`, `ReedSolomon/Folded.lean`,
   `SubspaceDesign.lean`.
4. `JohnsonBound/ABF26.lean` → `JohnsonBound/Family.lean`.
5. `ListDecodingBounds.lean` → `ListDecoding/Bounds.lean`.
6. `Connections.lean` → `Connections/ListDecodingAndCA.lean`.
7. `ProximityGap/EpsilonErrors.lean` → `ProximityGap/Errors.lean`.

**Risk:** import-graph breakage. Mitigation: validate after each rename;
keep umbrella `ArkLib.lean` in sync via `./scripts/update-lib.sh`.

### Phase 3 — Bridge lemmas to existing ArkLib

1. Add `restrictedRelHammingDist_univ` (already added in B1 commit) — keep.
2. Add `hammingBallVolume_eq_ncard_hammingBall` (already added; sub-sorry
   to discharge — see polish plan E1).
3. Add `mem_frsCode_iff`, `mem_frsCode_iff_flipped`,
   `mem_frsCode_one_iff_mem_rsCode`, `frsCode_one_map_eq_rsCode` (already added).
4. Add new bridge lemmas:
   - `Code.minDist_div_eq_minRelHammingDistCode` (links the raw
     `Code.minDist C / n` form used in T3.2/C3.3/etc. to `δᵣ C`).
   - `IsMDS_iff_singleton_bound_tight` (links `IsMDS` to
     `LinearCode.singleton_bound_linear`).

**Risk:** low. Bridges are additive; old call sites stay.

### Phase 4 — ProofSystem integration (high leverage, may surface real friction)

For each touchpoint identified in §4.5:

1. Add the iff bridge as a new lemma in the appropriate file.
2. Optionally: replace one call site with the new bridge as a
   demonstration. Don't try to convert all call sites in one PR.

**Risk:** may surface latent inconsistencies between WHIR's MCA notion
and ABF26's (already documented in commit `d01117c8` — one-way bridge
only). Mitigation: keep bridges *direction-explicit* and document any
asymmetry clearly.

### Phase 5 — §6 toy problem (separate session, large)

This is its own multi-session effort. Sketched in §4.1 above. Not part
of the initial integration PR.

### Phase 6 — Proof discharge follow-ups (open-ended)

Out of scope for this integration plan. Tracked in `ABF26_POLISH_PLAN.md`
and `ABF26_PLAN.md` per item.

## 6. What to do for the PR

The current branch has 78+ commits (61 statement-layer + Phase 1–4 integration +
proof discharges), all clean and validating. Three realistic shapes for the PR:

### Option A — push as-is, draft PR

- Single very large PR.
- Reviewer cost: high.
- Use case: project lead wants to see the whole arc.

### Option B — push as-is, then immediately stack Phase 1+2 cleanup commits

- Same single PR, but capped by an "integration polish" commit cluster.
- Reviewer reviews the final shape rather than the journey.
- Use case: prefer a single mergeable artifact.

### Option C — split into stacked PRs along phase boundaries

- PR 1: §1 grand challenge + §2 prelims + §3-§5 statement layer + polish (the bulk).
- PR 2: Phase 1+2 style and location refactor.
- PR 3: Phase 3 bridges.
- PR 4 (and beyond): ProofSystem integration, §6 toy problem.
- Reviewer cost: moderate per PR.
- Use case: incremental review, lower merge risk.

**Recommendation:** Option **B**. The current branch is the natural
unit; pushing it now and following up with style/location commits
keeps the narrative intact while improving the final shape before
review.

## 7. What this plan does *not* commit to

- Specific proof discharges for tagged sorries (`dim_irsCode`,
  `card_filter_hammingDist_eq`, the external admits, etc.). Those are
  tracked in `ABF26_POLISH_PLAN.md` Pass E and remain open follow-ups.
- B5 (the Mathlib refactor of `ExtensionFieldPresentation`). Same — open
  follow-up; would unlock `extensionCode_smul_mem`.
- §7 paper-section formalisation. Six research directions; not theorems.
- Any change to existing ArkLib code outside the new files (modulo the
  small `Basic/LinearCode.lean` extension for `IsMDS`).

## 8. Out-of-scope but worth tracking

- The `Polynomial/` and `MvPolynomial/` infrastructure noted by Survey 2
  has several pieces we could leverage but currently don't (e.g.
  `MvPolynomial.LinearMvExtension` for higher-dim folded codes). Not
  blocking ABF26; keep on radar for §6 / future paper extensions.
- WHIR-MCA vs ABF26-MCA asymmetry (one-way bridge) — recorded in commit
  `d01117c8`. Resolution path documented but not implemented.

### 8.1 Post-merge state (PR #430 + #504 landed, merge commit `37c5a6d8`)

1. **`LinearCode.IsMDS` collision** ✅ **resolved.** Adopted Katy's def
   (additive Nat form, no `ρ` parameter) as canonical:
   ```lean
   def IsMDS (LC : LinearCode ι F) : Prop :=
     Code.dist LC.carrier = length LC - dim LC + 1
   ```
   Our previous `IsMDS C ρ` removed; the `IsMDS_iff_singleton_bound_tight`
   bridge was rewritten as `IsMDS_iff_rate_distance` converting Katy's
   additive form to the rate-distance form `(δ_min : ℝ) / n = 1 - dim/n +
   1/n` (the form ABF26 §2-§3 uses). `mds_johnson_lambda_le` was the only
   consumer of our old `IsMDS C ρ`; it now takes `LinearCode.IsMDS C` and
   binds `ρ` inline as `dim C / n` via a `let`.

2. **Two cosmetic renames from #430 review** (still pending — Katy noted
   but didn't apply before merging, we offered to handle here):
   - `Basic/MDSCode.lean` L22: rename `namespace CoreResults`.
   - `Basic/MDSCode.lean` L167: rename `colRank_genMatrix_eq_dim_of_MDS` →
     `colRank_genMatrix_iff_dim_of_MDS`.
   Low priority — cosmetic only, can land in a future polish commit.

3. **`ProximityGap/ProximityGenerators.lean` API polish** (#430 review,
   still pending):
   - Connect `IsPolynomialGenerator` ↔ `IsPolynomialGeneratorOf` via
     reorder + recursive def OR a `Iff.rfl` bridge lemma.
   - Add docstring to `IsPolynomialGeneratorOf`.
   - Comment the `noncomputable example` at L77-78.
   Low priority — API polish, not blocking.

4. **PR #504 `mem_code_*` lemmas** now available for consumption. Some of
   our existing `simp [code, Submodule.mem_map]` unfolds in ABF26 files
   could become cleaner one-liners; worth a future polish pass.

## 9. Local bibliography map (from Survey 4)

Each PDF in the repo root mapped to its ABF26 role and ArkLib coverage:

### Papers already substantially present in ArkLib

| Local PDF | Citation in ABF26 | ABF26 items underwritten | ArkLib status |
|---|---|---|---|
| `ABF26.pdf` | — | (master paper) | branch in flight |
| `paper.pdf` | — | duplicate of `ABF26.pdf` | ignore |
| `ahiv22.pdf` | [AHIV17] | T4.8 | sorry-free in `AHIV22.lean` (PR #385); paper-shaped restatement still missing on this branch |
| `bciks20.pdf` | [BCIKS20] | T4.9.1, T4.11 form, parts of §4 hierarchy | extensive subtree under `ProximityGap/BCIKS20/`; several Phase 2 sorries open |
| `bgks19.pdf` | [BGKS20] | T4.11 Item 2, T5.4 | T4.11.2 stated; T5.4 stated; both as external admits |
| `bbhr18.pdf` | [BBHR18] | foundational FRI (used by §6 toy) | `ProofSystem/Fri/` formalised, some sorries open |
| `bcs16.pdf` | [BCS16] | foundational for §A.1 IORs | `OracleReduction/` framework present |
| `ACFY24a.pdf` | [ACFY25] STIR | toy-problem motivation, MCA-for-folded RS (T4.14) | `ProofSystem/Stir/` present; MCA pieces partially admitted |
| `ACFY24b.pdf` | [ACFY25] WHIR | MCA definitions (D4.3 family), T4.14 | `ProofSystem/Whir/` present; several pieces admitted |
| `gmw26.pdf` | (FRI RBR) | not in §3–§5 directly; supports §6 toy soundness | `Fri/RoundConsistency.lean` companion |

### Papers cited but not yet in ArkLib

| Local PDF | Citation | ABF26 items | Status |
|---|---|---|---|
| `bcgm26.pdf` | [BCGM25] | footnote 2 of intro; relates to T4.13, T4.14 (polynomial generators preserve MCA) | **Gap on branch.** Should be tracked in `ABF26_PLAN.md` external-admit ledger; the BCGM25 result extends T4.13/T4.14 to polynomial generators beyond affine lines. |
| `bcfw25.pdf` | (WARP) | not in §3–§5; framework for MCA-for-proximity-generators | tangential; mostly relevant to `OracleReduction/` accumulation theory |

### Papers tangential or out of scope

| Local PDF | Reason |
|---|---|
| `DP23.pdf`, `DP24.pdf` | Binius / binary-tower SNARKs; tangential to ABF26 open problems. `DP24.pdf` is actually the DP25 reference cited by ABF26's L2.21 distance equality remark — worth flagging in `ExtensionCodes.lean`'s docstring. |
| `kp22.pdf` | Algebraic Reductions of Knowledge; not cited in ABF26 main sections. |
| `lch14.pdf` | Novel polynomial basis (LCH); background for binary-field RS; outside ABF26 scope. |
| `hab22.pdf` | FRI exposition by Häböck; cited as [Hab25] in ABF26 T4.12 for parameter improvements. Mostly survey/exposition — cite in docstrings, don't formalise. |
| `short_pcp.pdf` | Ben-Sasson–Sudan short PCPs; historical context only. |

### Implications for the plan

- **No new statement-layer gap discovered** from the bibliography survey
  *except* BCGM25 (polynomial generators preserve MCA). This should be
  added to `ABF26_PLAN.md` §6 external-admit ledger as a new item between
  T4.14 and T4.15, or as a "T4.x-prime" extension.
- **L2.21 docstring should cite [DP25]** explicitly for the distance
  equality remark (currently the docstring removed the [DP25] reference
  because the bibtex key wasn't in the knowledge base; we can mention it
  in prose without a bracketed citation).
- **`Hab25` improvements** to T4.12 (parameter regime) are referenced in
  the paper but my branch's T4.12 statement uses the BCHKS25 form. This
  is fine — Hab25 is a parameter improvement, not a new theorem.

## 10. Updated coverage matrix (after bibliography survey)

Full statement-layer status for all ABF26 items, grouped by source paper:

| Source | ABF26 items underwritten | Branch status |
|---|---|---|
| [Eli57] | L3.7 | stated |
| [Joh62] | T3.2 | stated |
| [GR08] | D2.15 FRS | present |
| [BKR06] | T3.12 | stated |
| [GHSZ02] | T3.13 | stated |
| [JH01] | T3.14 | stated |
| [BS08] (BS-Sudan) | (background only) | n/a |
| [GRS12] | L6.5 (deferred) | not yet stated |
| [GX13] | D2.16 subspace-design | present |
| [GK16] | T2.18 FRS half | stated |
| [GCXK25] | T5.1 | stated |
| [BKS18] | (background MCA progress) | n/a |
| [BGKS20] | T4.11.2, T5.4 | stated |
| [BCIKS20] | T4.9.1, T4.11.x | partly proved (subtree) + stated |
| [AHIV17/22] | T4.8 | proved (AHIV22) + statement form stated |
| [AGL23] | T3.10 | stated |
| [BDG24] | T3.10 | stated (joint with AGL23) |
| [GLMRSW22] | T3.11 | stated |
| [BGM23] | T3.6 random RS | deferred |
| [GZ23] | T3.6 random RS | deferred |
| [AGL24] | T3.6 random RS | deferred |
| [GG25] | T3.4, C3.5, T4.13, T4.14, T4.15, T4.21, L2.17, line-decoding | all stated |
| [CZ25] | T3.4, C3.5 | stated |
| [GKL24] | T4.11.1 | stated |
| [BCHKS25] | T4.9.2, T4.12, T4.16, T4.18, T5.2 | stated |
| [KK25] | T4.16 (joint) | stated |
| [CS25] | T4.17, T5.3 | stated |
| [Hab25] | T4.12 parameter improvement | not separately stated (subsumed by BCHKS25 form) |
| [DG25] | L4.19 | stated |
| [DP25] | L2.21 distance equality (background) | docstring mention; not separate statement |
| [ACFY25] (WHIR/STIR) | L4.6 (MCA = CA below δ_min/2), MCA definitional shape | stated; L4.6 admitted |
| **[BCGM25]** | **Polynomial-generator MCA (extends T4.13/T4.14)** | **NEW GAP — add to external-admit ledger** |
| [NA25] | toy-problem motivation | n/a (cited in §6 intro only) |
| [BCFW25] | toy-problem motivation | n/a (cited in §6 intro only) |
| [CGHLL26] | T4.16 lower bound (joint) | mentioned in T4.16 docstring |
| [CW07] | T3.15 hardness | explicitly out of scope |
| [CHK25] | (Guruswami-Sudan derandomization, §3.1 page 12 background) | not in `ABF26-T*` |

**Action items from this matrix:**

1. Add a **BCGM25 statement** (polynomial generators preserve MCA) to the
   external-admit ledger. Likely lives in
   `ProximityGap/CapacityBounds.lean` between T4.14 and T4.15. State as
   tagged sorry citing [BCGM25].
2. Update `ExtensionCodes.lean` L2.21 docstring to mention [DP25] for
   the distance equality remark, in prose.
3. Update `CapacityBounds.lean` T4.12 docstring to note [Hab25] as a
   parameter-improvement reference.

These are small docstring/statement additions, not refactors. Include
them in Phase 1 of the sequencing.
