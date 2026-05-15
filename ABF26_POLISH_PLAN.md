# ABF26 Polish Plan

Companion to [`ABF26_PLAN.md`](ABF26_PLAN.md). Tracks the correctness and integration
polish of the ABF26 formalisation work after the statement layer was completed.

The goal is **not** to add new content. Every change here is one of:

- A fix to an existing statement so that it faithfully reflects ABF26.
- A refactor that brings an existing definition or notation into line with
  pre-existing ArkLib conventions.
- A bridge lemma that ties a paper-shaped definition to an existing ArkLib peer.

**Hard invariant:** nothing in the rest of ArkLib breaks. After every commit,
`./scripts/validate.sh` must pass with no new errors and no new `sorry`s outside
this work's tagged-external-admit set.

## 0. Working principles

- **No statement rewrites without paper re-read.** Each correctness fix must be
  justified by quoting the paper line being matched against.
- **Additive commits.** Do not amend, squash, or rebase prior session commits.
  Polish lands as new commits on top.
- **Smallest reversible unit.** One commit per fix category, not per file.
- **Status legend** (used in §1 and §2 tables):
  - `⏳ pending` — not yet audited.
  - `✅ verified` — read against paper, no fix needed.
  - `⚠ fix needed` — issue identified; fix planned.
  - `🔧 fixed` — fix landed in a follow-up commit.
  - `❌ broken` — material divergence from paper; needs re-statement.
  - `⏸ deferred decision` — known issue; deliberately left open pending a future decision point.

## 1. Correctness review (per statement)

For each statement: re-read paper text, then check Lean against it. Focus on
types, quantifier structure, well-definedness of RHS, and faithful dependency
on prior items. The "Known issues" column pre-loads concerns spotted during
the original drafting session — they should be confirmed or refuted, not
trusted blindly.

### §1 — Grand Challenges ([GrandChallenges.lean](ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean))

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| §1 | `ProximityGap.grandMCAChallenge` | ✅ | Maximality `>` correct (paper says "bound fails strictly above"); `δ ≤ 1` correct (paper says `δ_C_star ∈ [0, 1]`). |
| §1 | `ProximityGap.grandListDecodingChallenge` | ✅ | ENNReal multiplication is commutative, no zero-times-infinity case (`Fintype.card F ≠ 0`). `m : ℕ` matches paper's "constant interleaving parameter `m`". |

### §2 — Preliminaries

#### [ABF26Prelims.lean](ArkLib/Data/CodingTheory/ABF26Prelims.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| D2.2 | `CodingTheory.qEntropy` | 🔧 | **Boundary documented.** Decision: keep `q : ℕ` (no precondition) since consumers already guard (T4.17 `10 ≤ |F|`, T3.11 `Prime q`). Docstring now spells out `qEntropy 0 _ = qEntropy 1 _ = 0` so future readers aren't surprised. Set-entropy wrapper still call-site-only. |
| D2.3 | `CodingTheory.restrictedRelHammingDist` | ✅ | NNReal's `0/0 = 0` makes `Δ_∅ = 0` — the natural "vacuously agree" convention. Paper is silent on empty-T; ours is a reasonable totalisation. Docstring notes the choice. |
| D2.4 | `CodingTheory.hammingBallVolume` | ✅ | `⌊δ·n⌋₊` matches paper. `q = 0` boundary: Nat subtraction `0 - 1 = 0`, `0^0 = 1` in Mathlib, so the `i = 0` term contributes `Nat.choose n 0 · 1 = 1`. Higher `i` terms give 0. Volume well-defined throughout. |

#### [ABF26CodeFamilies.lean](ArkLib/Data/CodingTheory/ABF26CodeFamilies.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| D2.13 | `ReedSolomon.Interleaved.irsCode` | 🔧 | **Rounding documented** + **promoted to `Submodule F (ι → Fin s → F)`**. Closure proofs delegate to underlying RS's `.add_mem` / `.zero_mem` / `.smul_mem`. Now consumable as ModuleCode. |
| D2.14 | `ReedSolomon.Folded.Admissible` | ✅ | Equivalent: paper's `binom(L, 2)` (unordered) with asymmetric `α · ω^i ≠ β` means *both* `α · ω^i ≠ β` and `β · ω^i ≠ α` for each pair `{α, β}`. My ordered `∀ α β ∈ L, α ≠ β, …` quantifies over both orderings symmetrically. |
| D2.15 | `ReedSolomon.Folded.frsCode` | 🔧 | **Promoted to `Submodule F (ι → Fin s → F)`** via `(degreeLT F k).map frsEvalOnPoints`, exactly mirroring `ReedSolomon.code`. Paper-style membership preserved by the `mem_frsCode_iff` iff lemma. |
| D2.16 | `CodingTheory.IsSubspaceDesign` | 🔧 | **Equivalence bridge added** (`ker_proj_eq_vanish_at`): `(ker(LinearMap.proj i) : Set _) = {a | a i = 0}`, proving the paper's comprehension form is exactly the kernel used in the definition. Outstanding concern (now isolated): paper's `dim A ≤ r` for `r : ℕ` rules out infinite-dim by construction; `Module.finrank` returns `0` for infinite-dim modules which makes the constraint vacuous there. Document if it bites downstream. |
| L2.17 | `CodingTheory.subspaceDesign_tau_lower` | ✅ | Matches `LinearCode.rate`: both expand to `(dim MC : ℝ) / (length MC : ℝ)` for an F-linear code, modulo `ℚ≥0` vs `ℝ` type. Mathematically the same rate. |
| T2.18 | `CodingTheory.frs_is_subspaceDesign_gk16` | 🔧 | **Off-by-one in τ profile fixed.** Changed `Finset.range s` → `Finset.Icc 1 s` so `r ∈ {1, …, s}` matches paper's `[s]`. Docstring updated to call out the one-based convention. |

#### [ExtensionCodes.lean](ArkLib/Data/CodingTheory/ExtensionCodes.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| D2.19 | `CodingTheory.ExtensionFieldPresentation` | 🔧 | **B-linearity certified.** Added `φ_add` and `φ_smul_psi` fields to the structure; derived `coord_add` and `coord_psi_smul` lemmas. The structure now witnesses `B`-linearity of `φ` and (componentwise) of `P.coord`. Full `[Algebra B F]`-based Mathlib refactor still possible but no longer blocking — see B5. |
| D2.19 | `CodingTheory.ExtensionFieldPresentation.IsSystematic` | ✅ | `i.val = 0` is equivalent to `i = ⟨0, _⟩` modulo `Fin.val` injectivity. For `P.e = 0`, `Fin 0` is empty so `IsSystematic` is vacuously true — degenerate but consistent. Downstream theorems implicitly assume `P.e ≥ 1`. |
| D2.20 | `CodingTheory.extensionCode` | 🔧 | Added `extensionCode_iff_coord_in_base` (iff). **Added closure lemmas** `extensionCode_add_mem` and `extensionCode_psi_smul_mem` certifying closure under addition and the `ψ`-induced B-scalar action (assuming `C_B` is correspondingly closed). Both proved, not admitted. Full F-Submodule promotion (closure under arbitrary F-scalar mult, requiring basis expansion) still gated on `[Algebra B F] + [Module.Finite B F] + Basis` — explicitly documented in the docstring. |
| L2.21 | `CodingTheory.lambda_extensionCode_eq_lambda_interleaved` | ✅ | `Code.interleavedCodeSet (κ := Fin P.e) C_B` matches paper's `C_B^≡e` exactly (`κ = Fin e` is the interleaving-factor type, and `e := P.e` is the extension dimension). |

### §3 — List Decoding

#### [JohnsonBound/ABF26.lean](ArkLib/Data/CodingTheory/JohnsonBound/ABF26.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| D3.1 | `JohnsonBound.Jqℓ` | ✅ | `1 - frac * lFac * δ` with `*` left-associative parses as `1 - ((frac * lFac) * δ)` = `1 - (frac · lFac · δ)`. Matches paper's `1 - q/(q-1) · ℓ/(ℓ-1) · δ`. |
| D3.1 | `JohnsonBound.Jcap` | ✅ | Definition `1 − √(1 − δ)` matches paper exactly; boundary simp lemmas check out. |
| T3.2 | `CodingTheory.johnson_bound_lambda_le_ell` | ⚠ | Statement uses `Set (ι → F)` over a `Field F`, taking `F` as the alphabet. Paper's "code over `Σ^n`" with arbitrary `Σ` is strictly broader. For RS-style applications our statement covers it; for general non-field alphabets we'd need a `[DecidableEq Σ] [Fintype Σ]` variant. Mark for follow-up if a non-field call site appears. |
| C3.3 | `CodingTheory.mds_johnson_lambda_le` | ✅ | The MDS hypothesis `δ_min = 1 - ρ + 1/n` is the *consequence* of Singleton-tight, which is the paper's MDS definition. Either encoding is equivalent. Keeping the consequence form keeps the statement self-contained. |

#### [ListDecodingBounds.lean](ArkLib/Data/CodingTheory/ListDecodingBounds.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| L3.7 | `CodingTheory.linear_lambda_ge_elias_volume_eli57` | 🔧 | **Nat-subtraction fix:** cast both `Fintype.card ι` and `Module.finrank F C` to `ℝ` before subtracting; wrap whole RHS in `ENNReal.ofReal`. Uses `Real.rpow` so `|F|^{n−k}` is well-defined even if Lean can't see `k ≤ n`. |
| C3.8 | `CodingTheory.linear_lambda_ge_entropy_volume` | ✅ | Lean precedence: `^` binds tighter than `*` binds tighter than `/`. So `q ^ E / X ^ ((1:ℝ)/2)` parses as `(q^E) / (X^(1/2))`. Matches paper's `q^{…} / √{…}`. |
| T3.9 | `CodingTheory.linear_C_le_generalized_singleton_st20` | 🔧 | **Nat-subtraction fix:** kept the floor (paper has `⌊…⌋`, dropping it would tighten the bound) but cast both `Fintype.card ι` and `Nat.floor (…)` to `ℝ` before subtracting. Real-valued exponent. |
| T3.10 | `CodingTheory.large_alphabet_barrier_bdg24_agl23` | ✅ | Premise `Lambda C … ≤ (ℓ : ℕ∞)` matches paper's "code with `\|Λ(C, …)\| ≤ ℓ`". Existential `∃ n₀` correctly captures paper's "sufficiently large `n`". |
| T3.11 | `CodingTheory.random_linear_lambda_lower_glmrsw22` | 🔧 | **Broadened `Nat.Prime q` to `IsPrimePow q`** to match paper's "prime power". |
| T3.12 | `CodingTheory.rs_lambda_superpoly_extension_bkr06` | 🔧 | Same fix: `Nat.Prime (qs i)` → `IsPrimePow (qs i)`. Bound `q^{(α-β²)·log q}` parses correctly; equivalent to paper's `2^{(α-β²)·(log q)²}` since `q^x = 2^{x·log₂ q}` — paper's two forms are notational variants, my code uses the first. |
| T3.13 | `CodingTheory.rs_lambda_large_prime_ghsz02` | 🔧 | **Weakened to `∃ c > 0, … > c · p^…`** matching paper's `Ω(p^{p^α·β/2})`. Without the constant, strict `> p^…` would overstate. |
| T3.14 | `CodingTheory.rs_lambda_high_rate_jh01` | 🔧 | `Nat.Prime (qs i)` → `IsPrimePow (qs i)` to match paper's "prime powers". Mod condition `qs i % (j + 1) = 1` matches paper's `q ≡ 1 (mod j+1)`. |
| T3.4 | `CodingTheory.subspaceDesign_list_decoding_cz25` | ✅ | `τ : ℕ → ℝ` so `τ(1/η)` needs `1/η` cast to ℕ. `Nat.floor (1/η)` is the standard interpretation; paper presumably means the same (it uses the value `1/η` without further specification). |
| C3.5 | `CodingTheory.frs_list_decoding_capacity_cz25` | 🔧 | **Refactored to `Lambda`** for consistency with T3.4 and paper notation `\|Λ(C, δ)\|`. Now reads `Lambda (frsCode …) δ ≤ ENNReal.ofReal bound` instead of `∀ y, .ncard ≤ bound`. |

### §4 — Correlated Agreement

#### [LineDecoding.lean](ArkLib/Data/CodingTheory/LineDecoding.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| D4.20 | `CodingTheory.LineDecodable` | ✅ | Choice documented in docstring; equivalent to paper's `U : F → C` formulation. |
| T4.21 | `CodingTheory.lineDecodable_imp_epsMCA_le` | ✅ | `(Fintype.card ι : ℝ≥0) + 1` matches paper's `n + 1`; final ENNReal RHS is `a / |F|` cast via direct division on ENNReals. |

#### [ProximityGap/CapacityBounds.lean](ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| T4.11.1 | `CodingTheory.linear_epsMCA_1_5_johnson_gkl24` | 🔧 | **Added `η < δ_min` hypothesis** so `1 − δ_min + η < 1` and the denominator `∛x − √x` is strictly positive (since for `x < 1`, `∛x > √x`). Docstring spells out the implicit regime. |
| T4.11.2 | `CodingTheory.linear_epsCA_1_5_johnson_bgks20` | 🔧 | **Added `η < δ_min` for hypothesis-parity with Item 1** (paper presents both under one regime statement). The RHS `2 / (η²|F|)` doesn't need it but matching keeps the API symmetric. |
| T4.9.2 | `CodingTheory.rs_epsCA_bchks25_item2` | ✅ | `Code.minDist (…) / Fintype.card ι / 3 ≤ δ_fld` parses left-associatively as `(δ_min / 3) ≤ δ_fld`, matching paper. `max a b` with negative `a` → `b` wins; `ENNReal.ofReal` of a positive max is the positive value. Bound vacuously holds outside the regime. |
| R4.10 | `CodingTheory.rs_epsCA_small_loss_r4_10` | ✅ | `γ ∈ (0, 1)` parameter matches paper's dimensionless slack convention `(δ_int - δ_fld) = γ/n`. My bound formula uses `γ` (not `γ/n`) directly; consistent with paper. |
| T4.12 | `CodingTheory.rs_epsMCA_johnson_range_bchks25` | ✅ | All `^` with real exponents elaborate to `Real.rpow` (verified by C2 sweep). `max ⌈x⌉ 3 : ℝ` with `⌈⌉` going through `Nat.ceil` cast to ℝ; Lean unifies via the `letI` target. |
| T4.13 | `CodingTheory.subspaceDesign_epsMCA_gg25` | ✅ | `τ (t + 1)` matches paper's `r = t + 1` substitution. |
| T4.14 | `CodingTheory.frs_epsMCA_capacity_gg25` | 🔧 | **Refactored** (existential dropped) **+ submodule-aware** (frsCode is now a Submodule, coerced to Set via `(… : Set _)` for `epsMCA`'s argument). |
| T4.16 | `CodingTheory.rs_epsCA_lower_capacity_bchks25_kk25` | 🔧 | **Added power-of-two `n` constraint** as `∃ p : ℕ, Fintype.card ιC = 2 ^ p` in the existential body. "|F| = poly(n)" stays in the docstring (no polynomial-time predicate in Mathlib). |
| T4.17 | `CodingTheory.rs_epsCA_breakdown_cs25` | ✅ | Paper's regime `1 - H_q(δ) + 2/n + √((H_q(δ) - δ)/n) ≤ ρ` implicitly assumes `H_q(δ) ≥ δ` (else the sqrt argument is negative). Outside this regime my hypothesis becomes a tighter inequality (sqrt → 0), making the bound stricter — vacuously consistent. |
| T4.18 | `CodingTheory.rs_epsCA_johnson_jump_bchks25` | 🔧 | **Relaxed exact-equality to a two-sided bound** `|F|^{(1+ε)/2} - 1 ≤ n ≤ |F|^{(1+ε)/2} + 1`, which is the natural reading of paper's `n = |F|^{(1+ε)/2}` when the RHS is generally non-integral. Docstring spells out the choice. |
| L4.19 | `CodingTheory.linear_epsCA_ge_sampling_dg25` | ✅ | `relDistFromCode : (ι → F) → Set (ι → F) → ENNReal` per `Basic/RelativeDistance.lean:47`. My `⨆ u, δᵣ(u, ↑C) : ENNReal` types check. |

### §5 — Connections

#### [Connections.lean](ArkLib/Data/CodingTheory/Connections.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| T5.1 | `CodingTheory.linear_listSize_to_epsMCA_gcxk25` | 🔧 | **Added `η ≤ δ` hypothesis** so `1 − δ + η ≤ 1` and the sqrt-proximity radius stays in `[0, 1]`. Docstring spells out the implicit requirement. |
| T5.2 | `CodingTheory.rs_epsCA_small_implies_lambda_lt_F_bchks25` | ✅ | `(δ + 2 / Fintype.card ι).toNNReal` non-truncating: `δ > 0` and `2/n > 0` for `n ≥ 1`. |
| T5.3 | `CodingTheory.rs_epsCA_implies_lambda_extended_cs25` | 🔧 | **Refactored.** Replaced double-wrap with direct `Nat.ceil (…) : ℕ∞` comparison against `Lambda`. Restored the paper's integer ceiling so we don't overstate (`Lambda ≤ x` would be strictly stronger than paper's `Lambda ≤ ⌈x⌉`). |
| T5.4 | `CodingTheory.rs_epsCA_separation_bgks20` | ✅ | Paper's "evaluation domain is the entire `F`" matches `Fintype.card F = Fintype.card ι` + `domain : ι ↪ F` (injective + same cardinality ⇒ bijective by pigeonhole). Standard encoding. |

## 2. Integration review (per axis)

Each axis below is a sweep across all files committed in this session.

### 2a. Types and operator conventions

| Concern | Status | Files affected | Notes |
| --- | --- | --- | --- |
| Distance return type: `ℚ≥0` vs `ℝ≥0` vs `ℝ` | ✅ | `ABF26Prelims.lean` (`restrictedRelHammingDist : ℝ≥0`); `Basic/RelativeDistance.lean` (`relHammingDist : ℚ≥0`). | **Bridged via B1** (`restrictedRelHammingDist_univ`). Mixed return types are acceptable because the bridge lemma lets callers convert freely; forcing one type system-wide would be a bigger refactor than the benefit warrants. |
| Probability bounds: `ENNReal` vs `ℝ≥0` | ✅ | All ε-bounds files. | Spot-checked: `EpsilonErrors.lean` uses `ENNReal` for `epsCA` / `epsMCA` / `epsPG`; new files consume them at the same type. No mixed conventions. |
| `epsCA` / `epsMCA` argument: `Set` vs `Submodule` | ✅ | `EpsilonErrors.lean`. | **Decision documented in file header.** Definitions stay `Set`-based — they're pure predicates over a codeword set, neither uses linearity. Theorems that need linearity add a `Submodule F (ι → A)` hypothesis separately. Avoids narrowing the API for a one-character win at each call site. |
| `ENNReal.ofReal` vs `(x : ENNReal)` direct cast | ✅ | `CapacityBounds.lean`, `ListDecodingBounds.lean`, `Connections.lean`. | **Verified.** Convention now documented in the file docstrings of `CapacityBounds.lean` and `Connections.lean`; `ListDecodingBounds.lean` uses `ENNReal.ofReal` exclusively (no `.toNNReal`). Rule held throughout: `ENNReal.ofReal` for ℝ-valued sources, direct cast for `ℝ≥0` / `ℕ` sources. |
| Nat subtraction silently truncating | ⚠ | `linear_lambda_ge_elias_volume_eli57` (L3.7), `linear_C_le_generalized_singleton_st20` (T3.9), possibly T4.11.x denominators. | Cast to ℤ or ℝ before subtracting; or add positivity hypothesis. |
| `Real.rpow` vs `HPow.hPow` for non-integer exponents | ✅ | Anywhere `^ ((1 : ℝ) / 2)` or `^ ((1 : ℝ) / 3)` appears. | **Verified.** Every `^` whose exponent has type `ℝ` elaborates to `Real.rpow` (build clean). Small-integer powers like `β ^ 2` use `Monoid.npow` (mathematically identical to `Real.rpow β 2`). No accidental Nat exponent picks. |
| `.toNNReal` truncation of negative reals | 🔧 | T5.1, T4.16, T4.17, T4.18 bound expressions. | **Documented file-by-file.** `Connections.lean` and `CapacityBounds.lean` each have a "Proximity-radius coercion" docstring section explaining: each `.toNNReal` is either provably non-negative under hypotheses (standard) or aligned with the paper's stated regime so truncation matches the vacuous case (e.g. T4.13). |

### 2b. Existing-vs-new definitions

**ModuleCode unification.** ArkLib's canonical F-linear-code abstraction is
`ModuleCode ι F A := Submodule F (ι → A)`. Three new defs were initially set-typed:
`irsCode`, `frsCode`, `extensionCode`. After polish:

- 🔧 **`frsCode`** refactored to `Submodule F (ι → Fin s → F)` via a new linear encoder
  map `frsEvalOnPoints : F[X] →ₗ[F] (ι → Fin s → F)` and `(degreeLT F k).map`, exactly
  mirroring `ReedSolomon.code`. Plus three sanity lemmas: `mem_frsCode_iff`,
  `mem_frsCode_iff_flipped`, `mem_frsCode_one_iff_mem_rsCode` (s=1 collapse to RS).
- 🔧 **`irsCode`** refactored to `Submodule F (ι → Fin s → F)` with explicit closure
  proofs `(rs.add_mem (hU j) (hV j))` style — short, no machinery.
- 🔧 **`extensionCode`** stays a `Set`, but `ExtensionFieldPresentation` now certifies
  `B`-linearity via `φ_add` + `φ_smul_psi` fields. Added `coord_add`,
  `coord_psi_smul`, `extensionCode_add_mem`, `extensionCode_psi_smul_mem` lemmas —
  all proved. **F-scalar closure** stated as `extensionCode_smul_mem` with a
  tagged-sorry — proof needs F-algebra structure constants from `[Algebra B F]`
  refactor (B5).

The refactor lets T2.18, T4.14, C3.5 consume `frsCode` / `irsCode` directly without
existential `∃ C, C = … ∧ …` wraps. T2.18 in particular collapses from a 3-conjunct
existential to a single `IsSubspaceDesign s τ (frsCode …)`.

| New name | Existing peer | Status | Action |
| --- | --- | --- | --- |
| `CodingTheory.restrictedRelHammingDist` | `Code.relHammingDist`, `Code.relDistFromCode` in `Basic/RelativeDistance.lean` | 🔧 | Added `restrictedRelHammingDist_univ : restrictedRelHammingDist Finset.univ f g = (Code.relHammingDist f g : ℝ≥0)`. Lets downstream theorems convert freely between paper's `Δ_T` and existing `δᵣ(u, v)`. Bridge proved (not admitted). |
| `CodingTheory.hammingBallVolume` | `ListDecodable.hammingBall` in `ListDecodability.lean` | 🔧 | Added `hammingBallVolume_eq_ncard_hammingBall`: bridge to `.ncard` of `hammingBall y ⌊δ·n⌋`. **Distance-partition step proved**; decomposed remaining work into `card_filter_hammingDist_eq` (combinatorial count, factored as a separate lemma) + a small Set/Finset conversion sub-sorry. Net: 1 sorry → 2 smaller sorries. |
| `CodingTheory.qEntropy` | `Real.negMulLog`, Mathlib's binary-entropy lemmas | ✅ | Mathlib has `Real.binEntropy` (binary entropy) but no q-ary variant. Keep ours; revisit if Mathlib adds one. |
| `JohnsonBound.Jcap` vs existing `J` (= paper's `J_q`) | `JohnsonBound.J` | ✅ | **Decision: keep both** with prominent docstring (Option A). Renaming existing `J → Jq` would break callers throughout `JohnsonBound/Basic.lean` and downstream — not worth the paper-name alignment given the docstring already disambiguates. |
| `CodingTheory.ExtensionFieldPresentation` | `Algebra B F`, `Module.Finite`, `Basis` (Mathlib) | ⏸ | **B5 deferred.** B-linearity certified via `φ_add` / `φ_smul_psi`. Full Mathlib refactor (replace `ψ, e, φ, φ_inv, …` with `[Algebra B F] + [Module.Finite B F] + Basis B F`) would unlock `extensionCode_smul_mem`'s proof (the structure constants come from `Basis.equivFun` applied to multiplication). Significant invasive change touching `Connections.lean`, `IsSystematic`, `coord`, and all closure lemmas. Deferred until a downstream proof actually pulls on it. |
| `CodingTheory.IsSubspaceDesign` formulation | `LinearMap.proj` vs comprehension | 🔧 | Added `ker_proj_eq_vanish_at`: a `Set`-level equality showing `(ker (LinearMap.proj i) : Set _) = {a | a i = 0}`. Proves the paper's comprehension form is exactly the kernel used in the definition. Lemma proved (one-line `ext` + `simp`). |
| `ReedSolomon.Interleaved.irsCode` | `interleavedCodeSet`, `^⋈` notation | 🔧 | **Refactored to `Submodule F (ι → Fin s → F)`** with explicit closure proofs delegating to the underlying RS code's `.add_mem` / `.zero_mem` / `.smul_mem`. Now first-class ModuleCode. |
| `ReedSolomon.Folded.frsCode` | `ReedSolomon.code` using `Polynomial.degreeLT` | 🔧 | **Refactored to `Submodule F (ι → Fin s → F)`** via `(degreeLT F k).map frsEvalOnPoints`. Membership equivalence preserved by `mem_frsCode_iff`. Now first-class ModuleCode. |
| `CodingTheory.extensionCode` | encoder-image vs set-of-codewords | 🔧 | Added `extensionCode_iff_coord_in_base`: makes the "each coordinate-projection is in `C_B`" view explicit. The full encoder-image equivalence (`v = φ_inv(c^{(1)}, …, c^{(e)})`) is a corollary of `φ`-bijectivity; downstream users can build it from this iff plus `φ`'s inverse. Lemma is definitional (`rfl`). |
| `CodingTheory.Lambda` (extended earlier in session) | `closeCodewordsRel`, `listDecodable` | ✅ | Already integrated; no action. |

### 2c. Namespace and file layout

| Concern | Status | Action |
| --- | --- | --- |
| `CodingTheory.*` vs `ProximityGap.*` vs `ABF26.*` | ✅ | Established split: `ProximityGap.*` for ε-functions (`epsCA`, `epsMCA`, `epsPG`); `CodingTheory.*` for all paper-statement theorems. `ABF26.*` namespace not introduced — names are descriptive (per plan D2). |
| `ABF26Prelims.lean` filename prefix | ⏸ | **Deferred decision.** Topical names (`Entropy.lean`, etc.) more discoverable, but renaming touches imports across multiple files; not worth doing until paper-statement set stabilises. Re-evaluate after first tagged-sorry discharge. |
| `ABF26CodeFamilies.lean` vs split per family | ✅ | Current size ~200 lines, well under the ~300-line threshold. Single file remains preferable for now. Revisit if file grows. |
| `Connections.lean`, `LineDecoding.lean`, `ExtensionCodes.lean` | ✅ | 1–4 statements each; each is topically coherent. Keep separate. |

### 2d. Notation alignment

| Concern | Status | Action |
| --- | --- | --- |
| Paper-style `RS[F, L, k]`, `IRS[F, L, k, s]`, `FRS[F, L, k, s, ω]` | ⏸ | **Deferred decision per plan D2 (descriptive names preferred).** Concrete call sites exist; revisit after first downstream proof discharges a tagged sorry — that will surface notation pain (or its absence). |
| `^⋈` for interleaved code usage | ⏸ | **Deferred decision.** Some files use `^⋈` (e.g. `GrandChallenges.lean`), others call `Code.interleavedCodeSet` directly. Both work. Standardise when the call-site count grows. |
| `Δ_T(f, g)`, `Λ(C, δ, f)`, `δ_min` paper notation | ⏸ | **Deferred decision.** All-or-nothing call; defer until statement set is stable. Existing notation (`Δ₀`, `δᵣ`) already covers the closest equivalents. |

### 2e. Tagged-sorry hygiene

| Concern | Status | Action |
| --- | --- | --- |
| Comment-line style for tagged sorries | 🔧 | **Canonical shape:** `sorry -- ABF26-X.Y; <classification> [Citation].` where classification ∈ {external admit, bridge, derived, in-tree admit}. Swept all 29 tagged sorries: one outlier (T4.21) used "external admit; see [...]" instead of "external admit [...]"; normalised. Remaining variations (bridge / derived qualifiers) carry genuine information and are kept. |
| `ABF26-X.Y` tag matches paper ID and audit row | ✅ | Swept all 29 tagged sorries; each tag matches the audit-doc row and the paper-section ID it cites. |
| Paper-page reference in docstring | ⏸ | **Deferred (cosmetic).** Most statements cite a paper theorem ID (e.g. `[GG25 Cor 4.10]`) which is the stable lookup key. Page numbers help but aren't blocking; defer until first paper revision creates a need to standardise. |

## 3. Execution plan

Execute in this order — earlier passes affect statement meaning, so they're load-bearing for later passes.

### Pass A: Correctness fixes (high priority)

Resolve every `⚠` and `❌` in §1. One commit per concern, smallest reversible unit:

1. **A1.** ✅ Fix T2.18 off-by-one in τ profile (`Finset.range s` → `Finset.Icc 1 s`).
2. **A2.** ✅ Fix Nat-subtraction in L3.7 and T3.9 exponents (cast to ℝ before subtracting; preserves paper's floor in T3.9).
3. **A3.** ✅ Document `qEntropy` boundary at `q ≤ 1` (no precondition; downstream already guards).
4. **A4.** ✅ Document `irsCode` rounding convention (Nat truncated division; downstream guards with `s ∣ k`).
5. **A5.** ✅ Tighten T5.1 hypotheses with `η ≤ δ`.
6. **A6.** ✅ Tighten T4.11.1 / T4.11.2 with `η < δ_min` (shared regime hypothesis).
7. **A7.** ✅ Align `frsCode` (D2.15) to `Polynomial.degreeLT` style.

After each fix: `./scripts/validate.sh` must pass.

### Pass B: Integration of definitions

Apply 2b actions in dependency order:

1. **B1.** ✅ Add `restrictedRelHammingDist Finset.univ f g = (Code.relHammingDist f g : ℝ≥0)` bridge.
2. **B2.** 🔧 Add `hammingBallVolume_eq_ncard_hammingBall` bridge. Partition step
   proved; combinatorial count and Set/Finset conversion split out as smaller
   tagged sorries.
3. **B3.** ✅ Add `ker_proj_eq_vanish_at` Set-level bridge (proved).
4. **B4.** ✅ Add `extensionCode_iff_coord_in_base` definitional iff lemma.
5. **B5.** ⏸ **Deferred.** Refactor `ExtensionFieldPresentation` to thin Mathlib wrapper (`[Algebra B F] + Basis`). Unlocks `extensionCode_smul_mem`'s proof but is a significant invasive change. Tracked as a known follow-up.

### Pass C: Operator and type convention sweep

Apply 2a actions:

1. **C1.** ✅ Standardise `.toNNReal` usage via file-level "Proximity-radius coercion" docstrings in `Connections.lean` and `CapacityBounds.lean`.
2. **C2.** ✅ Sweep `^ : ℝ → ℝ` usages — verified all elaborate to `Real.rpow` correctly.
3. **C3.** ✅ Standardise `ENNReal.ofReal` vs ENNReal cast — verified by file-header documentation.

### Pass D: Notation, namespace, hygiene

Apply 2c–2e actions. Lowest priority — leave until A–C stable.

1. **D1.** ✅ Sweep tagged-sorry comments for uniform style — one outlier (T4.21) normalised.
2. **D2.** Deferred (cosmetic; not blocking).
3. **D3.** Deferred (optional).
4. **D4.** Deferred (optional).

### Pass E: Post-refactor follow-ups (round 2)

Items surfaced by the ModuleCode-unification review:

1. **E1.** 🔧 Dim lemmas:
   - `dim_frsCode` **proved** (no sorry) via `Submodule.equivMapOfInjective` chained
     with `Polynomial.degreeLTEquiv`. Hypothesis: `Function.Injective` on the
     encoder.
   - `dim_irsCode` still tagged-sorry, but with a sharper proof sketch documenting
     the `LinearEquiv` to `Fin s → (RS code)` + `Module.finrank_pi` path.
2. **E2.** ✅ Strengthen `mem_frsCode_one_iff_mem_rsCode` to a Submodule-level
   `frsCode_one_map_eq_rsCode` (proved, not admitted).
3. **E3.** ✅ T3.2 alphabet generality — broadened `[Field F]` to
   `[Fintype α] [DecidableEq α]`.
4. **E4.** 🔧 `extensionCode_smul_mem` stated (full F-Submodule promotion) — proof
   tagged-sorry, gated on B5 refactor or structure-constants field.
5. **E5.** ⏸ B5 deferred (see above) — Mathlib structural refactor of
   `ExtensionFieldPresentation`. Would unlock E4's proof.

### Pass F: Round-3 integration with ArkLib conventions

Audit + refactors driven by the question "what else can be unified with existing
ArkLib defs / notations / conventions?":

1. **F-A. `δᵣ C` / `minRelHammingDistCode`** — skipped. `δᵣ C` returns `ℚ≥0`; my
   statements use `ℝ` for paper-faithful real bounds. Switching would *add* casts,
   not remove them. Current `(Code.minDist C : ℝ) / Fintype.card ι` form stays.
2. **F-B. `Code ι α` vs `Set (ι → α)`** — skipped. `Code` abbrev is local to
   `ListDecodability.lean`; the rest of ArkLib (BCIKS20, ProximityGap.Basic, …)
   uses `Set (ι → α)` directly. Switching mine would create new inconsistency.
3. **F-C.** 🔧 `^⋈` notation for `irsCode` — refactored to
   `(ReedSolomon.code domain (k / s)) ^⋈ (Fin s)` via `ModuleCode`'s
   `CodeInterleavable` instance. `irsCode` is now a 1-line def.
4. **F-D. `frsEvalOnPoints` from `evalOnPoints`** — skipped. The two encoders have
   genuinely different return shapes (`ι → Fin s → F` vs `ι → F`); deriving one
   from the other would require an artificial wrapper. Not a clean refactor.
5. **F-E.** 🔧 `IsMDS` predicate added to `JohnsonBound/ABF26.lean`. `mds_johnson_lambda_le`
   now takes `IsMDS C ρ` instead of the inlined Singleton-tight equation. Reusable
   for any future MDS-conditional theorem.
6. **F-F.** ✅ `closeCodewordsRel` → `Lambda_at` consistency: verified clean across
   all new files. C3.5 refactor caught the only straggler.
7. **F-G.** ✅ `Polynomial.degree < k` → `degreeLT F k` consistency: verified clean
   across all new files.

### Final validation

- `./scripts/validate.sh` full pass.
- `lake build` over entire tree.
- Manual `git diff main..HEAD` review.
- Update audit doc rows from `stated (external admit)` to indicate any post-polish refinements.
- Optionally cherry-pick the polish commits into a sub-PR for clearer review.

## 4. Deliverables

- This file (`ABF26_POLISH_PLAN.md`) updated as each item is addressed.
- A new section in [`ABF26_PLAN.md`](ABF26_PLAN.md) §6 noting which polish passes have landed.
- Audit doc rows ([open-problems-list-decoding-and-correlated-agreement.md](docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md)) updated where status descriptions change.

## 5. Out of scope for this polish pass

- Proving any of the tagged-external-admit sorries.
- Closing pre-existing in-tree sorries (BCIKS20, WHIR, DG25, etc. — tracked in `ABF26_PLAN.md` Phase 2).
- §6 toy problem work (deferred per `ABF26_PLAN.md` Phase 8).
- Random-RS distribution machinery (T3.6, T4.15 deferrals).

These remain on `ABF26_PLAN.md`'s long-term roadmap.
