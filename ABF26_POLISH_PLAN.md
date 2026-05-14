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

## 1. Correctness review (per statement)

For each statement: re-read paper text, then check Lean against it. Focus on
types, quantifier structure, well-definedness of RHS, and faithful dependency
on prior items. The "Known issues" column pre-loads concerns spotted during
the original drafting session — they should be confirmed or refuted, not
trusted blindly.

### §1 — Grand Challenges ([GrandChallenges.lean](ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean))

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| §1 | `ProximityGap.grandMCAChallenge` | ⏳ | maximality clause: `∀ δ, δ_C_star < δ → δ ≤ 1 → ε_mca(C, δ) > ε*`. Confirm `>` not `≥`. Confirm `δ ≤ 1` is correct upper bound for `δ_C_star ∈ [0, 1]`. |
| §1 | `ProximityGap.grandListDecodingChallenge` | ⏳ | `(ε_star : ENNReal) * (Fintype.card F : ENNReal)` ordering; ENNReal multiplication is OK but check no zero-times-infinity case. Verify `m : ℕ` parameter name matches paper's "constant interleaving parameter `m`". |

### §2 — Preliminaries

#### [ABF26Prelims.lean](ArkLib/Data/CodingTheory/ABF26Prelims.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| D2.2 | `CodingTheory.qEntropy` | 🔧 | **Boundary documented.** Decision: keep `q : ℕ` (no precondition) since consumers already guard (T4.17 `10 ≤ |F|`, T3.11 `Prime q`). Docstring now spells out `qEntropy 0 _ = qEntropy 1 _ = 0` so future readers aren't surprised. Set-entropy wrapper still call-site-only. |
| D2.3 | `CodingTheory.restrictedRelHammingDist` | ⏳ | `NNReal`'s `0 / 0 = 0` matches the empty-T case; confirm paper accepts that convention rather than leaving `Δ_∅` undefined. |
| D2.4 | `CodingTheory.hammingBallVolume` | ⏳ | `⌊δ * n⌋₊` rounds down; matches paper. Verify `(q - 1)^i` when `q = 0` doesn't blow up — Nat subtraction gives 0, then `0^0 = 1` (the `i = 0` term), so the i = 0 sum element is `n choose 0 = 1`. Boundary OK but worth documenting. |

#### [ABF26CodeFamilies.lean](ArkLib/Data/CodingTheory/ABF26CodeFamilies.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| D2.13 | `ReedSolomon.Interleaved.irsCode` | 🔧 | **Rounding documented.** Decision: keep unguarded `k / s` (Nat truncated division) in the definition so degenerate regimes type-check; downstream paper-quoting theorems (e.g. `dim(IRS) = k`) must add `s ∣ k` themselves. Docstring spells out the convention. |
| D2.14 | `ReedSolomon.Folded.Admissible` | ⏳ | Paper uses unordered pairs `binom(L, 2)`; my version uses ordered `∀ α β ∈ L, α ≠ β`. The asymmetric formula `α · ω^i ≠ β` means ordered is *stronger* than what the paper said but presumably equivalent. Confirm. |
| D2.15 | `ReedSolomon.Folded.frsCode` | ⚠ | Uses `p.degree < k` directly; existing ArkLib `ReedSolomon.code` uses `Polynomial.degreeLT F k`. Align. Verify the encoding `f x j = p.eval (domain x * ω ^ j)` matches paper's `f̂(x · ω^j)` exactly (multiplication side / parenthesisation). |
| D2.16 | `CodingTheory.IsSubspaceDesign` | ⚠ | `LinearMap.proj` formulation for `A_i` is technical; paper uses comprehension `{a ∈ A : a_i = 0^s}`. Add an equivalence lemma; pick one formulation as canonical. Also: paper requires `dim A ≤ r`, but `r ∈ ℕ` while `dim` lives in `ℕ∞` (here truncated to `Module.finrank` returning `ℕ`). Confirm infinite-dim ruled out. |
| L2.17 | `CodingTheory.subspaceDesign_tau_lower` | ⏳ | "rate `ρ`" in paper is implicit from `C`; my version uses `Module.finrank F C / Fintype.card ι` directly. Check this matches `LinearCode.rate` definition. |
| T2.18 | `CodingTheory.frs_is_subspaceDesign_gk16` | 🔧 | **Off-by-one in τ profile fixed.** Changed `Finset.range s` → `Finset.Icc 1 s` so `r ∈ {1, …, s}` matches paper's `[s]`. Docstring updated to call out the one-based convention. |

#### [ExtensionCodes.lean](ArkLib/Data/CodingTheory/ExtensionCodes.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| D2.19 | `CodingTheory.ExtensionFieldPresentation` | ⏳ | Structure stores `φ : F → Fin e → B` + explicit `φ_inv` + inverse witnesses. Verify this is enough to recover B-linearity (currently only used via coordinate projections — B-linearity is a *separate* claim). |
| D2.19 | `CodingTheory.ExtensionFieldPresentation.IsSystematic` | ⏳ | Uses `i.val = 0`; equivalent to `i = ⟨0, _⟩`. OK. Confirm `P.e ≥ 1` is implicit elsewhere. |
| D2.20 | `CodingTheory.extensionCode` | ⚠ | Set-level definition (image-of-encoder predicate) equivalent to paper's encoder definition only via `φ`-bijectivity. Add an `extensionCode_eq_encoder_image` lemma to bridge. |
| L2.21 | `CodingTheory.lambda_extensionCode_eq_lambda_interleaved` | ⏳ | Uses `Code.interleavedCodeSet`; confirm paper's `C_B^≡e` matches with `κ = Fin e`. |

### §3 — List Decoding

#### [JohnsonBound/ABF26.lean](ArkLib/Data/CodingTheory/JohnsonBound/ABF26.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| D3.1 | `JohnsonBound.Jqℓ` | ⏳ | Paper formula `(1 − 1/q) · (1 − √(1 − q/(q−1) · ℓ/(ℓ−1) · δ))`. Verify ordering inside the square root and that `q/(q−1) · ℓ/(ℓ−1)` is computed before multiplying by δ (precedence in Lean). |
| D3.1 | `JohnsonBound.Jcap` | ✅ | Definition `1 − √(1 − δ)` matches paper exactly; boundary simp lemmas check out. |
| T3.2 | `CodingTheory.johnson_bound_lambda_le_ell` | ⏳ | Paper says `|Σ| = q`; my Lean uses `Fintype.card F` for the alphabet. For codes over `Set (ι → F)` with `F` the alphabet, this is right — but verify against paper's "code over `Σ^n`" wording. |
| C3.3 | `CodingTheory.mds_johnson_lambda_le` | ⏳ | MDS hypothesis stated as `δ_min = 1 − ρ + 1/n` directly; consider deriving from `LinearCode.singleton_bound_linear` instead. |

#### [ListDecodingBounds.lean](ArkLib/Data/CodingTheory/ListDecodingBounds.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| L3.7 | `CodingTheory.linear_lambda_ge_elias_volume_eli57` | 🔧 | **Nat-subtraction fix:** cast both `Fintype.card ι` and `Module.finrank F C` to `ℝ` before subtracting; wrap whole RHS in `ENNReal.ofReal`. Uses `Real.rpow` so `|F|^{n−k}` is well-defined even if Lean can't see `k ≤ n`. |
| C3.8 | `CodingTheory.linear_lambda_ge_entropy_volume` | ⏳ | Operator precedence inside `ENNReal.ofReal (...)` block; verify `q^{n·(ρ−1+H_q(δ))} / √(8nδ(1−δ))` is what's parsed. |
| T3.9 | `CodingTheory.linear_C_le_generalized_singleton_st20` | 🔧 | **Nat-subtraction fix:** kept the floor (paper has `⌊…⌋`, dropping it would tighten the bound) but cast both `Fintype.card ι` and `Nat.floor (…)` to `ℝ` before subtracting. Real-valued exponent. |
| T3.10 | `CodingTheory.large_alphabet_barrier_bdg24_agl23` | ⏳ | Existential `∃ n₀, ∀ {ι} ..., n₀ ≤ Fintype.card ι → ...`. Check the `Lambda C ... ≤ (ℓ : ℕ∞)` premise direction matches paper's "any code with `|Λ(...)| ≤ ℓ` has..." |
| T3.11 | `CodingTheory.random_linear_lambda_lower_glmrsw22` | ⏳ | `Nat.Prime q` only allows primes, not prime powers; paper says "prime power". Confirm whether to keep restricted or broaden to `IsPrimePow q`. |
| T3.12 | `CodingTheory.rs_lambda_superpoly_extension_bkr06` | ⏳ | `Nat.Prime (qs i)` — same as T3.11 question. Also: paper's `2^{(α-β²)(log q)²}` exponent contains `log q` *and* the result is `q^{(α-β²) log q}`. Verify the equality `q^{(α-β²)·log q} = 2^{(α-β²)·(log q)²}` is captured in the bound. |
| T3.13 | `CodingTheory.rs_lambda_large_prime_ghsz02` | ⏳ | Bound `Ω(p^{p^α·β/2})` — my Lean writes `(p : ℝ) ^ ((p : ℝ) ^ α * β / 2)`. Paper's `Ω(...)` glossed over; check whether to add a constant factor. |
| T3.14 | `CodingTheory.rs_lambda_high_rate_jh01` | ⏳ | Paper: `q ≡ 1 (mod j+1)`. My Lean: `qs i % (j + 1) = 1`. Matches. |
| T3.4 | `CodingTheory.subspaceDesign_list_decoding_cz25` | ⏳ | Paper τ argument is `1/η`; my `τ (Nat.floor (1/η))` floors. Paper likely uses real-valued τ; check whether `Nat.floor` distortion matters. |
| C3.5 | `CodingTheory.frs_list_decoding_capacity_cz25` | ⏳ | Uses `closeCodewordsRel (frsCode ...) y δ` and `.ncard`. Verify against `Lambda_at`. Should use `Lambda_at` for consistency. |

### §4 — Correlated Agreement

#### [LineDecoding.lean](ArkLib/Data/CodingTheory/LineDecoding.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| D4.20 | `CodingTheory.LineDecodable` | ⏳ | Function `U : F → ι → A` with side condition `∀ γ, U γ ∈ C` vs paper's `U : F → C`. Equivalent; document the choice. |
| T4.21 | `CodingTheory.lineDecodable_imp_epsMCA_le` | ⏳ | Argument `(Fintype.card ι : ℝ≥0) + 1` matches paper's `n + 1`. Confirm ENNReal cast at end. |

#### [ProximityGap/CapacityBounds.lean](ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| T4.11.1 | `CodingTheory.linear_epsMCA_1_5_johnson_gkl24` | 🔧 | **Added `η < δ_min` hypothesis** so `1 − δ_min + η < 1` and the denominator `∛x − √x` is strictly positive (since for `x < 1`, `∛x > √x`). Docstring spells out the implicit regime. |
| T4.11.2 | `CodingTheory.linear_epsCA_1_5_johnson_bgks20` | 🔧 | **Added `η < δ_min` for hypothesis-parity with Item 1** (paper presents both under one regime statement). The RHS `2 / (η²|F|)` doesn't need it but matching keeps the API symmetric. |
| T4.9.2 | `CodingTheory.rs_epsCA_bchks25_item2` | ⏳ | Hypothesis `δ_fld ≥ δ_min/3` written as `... / 3 ≤ δ_fld`; confirm precedence. Also: `1 - ρ - 2·δ_fld` can be negative; max-of-two-bounds means negative one is dominated, but `ENNReal.ofReal` of negative truncates to 0 — verify the max still works through the wrap. |
| R4.10 | `CodingTheory.rs_epsCA_small_loss_r4_10` | ⏳ | Same precedence concerns as T4.9.2. Also: paper's `γ ∈ (0, 1)` is on `γ` as the slack `δ_int − δ_fld = γ/n`. Confirm I'm using `γ` not `γ/n` as the bound parameter. |
| T4.12 | `CodingTheory.rs_epsMCA_johnson_range_bchks25` | ⏳ | Heavy formula with ⌈⌉, √, ^{3/2}. Verify all `Real.rpow` vs `HPow.hPow` are correct. `m := max ⌈...⌉ 3` uses `Int.ceil`-returning-ℤ; my code does `max ⌈...⌉ 3` with `3 : ℝ` — types may mismatch. |
| T4.13 | `CodingTheory.subspaceDesign_epsMCA_gg25` | ⏳ | τ profile assumed at `t + 1`; verify against paper's `r = t + 1` substitution. |
| T4.14 | `CodingTheory.frs_epsMCA_capacity_gg25` | ⏳ | Existential `∃ C, C = frsCode ∧ ε_mca ≤ ...`. Could be simpler as `epsMCA (frsCode ...) ... ≤ ...` directly. Refactor candidate. |
| T4.16 | `CodingTheory.rs_epsCA_lower_capacity_bchks25_kk25` | ⏳ | "Power-of-two `n`" condition not stated as a hypothesis; paper requires it. Add `n.IsPowerOfTwo` clause. Also "|F| = poly(n)" deferred to docstring. |
| T4.17 | `CodingTheory.rs_epsCA_breakdown_cs25` | ⏳ | `qEntropy q δ - δ` can be negative; sqrt of negative via `Real.rpow ((1:ℝ)/2)` returns 0 (Real.rpow of negative is 0 for non-integer exponents). Check paper's regime ensures positivity. |
| T4.18 | `CodingTheory.rs_epsCA_johnson_jump_bchks25` | ⏳ | `(Fintype.card ι : ℝ) = (Fintype.card FC : ℝ) ^ ((1 + ε) / 2)` — exact equality on reals is brittle. Paper says `n = |F|^{(1+ε)/2}` but only meaningfully when RHS is a natural number; cast issue. Maybe `≤` + `≥` instead. |
| L4.19 | `CodingTheory.linear_epsCA_ge_sampling_dg25` | ⏳ | `(δ' : ENNReal) = ⨆ u, δᵣ(u, ↑C)` — supremum over `ι → F` of a relative-distance-to-code. ENNReal-valued. Verify `δᵣ(u, C) : ENNReal` (not `ℚ≥0`) per the existing API. |

### §5 — Connections

#### [Connections.lean](ArkLib/Data/CodingTheory/Connections.lean)

| ID | Lean name | Status | Known issues / things to check |
| --- | --- | --- | --- |
| T5.1 | `CodingTheory.linear_listSize_to_epsMCA_gcxk25` | 🔧 | **Added `η ≤ δ` hypothesis** so `1 − δ + η ≤ 1` and the sqrt-proximity radius stays in `[0, 1]`. Docstring spells out the implicit requirement. |
| T5.2 | `CodingTheory.rs_epsCA_small_implies_lambda_lt_F_bchks25` | ⏳ | `(δ + 2 / Fintype.card ι).toNNReal` — when `δ < 1 - ρ` and `n ≥ 1`, the sum is positive so `toNNReal` doesn't truncate. ✓ |
| T5.3 | `CodingTheory.rs_epsCA_implies_lambda_extended_cs25` | ⚠ | RHS `(ENNReal.ofReal (... * ε_ca.toReal)).toNNReal` is doubly wrapped — ENNReal then NNReal then ENNReal. Simplify. Also: `⌈ |F|/(1-η) · ε_ca ⌉` in paper is an integer ceiling; my version uses `ENNReal.ofReal` of a real, losing the ceiling. Either use `Nat.ceil` or document the slack. |
| T5.4 | `CodingTheory.rs_epsCA_separation_bgks20` | ⏳ | `Fintype.card F = Fintype.card ι` plus injectivity of `domain` makes it a bijection by pigeonhole. Paper's "evaluation domain is the entire `F`" — confirm we want this stronger than `domain : ι ↪ F` with type-cardinality match. |

## 2. Integration review (per axis)

Each axis below is a sweep across all files committed in this session.

### 2a. Types and operator conventions

| Concern | Status | Files affected | Notes |
| --- | --- | --- | --- |
| Distance return type: `ℚ≥0` vs `ℝ≥0` vs `ℝ` | ⏳ | `ABF26Prelims.lean` (`restrictedRelHammingDist : ℝ≥0`); `Basic/RelativeDistance.lean` (`relHammingDist : ℚ≥0`). | Pick one — likely `ℚ≥0` to align with existing `relHammingDist`, or migrate everything to `ℝ≥0`. |
| Probability bounds: `ENNReal` vs `ℝ≥0` | ⏳ | All ε-bounds files. | `ENNReal` is the established convention in `EpsilonErrors.lean`; new files mostly comply. Spot-check. |
| `ENNReal.ofReal` vs `(x : ENNReal)` direct cast | ⏳ | `CapacityBounds.lean`, `ListDecodingBounds.lean`, `Connections.lean`. | Use `ENNReal.ofReal` only when the source is genuinely `ℝ` (possibly negative); use cast when source is `ℝ≥0` or `ℕ`. |
| Nat subtraction silently truncating | ⚠ | `linear_lambda_ge_elias_volume_eli57` (L3.7), `linear_C_le_generalized_singleton_st20` (T3.9), possibly T4.11.x denominators. | Cast to ℤ or ℝ before subtracting; or add positivity hypothesis. |
| `Real.rpow` vs `HPow.hPow` for non-integer exponents | ⏳ | Anywhere `^ ((1 : ℝ) / 2)` or `^ ((1 : ℝ) / 3)` appears. | `Real.rpow` is what `^ : ℝ → ℝ → ℝ` desugars to via the `Monoid.npow`/`HPow` chain. Verify Lean isn't picking up `^ : ℝ → ℕ → ℝ` accidentally. |
| `.toNNReal` truncation of negative reals | ⚠ | T5.1, T4.16, T4.17, T4.18 bound expressions. | Each occurrence: confirm hypotheses ensure non-negativity, or document the truncation as intentional. |

### 2b. Existing-vs-new definitions

| New name | Existing peer | Status | Action |
| --- | --- | --- | --- |
| `CodingTheory.restrictedRelHammingDist` | `relHammingDist`, `relDistFromCode` in `Basic/RelativeDistance.lean` | ⏳ | Consider relocating to `Basic/RelativeDistance.lean`; add a one-line lemma `restrictedRelHammingDist Finset.univ f g = relHammingDist f g`. |
| `CodingTheory.hammingBallVolume` | `hammingBall : Set` in `ListDecodability.lean` | ⏳ | Add bridge `hammingBallVolume q δ n = (hammingBall y ⌊δ·n⌋).toFinset.card`. Useful for L3.7's eventual proof anyway. |
| `CodingTheory.qEntropy` | `Real.negMulLog`, Mathlib's binary-entropy lemmas | ⏳ | Confirm Mathlib has no q-ary entropy. If so, keep ours; if it grows one, alias. |
| `JohnsonBound.Jcap` vs existing `J` (= paper's `J_q`) | `JohnsonBound.J` | ⏳ | Naming clash is documented in docstring. Option A: keep both with prominent docstring. Option B: rename existing `J` → `Jq`, then `J := Jcap` matches paper. Option B is a breaking change; defer decision. |
| `CodingTheory.ExtensionFieldPresentation` | `Algebra B F`, `Module.Finite`, `Basis` (Mathlib) | ⏳ | Verify whether we can derive `(ψ, e, φ)` from `Algebra B F + FiniteDimensional B F + chooseBasis`. If yes, refactor to a thin wrapper, halving the structure size. |
| `CodingTheory.IsSubspaceDesign` formulation | `LinearMap.proj` vs comprehension | ⚠ | Add `IsSubspaceDesign_iff_comprehension` equivalence. Pick canonical form based on which is easier to use in T3.4 / T4.13 proofs. |
| `ReedSolomon.Interleaved.irsCode` | `interleavedCodeSet`, `^⋈` notation | ⏳ | One-liner; consider `abbrev` instead of `noncomputable def`. Or drop entirely and inline at call sites if not pulling weight. |
| `ReedSolomon.Folded.frsCode` | `ReedSolomon.code` using `Polynomial.degreeLT` | ⚠ | My version uses `p.degree < k`; align to `Polynomial.degreeLT F k.map evalOnPoints`-style for consistency. |
| `CodingTheory.extensionCode` | encoder-image vs set-of-codewords | ⚠ | Add equivalence lemma so callers can use either view interchangeably. |
| `CodingTheory.Lambda` (extended earlier in session) | `closeCodewordsRel`, `listDecodable` | ✅ | Already integrated; no action. |

### 2c. Namespace and file layout

| Concern | Status | Action |
| --- | --- | --- |
| `CodingTheory.*` vs `ProximityGap.*` vs `ABF26.*` | ⏳ | Most new statements live in `CodingTheory.*`; ε-functions in `ProximityGap.*`. Document the split in `ABF26_PLAN.md` §6 D2 follow-up. |
| `ABF26Prelims.lean` filename prefix | ⏳ | "ABF26" prefix is paper-ledger naming; topical names like `Entropy.lean`, `HammingBallVolume.lean` would be more discoverable. Defer rename until polish complete. |
| `ABF26CodeFamilies.lean` vs split per family | ⏳ | Three families (IRS, FRS, Subspace) in one file. Consider splitting to `CodeFamilies/Interleaved.lean`, `CodeFamilies/Folded.lean`, `CodeFamilies/Subspace.lean` if the file grows beyond ~300 lines. |
| `Connections.lean`, `LineDecoding.lean`, `ExtensionCodes.lean` | ⏳ | 1–4 statements each; each is topically coherent. Keep separate. |

### 2d. Notation alignment

| Concern | Status | Action |
| --- | --- | --- |
| Paper-style `RS[F, L, k]`, `IRS[F, L, k, s]`, `FRS[F, L, k, s, ω]` | ⏳ | Deferred per plan D2 (descriptive names). Reconsider once polish pass is otherwise done — concrete call sites now exist. |
| `^⋈` for interleaved code usage | ⏳ | Use it everywhere `interleavedCodeSet` appears, or nowhere. Standardise per-file. |
| `Δ_T(f, g)`, `Λ(C, δ, f)`, `δ_min` paper notation | ⏳ | Decide all-or-nothing at the end of polish, when statement set is stable. |

### 2e. Tagged-sorry hygiene

| Concern | Status | Action |
| --- | --- | --- |
| Comment-line style for tagged sorries | ⏳ | Pick one: `-- ABF26-T4.11 Item 1; external admit [GKL24 Thm 3].` is the current shape. Verify all 40+ sorries conform; rewrite any outliers. |
| `ABF26-X.Y` tag matches paper ID and audit row | ⏳ | Sweep every tagged sorry; cross-check against [audit doc](docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md). |
| Paper-page reference in docstring | ⏳ | Most statements cite paper section but not page. Add page numbers to docstrings for fast paper lookup. |

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
7. **A7.** Align `frsCode` (D2.15) to `Polynomial.degreeLT` style.

After each fix: `./scripts/validate.sh` must pass.

### Pass B: Integration of definitions

Apply 2b actions in dependency order:

1. **B1.** Add `restrictedRelHammingDist Finset.univ f g = relHammingDist f g` bridge.
2. **B2.** Add `hammingBallVolume_eq_ncard_hammingBall` bridge.
3. **B3.** Add `IsSubspaceDesign_iff_comprehension` (settles 2b row).
4. **B4.** Add `extensionCode_eq_encoder_image` bridge.
5. **B5.** (Optional, deferred) Refactor `ExtensionFieldPresentation` to thin Mathlib wrapper.

### Pass C: Operator and type convention sweep

Apply 2a actions:

1. **C1.** Standardise `.toNNReal` usage: every occurrence either provably non-negative or commented.
2. **C2.** Sweep `^ : ℝ → ℝ` usages for `Real.rpow` consistency.
3. **C3.** Standardise `ENNReal.ofReal` vs ENNReal cast choice (document rule in file headers).

### Pass D: Notation, namespace, hygiene

Apply 2c–2e actions. Lowest priority — leave until A–C stable.

1. **D1.** Sweep tagged-sorry comments for uniform style.
2. **D2.** Add paper-page references to docstrings.
3. **D3.** (Optional) Topical filename renames once content stable.
4. **D4.** (Optional) Paper-style notation decision.

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
