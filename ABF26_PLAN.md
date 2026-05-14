# ABF26 Implementation Plan

Working plan for bringing every formal item from `ABF26.pdf` — *Open Problems in
List Decoding and Correlated Agreement* (Arnon, Boneh, Fenzi; April 8, 2026) —
into ArkLib in a complete, correct, and incrementally non-breaking way.

This file is operational scaffolding. Once the work is complete, useful
implementation notes will be migrated into `docs/wiki/` (likely
`knowledge-base.md` and the existing paper-audit page) and this file will be
deleted.

Companion documents:

- `docs/wiki/paper-audit-open-problems-list-decoding-and-correlated-agreement.md` —
  the existing per-item audit. This plan **extends** it; it does not replace
  it. Where this plan and the audit disagree, the audit is the snapshot and
  this plan is the intent. The plan must keep the audit in lockstep — every
  item-level PR updates the corresponding audit row.
- `ABF26.pdf` and `paper.pdf` in the working tree appear to be the same April 8,
  2026 paper. References to `paper.pdf` in the audit doc are equivalent to
  `ABF26.pdf` here.

---

## 0. Goals and non-goals

### Goals

1. Every named formal item in `ABF26.pdf` is either:
   - present in ArkLib with a statement matching the paper, OR
   - present with a documented intentional difference and an adapter
     lemma/definition bridging the two shapes, OR
   - explicitly deferred with a recorded reason.
2. Changes are incremental and non-breaking. Each PR keeps `./scripts/validate.sh`
   green and does not introduce new `sorry`s except behind items flagged in
   the conjecture/external-results ledger (§6).
3. New work integrates with existing ArkLib structure rather than forking it.
4. Section-level theorems use the numeric ε_pg / ε_ca / ε_mca interface,
   matching the paper, while keeping the existing predicate-style APIs as a
   compatibility layer until callers migrate.
5. Every paper item has a tracked entry in §7 below. No item is "implicitly
   handled" — items either have an entry, a deferred-explicit entry, or a
   skipped-with-reason entry.

### Non-goals (initial pass)

- §6 toy problem and attacks. Tracked in §7 with `deferred` status.
- §7 of the paper ("Related problems and promising directions") — survey
  content only, no formal items.
- §6.3 concrete numerical parametrizations (Tables 2–5) — only the symbolic
  protocol soundness/argument-size formulas need formalizing.

---

## 1. Approach overview

1. **Phase 0** — Refresh the audit row-by-row against current `HEAD`.
2. **Phase 1** — Migrate the ε-error interface. Linchpin for §4 and §5.
3. **Phase 2** — Close existing sorries on already-present items.
4. **Phase 3** — Add the missing code families: FRS, UM, subspace-design,
   extension.
5. **Phase 4** — §3 list-decoding theorems.
6. **Phase 5** — §4 CA/MCA in the unique-decoding regime.
7. **Phase 6** — Line-decoding and capacity-regime CA/MCA.
8. **Phase 7** — §5 connections.
9. **Phase 8 (deferred)** — §6 toy problem and attacks.
10. **Phase 9** — Misc preliminaries (q-entropy, ball volume, restricted
    Hamming, paper-style notation aliases).

---

## 2. Branch and PR strategy

- **Single branch (user-confirmed 2026-05-14)**: all phases of this effort
  accumulate on `feat/abf26-plan`. The "Phase N PR M" numbering in §8 below
  is now a commit-level breakdown rather than a per-PR branch breakdown;
  each numbered work package is one logical commit (or a small cluster) on
  this branch. The original plan called for small PRs to `main` and a
  separate long-lived `feat/abf26-eps-interface` branch for Phase 1; that
  is overridden in favour of a single accumulating branch.
- **Commit hygiene**: each commit message references the `ABF26-*` item
  IDs it closes and uses the conventional-commits prefixes the repo
  already follows (`feat(...)`, `fix(...)`, `docs(...)`, etc.).
- **Sorry hygiene**: new `sorry`s must (a) be listed in §6 of this plan
  and (b) carry a `-- ABF26 <Item-ID>: external/conjectural, see <source>`
  comment.
- **Validation gate**: every commit that touches Lean runs
  `./scripts/validate.sh`; ε-interface commits also run
  `./scripts/validate.sh --docs`.
- **Audit doc gate**: every item-closing commit updates the corresponding
  row in `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`
  in the same commit.

---

## 3. Phase ordering and gating

The phase ordering exists to control PR dependencies. The granular per-item
ledger in §7 is the source of truth for *what* lands; this section is the
source of truth for *when*.

| Phase | Theme | Hard prereqs | Items |
| --- | --- | --- | --- |
| 0 | Audit refresh | — | (audit doc only) |
| 1 | ε-error interface | Phase 0 | D4.1, D4.3, R4.2, R4.4, F4.5, L4.6, L4.7, plus Lambda function from D2.8 |
| 2 | Close existing sorries | — (independent) | none new |
| 3 | Code families | Phase 0 | D2.13, D2.14, D2.15, D2.16, L2.17, T2.18, D2.19, D2.20, L2.21, DA.6, DA.7 |
| 4 | §3 list decoding | Phases 1, 3 | D3.1, T3.2, C3.3, T3.4, C3.5, T3.6, L3.7, C3.8, T3.9, T3.10–T3.15, plus L2.10 |
| 5 | §4 unique decoding | Phases 1, 2, 3, 4 | T4.8, T4.9.1, T4.9.2, R4.10 |
| 6 | §4 capacity regime + line-decoding | Phases 1, 3, 5 | D4.20, T4.21, T4.11, T4.12, T4.13, T4.14, T4.15, T4.16, T4.17, T4.18, L4.19 |
| 7 | §5 connections | Phases 4, 5, 6 | T5.1, T5.2, T5.3, T5.4 |
| 8 (deferred) | §6 toy problem | OracleReduction security sorries cleared | D6.1, C6.2, D6.3, D6.4, L6.5, L6.6, R6.7, L6.8, C6.9, L6.10, D6.11, L6.12, L6.13, R6.14, B.1 |
| 9 | Misc preliminaries | Phase 0 | L2.1, D2.2, D2.3, D2.4, D2.5, D2.7, D2.9, plus appendix notation aliases DA.1, RA.2, DA.3, DA.5. (D2.8 is owned by Phase 1 and DA.4 is already `present`, so neither is in Phase 9.) |

---

## 4. Risk register

| ID | Risk | Mitigation |
| -- | ---- | ---------- |
| R1 | ε-interface migration breaks downstream WHIR/STIR/BatchedFri proofs | Phase 1 is a long-lived branch with bridging lemmas (`δ_ε_*_iff_eps*`). Downstream callers keep compiling against the predicate API until they migrate. |
| R2 | `ProximityGap/Basic.lean` exceeds the 1500-line file cap | Split into `EpsilonErrors.lean` proactively. |
| R3 | Subspace-design definition does not generalize cleanly across FRS, UM, and unknown future families | Define `IsSubspaceDesign` as a predicate over `ModuleCode`, not over a concrete ADT. |
| R4 | Several §3/§4 theorems are external results we cannot reasonably reprove in-tree | Conjecture/external-result ledger (§6). Tagged `sorry`s only. |
| R5 | Recent FFT/CompPoly refactors invalidate the existing audit | Phase 0 explicitly re-runs the audit before code lands. |
| R6 | Notation churn: `Λ`, `δ_min`, `δ_fld`, `δ_int`, `ε_mca`, `ρ`, `J` vs ArkLib's existing `‖C‖₀`, `relUDR`, `relMinDist` | Decide notation per item in §7 under "Open questions". Avoid multiple notations for one concept; use `scoped notation` so paper symbols only appear inside `ABF26` namespace. |
| R7 | `ABF26.pdf` may receive future revisions before work is complete | Capture SHA-256 of the PDF in audit doc header. |
| R8 | Cross-paper notational drift (e.g. WHIR's `Gen`, BCIKS20's `[BCIKS20]` notation) | Each PR keeps the paper-of-origin citation in the file docstring; the audit doc lists the canonical name we use across papers. |
| R9 | A "missing" item turns out to be present under a name we did not search for | Phase 0 grep must check for `Λ`, `δ_min`, `J_q`, `H_q`, `Vol_q`, `frs`, `multiplicity`, `subspaceDesign`, `extension`, plus paper-cite citations `[BKR06]`, `[GHSZ02]`, etc. |
| R10 | One item's PR introduces an interface that conflicts with a later item's needs | Per-item "Reverse dependencies" field in §7 surfaces this. Phase 1 reviewer must check that the ε-error signatures satisfy all reverse-dep items. |

---

## 5. Acceptance criteria

The overall effort is "done" when:

1. The audit doc's status column shows `present` for every paper item not
   listed in the conjecture/external-results ledger.
2. No file in `Data/CodingTheory/`, `ProofSystem/Whir/`,
   `ProofSystem/Stir/`, or `ProofSystem/BatchedFri/` has a `sorry` that
   is not tagged with an `ABF26-*` conjecture/external-result comment or
   an already-known unrelated `sorry`.
3. `./scripts/validate.sh` and `./scripts/validate.sh --lint` are green on
   `main`.
4. The blueprint cross-references the new declarations.
5. This plan file is migrated into `docs/wiki/` and deleted from root.

---

## 6. Open decisions log and conjecture/external-result ledger

### Open decisions

| ID | Decision | Status | Notes |
| -- | -------- | ------ | ----- |
| D1 | ε-error values: `ℝ≥0` or `ENNReal`? | **decided 2026-05-14**: `ENNReal` for ε-return values (to match `Pr_{...}[...]`); `ℝ≥0` for `δ_fld`/`δ_int` inputs (to match the existing `δ_ε_*` predicate API in `Basic.lean`); `ℕ∞` for `Lambda`. | Locked in by the D2.8/D4.1/D4.3 commits. |
| D2 | Paper `Λ(C,δ)` notation: `Λ` macro or descriptive Lean name? | **decided 2026-05-14**: descriptive Lean names (`Lambda_at`, `Lambda`, `epsCA`, `epsMCA`, etc.) only; no `Λ`/`ε` macros for now | Scoped notation can be added later in Phase 9 if useful, but the descriptive names are the canonical identifiers. |
| D3 | Subspace-design: `class` or `Prop` predicate? | pending; recommend `Prop` predicate | Phase 3. |
| D4 | External-result theorems: `sorry` or `axiom`? | decided: `sorry` with tagged comment | Axioms inflate `#print axioms`. |
| D5 | `paper.pdf` vs `ABF26.pdf`: identical? | decided: yes | Confirmed against audit content. |
| D6 | `Smooth` typeclass placement | decided: keep on `ι ↪ F` | Existing WHIR usage non-trivial. |
| D7 | Where do paper-style notation aliases live? | pending; recommend `ArkLib/Data/CodingTheory/ABF26Notation.lean` | Phase 9. |
| D8 | Computable vs noncomputable defaults for ε's? | **decided 2026-05-14**: `noncomputable def` for `Lambda`, `epsCA`, `epsCA'`, `epsMCA`; `def` for `Prop`-returning helpers (`pairJointAgreesOn`, `mcaEvent`) | Matches `distFromCode` and predicate-style conventions. |
| D9 | One branch for the whole effort vs many PRs to `main`? | **decided 2026-05-14**: single branch `feat/abf26-plan` | User preference. Each "PR" in §8 becomes a commit (or small cluster) on this branch. |
| D10 | `epsMCA` / `mcaEvent` interleaving width: `Fin 2` only, or general `Fin ℓ`? | **decided 2026-05-14**: `Fin 2` only for the initial pass | Paper Section 4 only uses lines (the affine-line case, `ℓ = 2`). F4.5, L4.6, and L4.7 do not require higher `ℓ`. Generalizing to `Fin ℓ` is tracked as a future extension, not in Phase 1. |
| D11 | Linter suppression idiom for `unusedFintypeInType`/`unusedDecidableInType`/`unusedSectionVars` | **decided 2026-05-14**: file-level `set_option` block right after imports | Matches `ReedSolomon/FftDomain.lean` style; chosen over per-declaration `... in` because the section variables are needed proof-wide. |

### Conjecture / external-result ledger

Items the paper itself states without full proof, or whose proof is out of
ArkLib's scope. These are the only `sorry`s the plan permits.

| ID | Source | Phase | Status |
| -- | ------ | ----- | ------ |
| `ABF26-T3.6` | AGL24 | 4 | external; admit |
| `ABF26-T3.10` | BDG24/AGL23 | 4 | external; admit |
| `ABF26-T3.11` | GLMRSW22 | 4 | external; admit |
| `ABF26-T3.12` | BKR06 | 4 | external; admit |
| `ABF26-T3.13` | GHSZ02 | 4 | external; admit |
| `ABF26-T3.14` | JH01 | 4 | external; admit |
| `ABF26-T3.15` | CW07 | 4 | external; admit |
| `ABF26-T4.12` | BCHKS25 Thm 4.6 | 6 | external; admit |
| `ABF26-T4.13` | GG25 Cor 4.9 | 6 | external; admit |
| `ABF26-T4.14` | GG25 Cor 4.10 | 6 | external; admit |
| `ABF26-T4.15` | GG25 Thm 5.15 | 6 | external; admit |
| `ABF26-T4.16` | BCHKS25/KK25 | 6 | external; admit |
| `ABF26-T4.17` | CS25 Cor 1 | 6 | external; admit |
| `ABF26-T4.18` | BCHKS25 Cor 1.7 | 6 | external; admit |
| `ABF26-T5.1` | GCXK25 Thm 3 | 7 | external; admit |
| `ABF26-T5.2` | BCHKS25 Thm 1.9 | 7 | external; admit |
| `ABF26-T5.3` | CS25 Thm 2 | 7 | external; admit |
| `ABF26-T5.4` | BGKS20 Lem 3.3 | 7 | external; admit |
| `mca_johnson_bound_CONJECTURE` | existing | 1 | already conjectural |
| `mca_capacity_bound_CONJECTURE` | existing | 1 | already conjectural |

`sorry`s in this ledger must carry a Lean comment of the form
`-- ABF26 <Item-ID>: external result from <source>`.

---

## 7. Per-item ledger

The remainder of this file is the per-item ledger. One subsection per paper
item. Status legend:

- `missing` — no formalization found.
- `present` — close match present in ArkLib.
- `present-but-different` — underlying concept present, shape differs.
- `present-but-incomplete` — declaration exists but contains `sorry`.
- `deferred` — out of initial scope, tracked for follow-up.

Sub-task numbering is intentionally fine-grained. Each numbered sub-task is
expected to map to at most one commit; many will map to a single line in a
diff.

### Section 2 — Preliminaries

#### ABF26-L2.1 — Polynomial identity lemma

- **Paper location**: §2 page 6, Lemma 2.1.
- **Statement**: `∀ p̂ ∈ F<d[X₁..Xₘ]` nonzero, `Pr_{v ← F^m}[p̂(v)=0] ≤ m(d-1)/|F|`.
- **Status**: present-but-different.
- **Existing in ArkLib**:
  - `prob_schwartz_zippel_mv_polynomial` in `ArkLib/Data/Probability/Instances.lean`.
  - `schwartz_zippel_of_fintype` in `ArkLib/Data/MvPolynomial/Interpolation.lean`.
- **Target Lean name**: `ABF26.polyIdentity_le` (alias wrapping the existing Schwartz-Zippel result with the paper's `m(d-1)/|F|` shape).
- **Target file**: `ArkLib/Data/MvPolynomial/Interpolation.lean` (append alias) or a new `ArkLib/Data/CodingTheory/ABF26Notation.lean`.
- **Direct dependencies (paper)**: none.
- **Direct dependencies (ArkLib infra)**: existing Schwartz-Zippel lemma.
- **Reverse dependencies**: L6.6, L6.8 (both deferred), and informally throughout §6.
- **Target PR**: Phase 9 PR 1.
- **Sub-tasks**:
  1. Confirm `prob_schwartz_zippel_mv_polynomial` produces the bound `m(d-1)/|F|`. If it does, alias it. If it produces `d/|F|` (single-variable form), prove the multivariate bound from it.
  2. State `theorem ABF26.polyIdentity_le ...` matching the paper's exact hypothesis (degree `< d` per variable, nonzero polynomial).
  3. Add docstring `/-- **ABF26 Lemma 2.1.** Polynomial identity lemma. -/`.
  4. Update audit doc row.
- **Acceptance**: stated theorem compiles, no new `sorry`.
- **Open questions**: does ArkLib already enforce the per-variable degree bound `F<d[X₁..Xₘ]`, or only total degree?

#### ABF26-D2.2 — q-entropy function `H_q`

- **Paper location**: §2.2 page 7, Definition 2.2.
- **Statement**: `H_q(x) = x·log_q(q-1) − x·log_q(x) − (1−x)·log_q(1−x)`.
- **Status**: missing.
- **Existing in ArkLib**: none.
- **Target Lean name**: `CodingTheory.qEntropy (q : ℕ) (x : ℝ) : ℝ` with `H_q` notation in scope `ABF26`.
- **Target file**: new `ArkLib/Data/CodingTheory/Prelims/Entropy.lean`.
- **Direct dependencies (paper)**: none.
- **Direct dependencies (ArkLib infra)**: `Real.log`, `Real.logb`.
- **Reverse dependencies**: C3.8, T3.11, T4.17.
- **Target PR**: Phase 9 PR 1.
- **Sub-tasks**:
  1. Create file with imports `Mathlib.Analysis.SpecialFunctions.Log.Basic`.
  2. Define `noncomputable def qEntropy (q : ℕ) (x : ℝ) : ℝ := ...`.
  3. Define `H_S` alias: `noncomputable def setEntropy (S : Type*) [Fintype S] (x : ℝ) : ℝ := qEntropy (Fintype.card S) x`.
  4. Prove sanity lemmas: `qEntropy_zero`, `qEntropy_one`, monotonicity on `[0, 1 - 1/q]`.
  5. Add `scoped notation "H_" => qEntropy` inside `ABF26` namespace.
  6. Update audit doc row.
- **Acceptance**: `qEntropy 2 0.5 = 1` proved as an example (binary entropy of 1/2).
- **Open questions**: does `H_q` get re-used elsewhere or only inside ABF26? If only ABF26, scope notation tightly.

#### ABF26-D2.3 — Restricted Hamming distance `Δ_T(f,g)`

- **Paper location**: §2.2 page 7, Definition 2.3.
- **Statement**: `Δ_T(f,g) = Pr_{i ← T}[f(i) ≠ g(i)]`.
- **Status**: present-but-different.
- **Existing in ArkLib**: `Δ₀`, `δᵣ`, `distFromCode`, `relDistFromCode` in `ArkLib/Data/CodingTheory/Basic/Distance.lean`. None restrict to a subset `T`.
- **Target Lean name**: `Code.restrictedRelHammingDist (T : Finset ι) (f g : ι → F) : ℝ≥0`.
- **Target file**: `ArkLib/Data/CodingTheory/Basic/Distance.lean` (append).
- **Direct dependencies (paper)**: none.
- **Direct dependencies (ArkLib infra)**: existing `relDistFromCode` patterns.
- **Reverse dependencies**: D4.1 (CA uses `Δ_S` over a set), D4.20 (line-decoding uses `Δ_S`), L6.6, L6.8 (deferred).
- **Target PR**: Phase 9 PR 2.
- **Sub-tasks**:
  1. Define `restrictedRelHammingDist T f g := (Finset.filter (fun i => f i ≠ g i) T).card / T.card`.
  2. Prove `restrictedRelHammingDist Finset.univ f g = relDistFromCode_pairwise f g`.
  3. Define `restrictedRelHammingDist_set T f C : ℝ≥0 := min over c ∈ C`.
  4. Prove monotonicity in `T`: `T₁ ⊆ T₂ → ...`.
  5. Add notation `notation "Δ[" T "](" f ", " g ")" => restrictedRelHammingDist T f g`.
  6. Update audit doc row.
- **Acceptance**: examples compile.
- **Open questions**: does ArkLib already have a `Δ₀` indexed-by-Finset variant? Grep before defining.

#### ABF26-D2.4 — Hamming-ball volume `Vol_q(δ, n)`

- **Paper location**: §2.2 page 8, Definition 2.4.
- **Statement**: `Vol_q(δ, n) = ∑_{i=0}^{⌊δn⌋} binom(n,i)·(q-1)^i`.
- **Status**: present-but-different.
- **Existing in ArkLib**: `hammingBall`, `relHammingBall` as sets in `ArkLib/Data/CodingTheory/ListDecodability.lean`. No cardinality function.
- **Target Lean name**: `CodingTheory.hammingBallVolume (q : ℕ) (δ : ℝ≥0) (n : ℕ) : ℕ`.
- **Target file**: new `ArkLib/Data/CodingTheory/Prelims/Volume.lean`.
- **Direct dependencies (paper)**: D2.3 (uses Hamming distance).
- **Direct dependencies (ArkLib infra)**: `Nat.choose`, existing `hammingBall`.
- **Reverse dependencies**: L3.7, C3.8.
- **Target PR**: Phase 9 PR 1.
- **Sub-tasks**:
  1. Create file.
  2. Define `hammingBallVolume q δ n := ∑ i ∈ Finset.range (⌊δ * n⌋₊ + 1), Nat.choose n i * (q - 1)^i`.
  3. Prove `hammingBallVolume q δ n = (hammingBall y (⌊δ * n⌋₊)).toFinset.card` for any `y : Fin n → Fin q`. This is the cardinality bridge.
  4. Prove `Vol_q(δ, n) ≈ q^(n(ρ-1+H_q(δ)))` lower bound (paper alludes to MS77).
  5. Update audit doc.
- **Acceptance**: cardinality bridge proved without `sorry`.
- **Open questions**: which underlying representation of the Hamming ball is ArkLib's canonical one (Σ^n or `Fin n → Σ`)?

#### ABF26-D2.5 — ECC with `δ_min`, rate `ρ`

- **Paper location**: §2.3 page 8, Definition 2.5.
- **Statement**: `C ⊆ Σ^n`, `δ_min(C) = min_{f,g ∈ C} Δ(f,g)`, `ρ(C) = log_|Σ| |C| / n`.
- **Status**: present-but-different.
- **Existing in ArkLib**: `Code.dist`, `Code.minDist`, `LinearCode.rate` in `ArkLib/Data/CodingTheory/Basic/`.
- **Target Lean name**: keep existing names; add `scoped notation "δ_min" => Code.relMinDist` and `scoped notation "ρ" => LinearCode.rate` inside `ABF26` namespace.
- **Target file**: notation lives in `ArkLib/Data/CodingTheory/ABF26Notation.lean` (new).
- **Direct dependencies (paper)**: D2.3.
- **Direct dependencies (ArkLib infra)**: existing.
- **Reverse dependencies**: pervasive.
- **Target PR**: Phase 9 PR 2.
- **Sub-tasks**:
  1. Verify ArkLib has `relMinDist` (relative minimum distance). If not, define it.
  2. Add the notation file.
  3. Update audit doc.
- **Acceptance**: imports clean, no shadowing of existing notation outside `ABF26` namespace.
- **Open questions**: does ArkLib's `LinearCode.rate` exactly match `log_|Σ| |C| / n` for non-linear codes? Likely needs a separate `Code.rate` for the general case.

#### ABF26-L2.6 — Singleton bound

- **Paper location**: §2.3 page 8, Lemma 2.6.
- **Status**: present.
- **Existing in ArkLib**: `singleton_bound`, `singleton_bound_linear` in `ArkLib/Data/CodingTheory/Basic/LinearCode.lean:107` and `:447`.
- **Target Lean name**: existing.
- **Direct dependencies (paper)**: D2.5.
- **Reverse dependencies**: C3.3, T3.9.
- **Target PR**: none — already done.
- **Sub-tasks**:
  1. Verify audit row is `present`. Done.
- **Acceptance**: no action.
- **Open questions**: should we add an explicit MDS predicate `IsMDS` equal to `ρ = 1 − δ_min + 1/n`? Recommended.

#### ABF26-D2.7 — F-additive code

- **Paper location**: §2.3 page 8, Definition 2.7.
- **Statement**: `Σ = F^s` and `C` is an F-linear subspace of `Σ^n`. If `s = 1`, "F-linear".
- **Status**: present-but-different.
- **Existing in ArkLib**: `ModuleCode`, `LinearCode` in `ArkLib/Data/CodingTheory/Basic/LinearCode.lean:157,160`.
- **Target Lean name**: `CodingTheory.IsFAdditive (F : Type*) (Σ : Type*) (s : ℕ) (C : Set (ι → Σ)) : Prop` plus the existing `ModuleCode` for the typed case.
- **Target file**: `ArkLib/Data/CodingTheory/Basic/LinearCode.lean` (append).
- **Direct dependencies (paper)**: D2.5.
- **Reverse dependencies**: D2.16, D2.19, D4.1, D4.3, and throughout §4–§6.
- **Target PR**: Phase 9 PR 2.
- **Sub-tasks**:
  1. Define `class FAdditive (F : Type*) [Field F] {Σ : Type*} (s : ℕ) (φ : Σ ≃ₗ[F] (Fin s → F)) (C : Submodule F (ι → Σ))`.
  2. Or simpler: `def IsFAdditive ... := ∃ φ : Σ ≃ₗ[F] (Fin s → F), ...`.
  3. Prove F-linear is the special case `s = 1`.
  4. Update audit doc.
- **Acceptance**: example: `ReedSolomon.code` is F-linear.
- **Open questions**: do we model `Σ = F^s` via a fixed equivalence or via a class? Recommend equivalence for cleanness.

#### ABF26-D2.8 — List around a word `Λ(C,δ,f)` and `|Λ(C,δ)|`

- **Paper location**: §2.3 page 8, Definition 2.8.
- **Statement**: `Λ(C,δ,f) = {g ∈ C : Δ(f,g) ≤ δ}` and `|Λ(C,δ)| = max_f |Λ(C,δ,f)|`.
- **Status**: ✅ present (closed by commit `7c913b3b`).
- **Existing in ArkLib**: `closeCodewordsRel`, `listDecodable`, `uniqueDecodable` in `ArkLib/Data/CodingTheory/ListDecodability.lean`.
- **Target Lean name**: `ListDecodable.Lambda_at (C : Set (ι → F)) (δ : ℝ≥0) (f : ι → F) : Set (ι → F) := closeCodewordsRel C f δ`; `ListDecodable.Lambda (C : Set (ι → F)) (δ : ℝ≥0) : ℕ∞ := ⨆ f, (Lambda_at C δ f).toFinset.card`.
- **Target file**: `ArkLib/Data/CodingTheory/ListDecodability.lean` (append).
- **Direct dependencies (paper)**: D2.3.
- **Reverse dependencies**: D2.10, all of §3, D4.3, L6.6, L6.8.
- **Target PR**: Phase 1 PR 1 (because D4.3 ε_mca uses `Lambda`).
- **Sub-tasks**:
  1. ✅ Define `Lambda_at` (commit `7c913b3b`).
  2. ✅ Define `Lambda` as a `ℕ∞`-valued max (commit `7c913b3b`).
  3. ✅ Prove monotonicity `δ₁ ≤ δ₂ → Lambda C δ₁ ≤ Lambda C δ₂` (`Lambda_mono`).
  4. ✅ Prove `Lambda C δ ≤ (C.ncard : ℕ∞)` for finite `C` (`Lambda_le_ncard`).
  5. N/A — `ℕ∞ ≥ 0` is automatic; no separate lemma needed.
  6. Skipped per decision D2 (descriptive names only, no `Λ` macro).
  7. ✅ Update audit doc.
- **Acceptance**: monotonicity and bound proved. ✅ Met.
- **Open questions**: `ℕ∞` vs `ℕ` for `Lambda` — **decided `ℕ∞`** for consistency with `distFromCode`; recorded in plan §6 D1.

#### ABF26-L2.10 — Interleaved-code list-size bound

- **Paper location**: §2.3 page 9, Lemma 2.10 [GGR11].
- **Statement**: With `η := δ_min(C) - δ`, `b := ⌈δ/η⌉`, `r := ⌈log(δ_min(C)/η)⌉`:
  `|Λ(C^≡m, δ)| ≤ binom(b+r, r) · |Λ(C,δ)|^r`.
- **Status**: missing.
- **Existing in ArkLib**: none.
- **Target Lean name**: `InterleavedCode.lambda_le`.
- **Target file**: `ArkLib/Data/CodingTheory/InterleavedListSize.lean` (new) or appended to `InterleavedCode.lean` if cap allows.
- **Direct dependencies (paper)**: D2.8, D2.9.
- **Direct dependencies (ArkLib infra)**: `interleavedCodeSet`, `Lambda`.
- **Reverse dependencies**: L6.6, L6.8, §6.3 instantiations.
- **Target PR**: Phase 4 PR 2.
- **Sub-tasks**:
  1. State the theorem with `Lambda` and `interleavedCodeSet`.
  2. Prove via the GGR11 strategy (would need to read the source paper). If this becomes prohibitively large, mark as external admit and add to ledger.
  3. Add corollary `|Λ(C,δ)| ≤ |Λ(C^≡m, δ)| ≤ |Λ(C,δ)|^m` (sandwich bound mentioned right before Lemma 2.10).
  4. Update audit doc.
- **Acceptance**: theorem stated; proof or external-result tag.
- **Open questions**: include in initial scope or mark as external? Recommend attempting the proof — it is short combinatorics — but allow falling back to external admit.

#### ABF26-D2.11 — Reed-Solomon code `RS[F, L, k]`

- **Paper location**: §2.4 page 9, Definition 2.11.
- **Status**: present-but-different (uses injection `ι ↪ F` rather than literal subset `L ⊆ F`).
- **Existing in ArkLib**: `ReedSolomon.code` in `ArkLib/Data/CodingTheory/ReedSolomon.lean:44`.
- **Target Lean name**: keep existing; add `scoped notation "RS[" F ", " L ", " k "]" => ReedSolomon.code L k` in the `ABF26Notation` file.
- **Target file**: existing.
- **Direct dependencies (paper)**: D2.5.
- **Reverse dependencies**: D2.13, D2.15, DA.7, all of §3 RS-specific, all of §4 RS-specific.
- **Target PR**: Phase 9 PR 2 (notation alias).
- **Sub-tasks**:
  1. Decide whether to add a `Set F`-based wrapper. Recommend skipping — injection is strictly more general and forcing a `Finset F` wrapper is busywork.
  2. Add notation.
  3. Update audit doc.
- **Acceptance**: notation compiles.
- **Open questions**: none.

#### ABF26-D2.12 — Smooth domain

- **Paper location**: §2.4 page 9, Definition 2.12.
- **Status**: present-but-different.
- **Existing in ArkLib**: `ReedSolomon.Smooth` in `ArkLib/Data/CodingTheory/ReedSolomon.lean:571`.
- **Target Lean name**: existing.
- **Target file**: existing.
- **Direct dependencies (paper)**: none.
- **Reverse dependencies**: D2.13, D2.15, smooth-domain RS theorems throughout.
- **Target PR**: none — already done. Phase 0 verify the audit row.
- **Sub-tasks**:
  1. Verify `Smooth` matches paper: multiplicative coset of a subgroup whose order is a power of two.
  2. Update audit doc.
- **Acceptance**: no action beyond verification.
- **Open questions**: paper requires order is a power of two; ArkLib's `Smooth` also requires this (`h_card_pow2`). Aligned.

#### ABF26-D2.13 — s-interleaved Reed-Solomon `IRS[F, L, k, s]`

- **Paper location**: §2.4 page 9, Definition 2.13.
- **Statement**: `IRS[F,L,k,s] := (RS[F,L,k/s])^≡s`.
- **Status**: present-but-different (no dedicated alias).
- **Existing in ArkLib**: composition of `ReedSolomon.code` and `interleavedCodeSet`.
- **Target Lean name**: `ReedSolomon.Interleaved.irsCode`.
- **Target file**: new `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved.lean`.
- **Direct dependencies (paper)**: D2.11, D2.9.
- **Direct dependencies (ArkLib infra)**: `ReedSolomon.code`, `interleavedCodeSet`.
- **Reverse dependencies**: D2.15, D2.16 (FRS as IRS variant), DA.7, §6.3.1.
- **Target PR**: Phase 3 PR 1.
- **Sub-tasks**:
  1. Create file with imports.
  2. Define `noncomputable def irsCode (domain : ι ↪ F) (k s : ℕ) : Set (Matrix ι (Fin s) F) := (ReedSolomon.code domain (k / s))^⋈ (Fin s)`.
  3. Prove `irsCode_dim`: dimension `= (k / s) * s` (modulo divisibility).
  4. Prove `irsCode_length`: length `= |ι|`.
  5. Prove `irsCode_relMinDist`: `1 - (k/s)/|ι| + 1/|ι|` (MDS via base RS).
  6. Add notation `scoped notation "IRS[" F ", " L ", " k ", " s "]" => ReedSolomon.Interleaved.irsCode L k s`.
  7. Sanity example: `IRS[F,L,k,1] = RS[F,L,k]`.
  8. Update audit doc.
- **Acceptance**: file builds; sanity example proved.
- **Open questions**: `Matrix ι (Fin s) F` vs `ι → Fin s → F` — match `interleavedCodeSet`'s ambient type.

#### ABF26-D2.14 — `(L,s)`-admissible field element

- **Paper location**: §2.4 page 10, Definition 2.14.
- **Statement**: `ω ∈ F` is `(L,s)`-admissible iff for every `α,β ∈ binom(L,2)`, `α·ω^i ≠ β` for every `0 ≤ i < s`.
- **Status**: missing.
- **Target Lean name**: `ReedSolomon.Folded.Admissible (L : Finset F) (s : ℕ) (ω : F) : Prop`.
- **Target file**: new `ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean`.
- **Direct dependencies (paper)**: none.
- **Direct dependencies (ArkLib infra)**: none.
- **Reverse dependencies**: D2.15, T2.18.
- **Target PR**: Phase 3 PR 2.
- **Sub-tasks**:
  1. Create file.
  2. State the definition.
  3. Prove existence under a size hypothesis: `|F^*| ≥ s·(|L| choose 2) → ∃ ω, Admissible L s ω`.
  4. Update audit doc.
- **Acceptance**: definition + existence stated.
- **Open questions**: do we parametrize by `Finset F` or by `ι ↪ F`? Recommend `Finset F` because paper writes `L ⊆ F`.

#### ABF26-D2.15 — Folded Reed-Solomon code `FRS[F, L, k, s, ω]`

- **Paper location**: §2.4 page 10, Definition 2.15.
- **Status**: missing.
- **Target Lean name**: `ReedSolomon.Folded.frsCode (L : Finset F) (k s : ℕ) (ω : F) : Set (L → (Fin s → F))`.
- **Target file**: same as D2.14.
- **Direct dependencies (paper)**: D2.11, D2.14.
- **Reverse dependencies**: C3.5, T4.14, §6.3.2, T2.18.
- **Target PR**: Phase 3 PR 2.
- **Sub-tasks**:
  1. State definition: `{f : L → F^s | ∃ f̂ ∈ F<k[X], ∀ x ∈ L, f(x) = (f̂(x), f̂(xω), ..., f̂(xω^(s-1)))}`.
  2. Prove `FRS[F,L,k,1,ω] = RS[F,L,k]` for any `ω`.
  3. Prove dimension `= k`.
  4. Prove length `= |L|`.
  5. Prove `δ_min(FRS) = 1 - (k-1)/|L|·s`? — Verify against paper; FRS preserves Singleton-bound-like properties.
  6. Add notation `scoped notation "FRS[" F ", " L ", " k ", " s ", " ω "]" => ...`.
  7. Update audit doc.
- **Acceptance**: definition, `s=1` collapse, dimension, length proved.
- **Open questions**: encoding time claim ("same as RS of block length n·s") — formalize the encoding map but skip the asymptotic claim.

#### ABF26-D2.16 — τ-subspace-design code

- **Paper location**: §2.5 page 10, Definition 2.16 [GX13].
- **Statement**: F-additive `C : F^k → (F^s)^n` is `τ`-subspace-design iff `∀ r ∈ ℕ, ∀` F-linear subspace `A ⊆ C` with `dim A ≤ r`: `(∑_{i ∈ [n]} dim A_i) / n ≤ dim A · τ(r)`, where `A_i = {a ∈ A : a_i = 0^s}`.
- **Status**: missing.
- **Target Lean name**: `CodingTheory.IsSubspaceDesign (C : Submodule F (ι → (Fin s → F))) (τ : ℕ → ℝ) : Prop`.
- **Target file**: new `ArkLib/Data/CodingTheory/SubspaceDesign.lean`.
- **Direct dependencies (paper)**: D2.7.
- **Reverse dependencies**: L2.17, T2.18, T3.4, T4.13.
- **Target PR**: Phase 3 PR 4.
- **Sub-tasks**:
  1. Create file.
  2. Define `A_i := {a ∈ A | a i = 0}` as a `Submodule F A`.
  3. State `IsSubspaceDesign`.
  4. Prove the trivial cases (`r = 0`, `r = 1`).
  5. Update audit doc.
- **Acceptance**: definition + trivial cases proved.
- **Open questions**: `τ : ℕ → ℝ` or `τ : ℕ → ℝ≥0`? Paper allows τ ∈ [0,1] but does not constrain; use `ℝ` for flexibility.

#### ABF26-L2.17 — Lower bound on `τ`

- **Paper location**: §2.5 page 10, Lemma 2.17 [GG25].
- **Statement**: If `C` is a `τ`-subspace-design code of rate `ρ`, then `min_r τ(r) ≥ ρ − 1/n`.
- **Status**: missing.
- **Target Lean name**: `CodingTheory.IsSubspaceDesign.tau_lb`.
- **Target file**: same as D2.16.
- **Direct dependencies (paper)**: D2.16.
- **Reverse dependencies**: indirect; useful for bookkeeping.
- **Target PR**: Phase 3 PR 4.
- **Sub-tasks**:
  1. State.
  2. Prove or admit as external (cite GG25).
  3. Update audit doc.
- **Acceptance**: theorem stated.

#### ABF26-T2.18 — FRS and UM are subspace-design

- **Paper location**: §2.5 page 10, Theorem 2.18 [GK16].
- **Status**: missing.
- **Target Lean name**: `ReedSolomon.Folded.isSubspaceDesign` and `ReedSolomon.Multiplicity.isSubspaceDesign`.
- **Target file**: `ArkLib/Data/CodingTheory/SubspaceDesign.lean` (the FRS/UM instances live here, not in the code-family files).
- **Direct dependencies (paper)**: D2.15, D2.16, DA.7.
- **Reverse dependencies**: T3.4 (via subspace-design list decoding).
- **Target PR**: Phase 3 PR 4.
- **Sub-tasks**:
  1. State for FRS with `τ(r) = s·ρ/(s−r+1)` for `r ∈ [s]`, `τ(r) = 1` otherwise.
  2. State for UM analogously (with `|F| > n` and `char(F) > ρ·s·n > s`).
  3. Prove or admit as external [GK16].
  4. Update audit doc.
- **Acceptance**: both theorems stated.

#### ABF26-D2.19 — Extension field presentation `(B, F, e, ψ, φ)`

- **Paper location**: §2.6 page 11, Definition 2.19.
- **Statement**: structure with two fields `B`, `F`, an injective ring hom `ψ : B ↪ F`, dimension `e`, and a B-linear iso `φ : F → B^e`. Systematic if `φ(ψ(x)) = (x,0,...,0)`.
- **Status**: missing.
- **Target Lean name**: `CodingTheory.ExtensionFieldPresentation` (structure).
- **Target file**: new `ArkLib/Data/CodingTheory/ExtensionCode.lean`.
- **Direct dependencies (paper)**: none.
- **Reverse dependencies**: D2.20, L2.21.
- **Target PR**: Phase 3 PR 5.
- **Sub-tasks**:
  1. Create file.
  2. Define `structure ExtensionFieldPresentation (B F : Type*) [Field B] [Field F] where ψ : B →+* F, ψ_inj : Function.Injective ψ, e : ℕ, φ : F ≃ₗ[B] (Fin e → B)`.
  3. Define `IsSystematic`.
  4. Update audit doc.
- **Acceptance**: structure compiles, `IsSystematic` example for `F = B[X]/⟨irred⟩`.

#### ABF26-D2.20 — Extension code `C_F`

- **Paper location**: §2.6 page 11, Definition 2.20.
- **Status**: missing.
- **Target Lean name**: `CodingTheory.extensionCode (CB : Submodule B (ι → B)) (pres : ExtensionFieldPresentation B F)`.
- **Target file**: same as D2.19.
- **Direct dependencies (paper)**: D2.19, D2.7.
- **Reverse dependencies**: L2.21, §4 extension-field-RS implications.
- **Target PR**: Phase 3 PR 5.
- **Sub-tasks**:
  1. State.
  2. Prove `δ_min(C_F) = δ_min(CB)` (paper notes this, cites DP25 Thm 3.2).
  3. Update audit doc.
- **Acceptance**: definition + distance equality.

#### ABF26-L2.21 — `|Λ(C_F, δ)| = |Λ(C_B^e, δ)|`

- **Paper location**: §2.6 page 11, Lemma 2.21 [BCFW25].
- **Status**: missing.
- **Target Lean name**: `CodingTheory.lambda_extensionCode_eq`.
- **Target file**: same as D2.19.
- **Direct dependencies (paper)**: D2.20, D2.8, D2.9.
- **Reverse dependencies**: §3 extension theorems, §4 extension theorems.
- **Target PR**: Phase 3 PR 5.
- **Sub-tasks**:
  1. State.
  2. Prove or admit as external [BCFW25].
  3. Update audit doc.

### Section 3 — List decoding

#### ABF26-D3.1 — Johnson function family `J_{q,ℓ}`, `J_q`, `J`

- **Paper location**: §3.1 page 12, Definition 3.1.
- **Status**: present-but-different (only `J` present).
- **Existing in ArkLib**: `J` in `ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean`.
- **Target Lean name**: extend with `JohnsonBound.Jqℓ (q ℓ : ℕ) (δ : ℝ)` and `JohnsonBound.Jq (q : ℕ) (δ : ℝ)`.
- **Target file**: existing.
- **Direct dependencies (paper)**: none.
- **Reverse dependencies**: T3.2, C3.3.
- **Target PR**: Phase 4 PR 1.
- **Sub-tasks**:
  1. Define `Jqℓ` and `Jq`.
  2. Prove `J = lim_{q→∞} Jq` (in the limit sense ArkLib can handle, likely a uniform bound).
  3. Prove `Jq = lim_{ℓ→∞} Jqℓ`.
  4. Update audit doc.
- **Acceptance**: all three functions present, limit relationships proved or stated as conjectures (paper does not prove these limits explicitly).

#### ABF26-T3.2 — Johnson bound

- **Paper location**: §3.1 page 12, Theorem 3.2 [Joh62].
- **Status**: present-but-different.
- **Existing in ArkLib**: `johnson_bound`, `johnson_bound_alphabet_free`.
- **Target Lean name**: `ABF26.johnson_bound` aliasing existing form.
- **Target file**: existing.
- **Direct dependencies (paper)**: D3.1.
- **Reverse dependencies**: C3.3.
- **Target PR**: Phase 4 PR 1.
- **Sub-tasks**:
  1. Restate using `Lambda` (paper form `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`).
  2. Prove from existing.
  3. Update audit doc.

#### ABF26-C3.3 — MDS coarse Johnson corollary

- **Paper location**: §3.1 page 12, Corollary 3.3.
- **Statement**: For every MDS code `C` with rate `ρ` and η > 0: `|Λ(C, 1 - √ρ - η)| ≤ 1/(2·η·ρ)`.
- **Status**: missing.
- **Target Lean name**: `ABF26.mds_johnson`.
- **Target file**: `ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean`.
- **Direct dependencies (paper)**: L2.6, T3.2.
- **Reverse dependencies**: §6.3.1 instantiations.
- **Target PR**: Phase 4 PR 1.
- **Sub-tasks**:
  1. State.
  2. Prove from T3.2 + MDS rate-distance relation.
  3. Update audit doc.

#### ABF26-T3.4 — List decoding for τ-subspace-design codes

- **Paper location**: §3.1 page 13, Theorem 3.4 [CZ25].
- **Status**: missing.
- **Target Lean name**: `ABF26.subspaceDesign_list_decoding`.
- **Target file**: `ArkLib/Data/CodingTheory/SubspaceDesign.lean`.
- **Direct dependencies (paper)**: D2.16.
- **Reverse dependencies**: C3.5, §6.3.2.
- **Target PR**: Phase 4 PR 3.
- **Sub-tasks**:
  1. State.
  2. Admit as external [CZ25]. Add to ledger.
  3. Update audit doc.

#### ABF26-C3.5 — Folded RS up to capacity

- **Paper location**: §3.1 page 13, Corollary 3.5 [CZ25 Cor 2.21].
- **Status**: missing.
- **Target Lean name**: `ABF26.frs_list_decoding_capacity`.
- **Target file**: `ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean`.
- **Direct dependencies (paper)**: D2.15, T2.18, T3.4.
- **Reverse dependencies**: §6.3.2.
- **Target PR**: Phase 4 PR 3.
- **Sub-tasks**:
  1. State.
  2. Derive from T3.4 + T2.18.
  3. Update audit doc.

#### ABF26-T3.6 — Random RS near capacity

- **Paper location**: §3.1 page 13, Theorem 3.6 [AGL24 Thm 1.1].
- **Status**: missing. Ledger: external.
- **Target Lean name**: `ABF26.random_rs_list_decoding`.
- **Target file**: new `ArkLib/Data/CodingTheory/ReedSolomon/RandomDomain.lean`.
- **Direct dependencies (paper)**: D2.11.
- **Reverse dependencies**: §4 random RS theorems.
- **Target PR**: Phase 4 PR 3.
- **Sub-tasks**:
  1. State.
  2. Admit; tag.
  3. Update audit doc.

#### ABF26-L3.7 — Elias volume bound

- **Paper location**: §3.2 page 14, Lemma 3.7 [Eli57].
- **Status**: missing.
- **Target Lean name**: `ABF26.elias_volume_bound`.
- **Target file**: `ArkLib/Data/CodingTheory/ListDecodability.lean`.
- **Direct dependencies (paper)**: D2.4, D2.8.
- **Reverse dependencies**: C3.8.
- **Target PR**: Phase 4 PR 4.
- **Sub-tasks**:
  1. State `|Λ(C,δ)| ≥ Vol_q(δ,n) / q^(n-k)`.
  2. Prove via averaging argument from paper.
  3. Update audit doc.

#### ABF26-C3.8 — Volume-based lower bound

- **Paper location**: §3.2 page 14, Corollary 3.8.
- **Statement**: `|Λ(C,δ)| ≥ q^{n(ρ-1+H_q(δ))} / √(8nδ(1-δ))`.
- **Status**: missing.
- **Target Lean name**: `ABF26.volume_lower_bound`.
- **Target file**: same.
- **Direct dependencies (paper)**: D2.2, D2.4, L3.7.
- **Reverse dependencies**: none.
- **Target PR**: Phase 4 PR 4.
- **Sub-tasks**:
  1. State.
  2. Prove using L3.7 + MS77 volume estimate (paper relies on this).
  3. Update audit doc.

#### ABF26-T3.9 — Generalized Singleton bound for list decoding

- **Paper location**: §3.2 page 14, Theorem 3.9 [ST20 Thm 1.2].
- **Status**: missing.
- **Target Lean name**: `ABF26.generalized_singleton_bound`.
- **Target file**: `ArkLib/Data/CodingTheory/ListDecodability.lean`.
- **Direct dependencies (paper)**: D2.8.
- **Reverse dependencies**: T3.10.
- **Target PR**: Phase 4 PR 4.
- **Sub-tasks**:
  1. State.
  2. Prove or admit. Generalizes classical Singleton; should be tractable.
  3. Update audit doc.

#### ABF26-T3.10 — Large-alphabet barrier

- **Paper location**: §3.2 page 14, Theorem 3.10 [BDG24, AGL23].
- **Status**: missing. Ledger: external.
- **Target Lean name**: `ABF26.large_alphabet_lower_bound`.
- **Target PR**: Phase 4 PR 4.
- **Sub-tasks**:
  1. State.
  2. Admit; tag.
  3. Update audit doc.

#### ABF26-T3.11 — Random linear-code lower bound

- **Paper location**: §3.2 page 15, Theorem 3.11 [GLMRSW22 Thm 4.1].
- **Status**: missing. Ledger: external.
- **Target PR**: Phase 4 PR 4.
- **Sub-tasks**: state + admit + audit.

#### ABF26-T3.12 — RS superpolynomial list size over extension fields

- **Paper location**: §3.2 page 15, Theorem 3.12 [BKR06 Cor 2.2].
- **Status**: missing. Ledger: external.
- **Target file**: new `ArkLib/Data/CodingTheory/ReedSolomon/Bounds.lean`.
- **Target PR**: Phase 4 PR 5.
- **Sub-tasks**: state + admit + audit.

#### ABF26-T3.13 — RS large list size over prime fields

- **Paper location**: §3.2 page 15, Theorem 3.13 [GHSZ02 Cor 20].
- **Status**: missing. Ledger: external.
- **Target PR**: Phase 4 PR 5.

#### ABF26-T3.14 — Large-rate RS lower bound

- **Paper location**: §3.2 page 15, Theorem 3.14 [JH01 Thm 2].
- **Status**: missing. Ledger: external.
- **Target PR**: Phase 4 PR 5.

#### ABF26-T3.15 — CW07 hardness barrier

- **Paper location**: §3.2 page 16, Theorem 3.15 [CW07].
- **Status**: missing. Ledger: external.
- **Target PR**: Phase 4 PR 5.
- **Note**: this is an algorithmic hardness statement, not combinatorial. Formalizing reductions to discrete log is out of scope; admit only.

### Section 4 — Correlated agreement conjectures

#### ABF26-D4.1 — Correlated agreement error `ε_ca(C, δ_fld, δ_int)`

- **Paper location**: §4.1 page 17, Definition 4.1.
- **Statement**: `ε_ca(C, δ_fld, δ_int) := max_{f₁,f₂ ∈ (F^s)^n} Pr_{γ ← F}[Δ(f₁ + γ·f₂, C) ≤ δ_fld ∧ Δ((f₁,f₂), C^≡2) > δ_int]`.
- **Status**: ✅ present (closed by commit `d18627fd`; monotonicity in both arguments and the `AffineLines` bridge subsequently added in `cbb08f5c`, `39cd9a67`. `Curves` and `AffineSpaces` bridges remain as follow-ups).
- **Target Lean name**: `ProximityGap.epsCA (C : Submodule F (ι → A)) (δ_fld δ_int : ℝ≥0) : ℝ≥0`.
- **Target file**: new `ArkLib/Data/CodingTheory/ProximityGap/EpsilonErrors.lean`.
- **Direct dependencies (paper)**: D2.3, D2.7.
- **Reverse dependencies**: R4.2, F4.5, L4.6, T4.8, T4.9, R4.10, T4.11, T4.16–T4.18, L4.19, T5.2, T5.3, T5.4, §6.
- **Target PR**: Phase 1 PR 1.
- **Sub-tasks**:
  1. ✅ Create file `ProximityGap/EpsilonErrors.lean` (commit `d18627fd`).
  2. ✅ Define `ProximityGap.epsCA` as the supremum over pairs of words of the joint probability.
  3. ✅ Special-case alias `epsCA' C δ := epsCA C δ δ`.
  4. ✅ `epsCA_antitone_δ_int`: `δ_int ≤ δ_int' → epsCA C δ_fld δ_int' ≤ epsCA C δ_fld δ_int`.
  5. ✅ `epsCA_mono_δ_fld`: `δ_fld ≤ δ_fld' → epsCA C δ_fld δ_int ≤ epsCA C δ_fld' δ_int`.
  6. ✅ Bridges `δ_ε_correlatedAgreementAffineLines_iff_epsCA_le` and `δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le`. **Pending**: same-shape bridge to `AffineSpaces` predicate.
  7. ✅ Update audit doc.
- **Acceptance**: definition + monotonicity + bridge. **Met**: every sub-task closed except the `AffineSpaces` bridge variant.
- **Open questions**: F-additive vs F-linear case — paper handles F-additive, ArkLib has both. Used `Module F A` (which subsumes both via choice of `A`).

#### ABF26-R4.2 — ε_ca discretization

- **Paper location**: §4.1 page 17, Remark 4.2.
- **Statement**: For `β, β' ∈ [0, 1/n)`: `ε_ca(C, δ, δ+β) = ε_ca(C, δ, δ+β') = ε_ca(C, δ, δ)`.
- **Status**: ✅ present (closed by the R4.2 commit; level-set form
  `epsCA_eq_of_floor_eq` proved).
- **Target Lean name**: `ProximityGap.epsCA_eq_of_floor_eq` (general level-set form).
  The paper's β-shift idiom is a corollary in the regime where `δ_int * n ∈ ℕ`.
- **Target file**: same as D4.1.
- **Direct dependencies (paper)**: D4.1.
- **Reverse dependencies**: R4.10.
- **Target PR**: Phase 1 PR 1.
- **Sub-tasks**:
  1. ✅ State.
  2. ✅ Prove via `Δ(f,g) ∈ {0, 1/n, ..., 1}` granularity (via the existing
    `relDistFromCode_le_iff_distFromCode_le` lemma in `Basic/RelativeDistance.lean`).
  3. ✅ Update audit doc.
- **Note on paper formulation**: the paper's exact wording (`ε_ca(C, δ, δ + β) = ε_ca(C, δ, δ)`
  for `β ∈ [0, 1/n)`) holds when `δ * n ∈ ℕ` but can fail at non-aligned `δ`, because shifting
  by `β` could cross a multiple-of-`1/n` boundary. The general level-set form proved here is
  the mathematically correct version.

#### ABF26-D4.3 — Mutual correlated agreement error `ε_mca(C, δ)`

- **Paper location**: §4.1 page 17, Definition 4.3.
- **Statement**: `ε_mca(C, δ) := max_{f₁,f₂} Pr_{γ ← F}[∃ S = S_γ ⊆ [n], |S| ≥ (1-δ)·n s.t. Δ_S(f₁ + γ·f₂, C) = 0 ∧ Δ_S((f₁,f₂), C^≡2) > 0]`.
- **Status**: ✅ present (closed by commit `10245caf`; WHIR `hasMutualCorrAgreement` re-expression is a follow-up).
- **Target Lean name**: `ProximityGap.epsMCA (C : Submodule F (ι → A)) (δ : ℝ≥0) : ℝ≥0`.
- **Target file**: same as D4.1.
- **Direct dependencies (paper)**: D2.3, D2.7, D4.1.
- **Reverse dependencies**: R4.4, F4.5, L4.6, L4.7, T4.8 (RS variant), T4.9.1, T4.11–T4.15, L6.6, L6.8, L6.10.
- **Target PR**: Phase 1 PR 1.
- **Sub-tasks**:
  1. ✅ Define `epsMCA` plus helper preds `pairJointAgreesOn` and `mcaEvent` (commit `10245caf`). Existential over `S` is expressed directly as a `Prop` inside `Pr_{...}[...]`; `open Classical in` makes the resulting decidability work.
  2. **Pending**: re-express `MutualCorrAgreement.hasMutualCorrAgreement` as a specialization of `epsMCA`.
  3. **Pending**: bridge lemma `δ_ε_correlatedAgreement* ↔ epsMCA ≤ ε`.
  4. ✅ Update audit doc.
- **Open questions**: `mcaEvent` is currently `Fin 2`-only; generalization to `Fin ℓ` interleavings is future work. Helpers `pairJointAgreesOn`/`mcaEvent` are currently public — flag for later if they should be `private`.

#### ABF26-R4.4 — No MCA-with-proximity-loss

- **Paper location**: §4.1 page 18, Remark 4.4.
- **Status**: ✅ present (closed by commit `d18627fd`; documentation only).
- **Target**: file-level docstring in `EpsilonErrors.lean`.
- **Target PR**: Phase 1 PR 1.
- **Sub-tasks**:
  1. Add docstring noting paper intentionally does not define MCA with proximity loss.
  2. Update audit doc.

#### ABF26-F4.5 — `ε_pg ≤ ε_ca ≤ ε_mca`

- **Paper location**: §4.1 page 18, Fact 4.5.
- **Status**: ✅ present (closed by commits `c053b38d`, `71084417`, `bddcec81`, and the
  final F4.5 commit; proved for `Submodule F (ι → A)`).
- **Target Lean name**: `ProximityGap.epsPG_le_epsCA`, `ProximityGap.epsCA_le_epsMCA`,
  `ProximityGap.epsPG_le_epsCA_le_epsMCA`.
- **Target file**: same as D4.1.
- **Direct dependencies (paper)**: D4.1, D4.3, plus `ε_pg` (in ArkLib `ProximityGap.epsPG`).
- **Reverse dependencies**: pervasive sanity-check use.
- **Target PR**: Phase 1 PR 1.
- **Sub-tasks**:
  1. ✅ Define `epsPG` (commit `c053b38d`).
  2. ✅ Prove both inequalities (`epsPG_le_epsCA` in `bddcec81`; `epsCA_le_epsMCA` in the F4.5 finish commit). The proof relies on the helper `jointProximity_imp_line_close` (commit `71084417`) plus the existing `Pr_le_Pr_of_implies` in `Probability/Instances.lean`.
  3. ✅ Update audit doc.
- **Acceptance**: both inequalities proved. ✅ Met.
- **Open follow-ups**: factor out a `not_jointProximity_imp_no_pair_agreement` helper if it
  is reused by L4.6 or the bridging lemmas; right now the joint-agreement contradiction
  is inlined inside `epsCA_le_epsMCA`.

#### ABF26-L4.6 — ε_mca = ε_ca below `δ_min/2`

- **Paper location**: §4.1 page 18, Lemma 4.6 [ACFY25 Lemma 4.10].
- **Status**: missing.
- **Target Lean name**: `ProximityGap.epsMCA_eq_epsCA_below_udr`.
- **Target file**: same as D4.1.
- **Direct dependencies (paper)**: D4.1, D4.3, D2.5.
- **Reverse dependencies**: T4.9.1.
- **Target PR**: Phase 1 PR 2.
- **Sub-tasks**:
  1. State `δ < δ_min(C)/2 → epsMCA C δ = epsCA C δ δ`.
  2. Prove via uniqueness of the close codeword (the witness `S` is fixed once you fix the codeword).
  3. Update audit doc.

#### ABF26-L4.7 — Interleaving degrades MCA by at most `t`

- **Paper location**: §4.1 page 18, Lemma 4.7.
- **Statement**: `ε_mca(C^≡t, δ) ≤ t · ε_mca(C, δ)`.
- **Status**: missing.
- **Target Lean name**: `ProximityGap.epsMCA_interleaved_le`.
- **Target file**: same as D4.1.
- **Direct dependencies (paper)**: D4.3, D2.9.
- **Reverse dependencies**: §6.3.1.
- **Target PR**: Phase 1 PR 2.
- **Sub-tasks**:
  1. State.
  2. Prove via union bound across rows.
  3. Update audit doc.

#### ABF26-T4.8 — AHIV17 general-code unique-decoding bound

- **Paper location**: §4.2.1 page 18, Theorem 4.8 [AHIV17].
- **Statement**: For linear `C` and `δ ≤ δ_min(C)/3`: `ε_mca(C,δ) = ε_ca(C,δ) ≤ (n·δ + 1)/|F|`.
- **Status**: missing as a paper-shaped statement. As of `05a010e3`, the underlying AHIV22 result is sorry-free in ArkLib (PR #385); only the paper-shaped restatement is missing.
- **Target Lean name**: `ABF26.ahiv17_epsCA_bound`.
- **Target file**: `ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean` (extend).
- **Direct dependencies (paper)**: D4.1, D4.3, L4.6.
- **Reverse dependencies**: §6.
- **Target PR**: Phase 5 PR 1.
- **Sub-tasks**:
  1. Restate the existing sorry-free AHIV22 result in `ε_ca` form on top of the new numeric interface.
  2. Combine with L4.6 to get the `ε_mca = ε_ca` form below `δ_min(C)/3`.
  3. Update audit doc.

#### ABF26-T4.9.1 — RS unique-decoding Item 1 [BCIKS20 Thm 1.4]

- **Paper location**: §4.2.1 page 18, Theorem 4.9 Item 1.
- **Statement**: `ε_mca(C, δ_fld) = ε_ca(C, δ_fld) ≤ n/|F|` for `δ_fld ≤ (1-ρ)/2`.
- **Status**: present-but-different (existing BCIKS20 work uses predicate CA).
- **Existing**: `RS_correlatedAgreement_affineLines_uniqueDecodingRegime` and `RS_correlatedAgreement_affineLines` in `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/`.
- **Target Lean name**: `ABF26.rs_epsMCA_uniqueDecoding`.
- **Target file**: existing.
- **Direct dependencies (paper)**: D4.1, D4.3, L4.6, D2.11.
- **Reverse dependencies**: §6.3.1.
- **Target PR**: Phase 5 PR 2.
- **Sub-tasks**:
  1. Phase 2 close sorries first.
  2. Restate via ε_mca / ε_ca.
  3. Update audit doc.

#### ABF26-T4.9.2 — RS unique-decoding Item 2 [BCHKS25 Thm 1.3]

- **Paper location**: §4.2.1 page 19, Theorem 4.9 Item 2.
- **Statement**: For `δ_min(C)/3 ≤ δ_fld < δ_int`, `ε_ca(C, δ_fld, δ_int) ≤ max{(1-ρ-δ_fld)/(δ_fld(1-ρ-2δ_fld)|F|), δ_int/((δ_int-δ_fld)|F|)}`.
- **Status**: missing.
- **Target Lean name**: `ABF26.rs_epsCA_bchks25`.
- **Target file**: existing BCIKS20 main file or new sibling.
- **Direct dependencies (paper)**: D4.1, D2.11.
- **Reverse dependencies**: R4.10, T5.2.
- **Target PR**: Phase 5 PR 2.
- **Sub-tasks**:
  1. State.
  2. Admit as external [BCHKS25] — long proof. Add to ledger? No — this is core RS theory we may want to prove, but defer to external until Phase 5 finalization. Mark as conditional admit.
  3. Update audit doc.

#### ABF26-R4.10 — Small proximity-loss simplification

- **Paper location**: §4.2.1 page 19, Remark 4.10.
- **Status**: missing.
- **Target Lean name**: `ABF26.epsCA_small_loss`.
- **Target file**: same as D4.1.
- **Direct dependencies (paper)**: T4.9.2, R4.2.
- **Reverse dependencies**: none.
- **Target PR**: Phase 5 PR 3.
- **Sub-tasks**:
  1. Derive from R4.2 + T4.9.2.
  2. Update audit doc.

#### ABF26-T4.11 — 1.5-Johnson regime for general linear codes

- **Paper location**: §4.2.2 page 19, Theorem 4.11.
- **Status**: missing.
- **Target Lean name**: `ABF26.linear_1_5_johnson`.
- **Target file**: new `ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean`.
- **Direct dependencies (paper)**: D4.3.
- **Reverse dependencies**: §6.
- **Target PR**: Phase 6 PR 2.
- **Sub-tasks**:
  1. State both items (GKL24 form and BGKS20 form).
  2. Admit as external if too long.
  3. Update audit doc.

#### ABF26-T4.12 — Johnson-range RS MCA bound

- **Paper location**: §4.2.2 page 19, Theorem 4.12 [BCHKS25 Thm 4.6].
- **Status**: missing. Ledger: external.
- **Target PR**: Phase 6 PR 2.

#### ABF26-T4.13 — MCA from τ-subspace-design codes

- **Paper location**: §4.2.2 page 20, Theorem 4.13 [GG25 Cor 4.9].
- **Status**: missing. Ledger: external.
- **Target PR**: Phase 6 PR 2.

#### ABF26-T4.14 — Folded RS MCA up to capacity

- **Paper location**: §4.2.2 page 20, Theorem 4.14 [GG25 Cor 4.10].
- **Status**: missing. Ledger: external.
- **Target PR**: Phase 6 PR 2.

#### ABF26-T4.15 — Random RS MCA up to capacity

- **Paper location**: §4.2.2 page 20, Theorem 4.15 [GG25 Thm 5.15].
- **Status**: missing. Ledger: external.
- **Target PR**: Phase 6 PR 2.

#### ABF26-T4.16 — Lower bound on CA near capacity

- **Paper location**: §4.3 page 21, Theorem 4.16 [BCHKS25/KK25].
- **Status**: missing. Ledger: external.
- **Target PR**: Phase 6 PR 3.

#### ABF26-T4.17 — Complete CA breakdown

- **Paper location**: §4.3 page 21, Theorem 4.17 [CS25 Cor 1].
- **Status**: missing. Ledger: external.
- **Target PR**: Phase 6 PR 3.

#### ABF26-T4.18 — CA jump at the Johnson bound

- **Paper location**: §4.3 page 21, Theorem 4.18 [BCHKS25 Cor 1.7].
- **Status**: missing. Ledger: external.
- **Target PR**: Phase 6 PR 3.

#### ABF26-L4.19 — CA bounded below by sampling probability

- **Paper location**: §4.3 page 21, Lemma 4.19 [DG25 Thm 2.5].
- **Statement**: `ε_ca(C,δ) ≥ ((q-1)/q) · Pr_{u ← F^n}[Δ(u,C) ≤ δ]` for `δ < δ' = max_{u} Δ(u,C)`.
- **Status**: missing.
- **Target Lean name**: `ABF26.epsCA_ge_sampling`.
- **Target file**: same as D4.1.
- **Direct dependencies (paper)**: D4.1.
- **Reverse dependencies**: T4.16, T4.17.
- **Target PR**: Phase 6 PR 3.
- **Sub-tasks**:
  1. State.
  2. Prove or admit.
  3. Update audit doc.

#### ABF26-D4.20 — Line-decoding

- **Paper location**: §4.4 page 22, Definition 4.20 [GG25 Def 3.1].
- **Statement**: `C` is `(δ,a,b)`-line-decodable iff for every `f₁,f₂ ∈ Σ^n` and every `U : F → C`, if `Pr_γ[Δ(f₁+γ·f₂, U(γ)) ≤ δ] ≥ a/|F|`, then `∃ u₁,u₂ ∈ C` with `Pr_γ[U(γ) = u₁ + γ·u₂] ≥ b/|F|`.
- **Status**: missing.
- **Target Lean name**: `CodingTheory.LineDecodable (C : Submodule F (ι → A)) (δ a b : ℝ) : Prop`.
- **Target file**: new `ArkLib/Data/CodingTheory/LineDecoding.lean`.
- **Direct dependencies (paper)**: D2.7.
- **Reverse dependencies**: T4.21.
- **Target PR**: Phase 6 PR 1.
- **Sub-tasks**:
  1. Create file.
  2. State definition.
  3. Add notation if desired.
  4. Update audit doc.

#### ABF26-T4.21 — Line-decoding implies MCA

- **Paper location**: §4.4 page 22, Theorem 4.21 [GG25 Thm 3.5].
- **Statement**: `LineDecodable C δ a (n+1) → ε_mca(C,δ) ≤ a/|F|`.
- **Status**: missing.
- **Target Lean name**: `ABF26.lineDecodable_implies_epsMCA`.
- **Target file**: same as D4.20.
- **Direct dependencies (paper)**: D4.3, D4.20.
- **Reverse dependencies**: §6.
- **Target PR**: Phase 6 PR 1.
- **Sub-tasks**:
  1. State.
  2. Prove or admit.
  3. Update audit doc.

### Section 5 — Connections

#### ABF26-T5.1 — List decoding implies MCA

- **Paper location**: §5 page 23, Theorem 5.1 [GCXK25 Thm 3].
- **Status**: missing. Ledger: external.
- **Target Lean name**: `ABF26.listDecoding_implies_mca`.
- **Target file**: new `ArkLib/Data/CodingTheory/Connections.lean`.
- **Direct dependencies (paper)**: D2.8, D4.3.
- **Reverse dependencies**: §6.
- **Target PR**: Phase 7 PR 1.
- **Sub-tasks**:
  1. State.
  2. Admit.
  3. Update audit doc.

#### ABF26-T5.2 — Small ε_ca implies list < |F|

- **Paper location**: §5 page 23, Theorem 5.2 [BCHKS25 Thm 1.9].
- **Status**: missing. Ledger: external.
- **Target Lean name**: `ABF26.smallEpsCA_implies_listSmall`.
- **Target file**: same.
- **Target PR**: Phase 7 PR 1.

#### ABF26-T5.3 — CA implies list decoding for related RS

- **Paper location**: §5 page 24, Theorem 5.3 [CS25 Thm 2].
- **Status**: missing. Ledger: external.
- **Target Lean name**: `ABF26.epsCA_implies_listDec`.
- **Target file**: same.
- **Target PR**: Phase 7 PR 1.

#### ABF26-T5.4 — Separation: list-decoding does not tightly imply CA

- **Paper location**: §5 page 24, Theorem 5.4 [BGKS20 Lem 3.3].
- **Status**: missing. Ledger: external.
- **Target Lean name**: `ABF26.list_vs_ca_separation`.
- **Target file**: same.
- **Target PR**: Phase 7 PR 2.

### Section 6 — Toy problem (deferred)

All §6 items are deferred until OracleReduction security framework gaps are
closed. They are tracked here so we don't lose them.

#### ABF26-D6.1 — Toy problem relation `R_C^ℓ`

- **Paper location**: §6.1 page 25, Definition 6.1.
- **Status**: deferred.
- **Target Lean name**: `ABF26.ToyProblem.relation`.
- **Target file**: new `ArkLib/ProofSystem/ToyProblem/Basic.lean` (when undeferred).

#### ABF26-C6.2 — Construction 6.2

- **Paper location**: §6.1 page 25.
- **Status**: deferred.
- **Reverse dependencies**: L6.6, L6.8.

#### ABF26-D6.3 — Relaxed toy relation `R̃_C,δ^ℓ`

- **Paper location**: §6.2 page 26, Definition 6.3.
- **Status**: deferred.

#### ABF26-D6.4 — Erasure correction

- **Paper location**: §6.2 page 26, Definition 6.4.
- **Status**: deferred.

#### ABF26-L6.5 — Every additive code supports erasure correction

- **Paper location**: §6.2 page 26, Lemma 6.5 [GRS12].
- **Status**: deferred.

#### ABF26-L6.6 — Knowledge soundness of Construction 6.2

- **Paper location**: §6.2 page 26, Lemma 6.6.
- **Status**: deferred. **Hard prereq**: `OracleReduction/Security/Basic.lean` sorries cleared.

#### ABF26-R6.7 — CA insufficient for Lemma 6.6 proof

- **Paper location**: §6.2 page 28, Remark 6.7.
- **Status**: deferred.

#### ABF26-L6.8 — RBR knowledge soundness of Construction 6.2

- **Paper location**: §6.2 page 29, Lemma 6.8.
- **Status**: deferred. **Hard prereq**: `OracleReduction/Security/RoundByRound.lean` sorries cleared.

#### ABF26-C6.9 — Construction 6.9 (attack target)

- **Paper location**: §6.4 page 34.
- **Status**: deferred.

#### ABF26-L6.10 — Soundness of Construction 6.9

- **Paper location**: §6.4 page 35, Lemma 6.10.
- **Status**: deferred.

#### ABF26-D6.11 — Winning set `Ω`

- **Paper location**: §6.4 page 35, Definition 6.11.
- **Status**: deferred.

#### ABF26-L6.12 — List-decoding lower-bound attack

- **Paper location**: §6.4 page 35, Lemma 6.12.
- **Status**: deferred. Uses B.1.

#### ABF26-L6.13 — CA lower-bound attack

- **Paper location**: §6.4 page 37, Lemma 6.13.
- **Status**: deferred.

#### ABF26-R6.14 — Attack only reaches `ε_ca`, not `ε_mca`

- **Paper location**: §6.4 page 37, Remark 6.14.
- **Status**: deferred.

### Appendix A — Additional preliminaries

#### ABF26-DA.1 — IOR completeness

- **Paper location**: App A.1 page 40, Definition A.1.
- **Status**: present-but-different.
- **Existing**: `Reduction.completeness`, `Reduction.perfectCompleteness` in `ArkLib/OracleReduction/Security/Basic.lean`.
- **Target Lean name**: alias `ABF26.IOR.completeness`.
- **Target PR**: Phase 9 PR 2.
- **Sub-tasks**: add docstring noting equivalence to paper Def A.1.

#### ABF26-RA.2 — IOP as IOR to trivial relation

- **Paper location**: App A.1 page 40, Remark A.2.
- **Status**: present-but-different.
- **Target**: docstring in `Security/Basic.lean`.
- **Target PR**: Phase 9 PR 2.

#### ABF26-DA.3 — Knowledge soundness for IORs

- **Paper location**: App A.1 page 40, Definition A.3.
- **Status**: present-but-different.
- **Existing**: `Verifier.knowledgeSoundness` in `Security/Basic.lean`.
- **Target Lean name**: alias `ABF26.IOR.knowledgeSoundness`.
- **Target PR**: Phase 9 PR 2.

#### ABF26-DA.4 — Knowledge state function

- **Paper location**: App A.1 page 41, Definition A.4.
- **Status**: present.
- **Existing**: `Security/RoundByRound.lean`.
- **Target PR**: none.

#### ABF26-DA.5 — Round-by-round knowledge soundness

- **Paper location**: App A.1 page 41, Definition A.5.
- **Status**: present-but-different.
- **Existing**: `Verifier.rbrKnowledgeSoundnessOneShot`, `Verifier.rbrKnowledgeSoundness`.
- **Target PR**: Phase 9 PR 2 (alias).

#### ABF26-DA.6 — Formal derivative

- **Paper location**: App A.2 page 41, Definition A.6.
- **Status**: present-but-different (Mathlib has it).
- **Target Lean name**: alias `ABF26.formalDerivative := Polynomial.derivative`.
- **Target file**: new `ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean`.
- **Target PR**: Phase 3 PR 3.
- **Sub-tasks**: define iterated derivative `f^(s) := (Polynomial.derivative)^[s]`.

#### ABF26-DA.7 — Univariate multiplicity code `UM[F, L, k, s]`

- **Paper location**: App A.2 page 41, Definition A.7 [GW13, KSY14].
- **Status**: missing.
- **Target Lean name**: `ReedSolomon.Multiplicity.umCode (L : Finset F) (k s : ℕ)`.
- **Target file**: same as DA.6.
- **Direct dependencies (paper)**: D2.11, DA.6.
- **Reverse dependencies**: T2.18, T4.14 indirectly.
- **Target PR**: Phase 3 PR 3.
- **Sub-tasks**:
  1. Create file.
  2. Define `umCode`.
  3. Prove `umCode F L k 1 = ReedSolomon.code (Finset.fintype L) k`.
  4. Prove `umCode F L k s = irsCode applied to (f, f', ..., f^(s-1))`.
  5. Add notation.
  6. Update audit doc.

### Appendix B

#### ABF26-B.1 — Collision bound

- **Paper location**: App B page 42, Claim B.1.
- **Status**: missing.
- **Target Lean name**: `ABF26.collision_bound`.
- **Target file**: new `ArkLib/Data/Probability/Combinatorial.lean`.
- **Direct dependencies (paper)**: none.
- **Reverse dependencies**: L6.12.
- **Target PR**: Phase 8 (deferred).
- **Sub-tasks**: state + prove (the proof is short and self-contained in the paper).

---

## 8. Per-PR breakdown (forward index)

This is the read-from-the-other-direction index: given a PR, which items
does it close? The §7 ledger is authoritative; this section is a
convenience.

- **Phase 0 PR 1**: audit refresh. No item closures; updates audit rows.
  Findings landed: `AHIV22.lean`, `BCIKS20/ReedSolomonGap.lean`, and
  `BCIKS20/AffineSpaces.lean` are now sorry-free (closed by PRs #385, #463,
  and commit `6389c0e` respectively; the third was pushed directly to main
  without an associated PR number). New residual `sorry`s discovered in
  `BCIKS20/ListDecoding/*`, `BCIKS20/WeightedAgreement.lean`, and
  `DG25/MainResults.lean`. Phase 2 PR list below is re-scoped accordingly.
- **Phase 1 PR 1**: ✅ D2.8 (Lambda, commit `7c913b3b`), ✅ D4.1 (`d18627fd`),
  ✅ D4.3 (`10245caf`), ✅ R4.2 (R4.2 finish commit), ✅ R4.4 (`d18627fd`),
  ✅ F4.5 (chain `c053b38d` → `71084417` → `bddcec81` → `1ec90bf1`).
  **Phase 1 PR 1 complete.**
- **Phase 1 PR 2**: L4.6, L4.7.
- **Phase 1 PR 3**: bridging lemmas + WHIR re-expression (does not touch the
  3 non-conjectural sorries in `Whir/MutualCorrAgreement.lean`, which stay
  during the interface migration).
- **Phase 2 PR 1**: `BCIKS20/AffineLines/Main.lean` line-40 sorry
  (`RS_correlatedAgreement_affineLines` non-unique-decoding branch). Closes
  T4.9.1 to fully `present`.
- **Phase 2 PR 2**: `BCIKS20/Curves.lean` (3 sorries).
- **Phase 2 PR 3**: `BCIKS20/ListDecoding/Agreement.lean` (8),
  `Extraction.lean` (2), `Guruswami.lean` (2). One PR if helpers shared,
  otherwise split. **Soft prereq**: PR #497 (`feat: proofs for rational
  function lemmas`) is open against `main` and adds the rational-function
  machinery these `sorry`s need. If #497 has not merged when Phase 2
  PR 3 begins, plan to either rebase on top of it or absorb its content.
- **Phase 2 PR 4**: `BCIKS20/WeightedAgreement.lean` (6 sorries).
- **Phase 2 PR 5**: `DG25/MainResults.lean` (2 sorries). Touches L4.19
  underpinnings.
- **Phase 2 PR 6**: `GuruswamiSudan/GuruswamiSudan.lean` (3 sorries).
  Required before §3 results that cite GS decoding.
- **Phase 3 PR 1**: D2.13.
- **Phase 3 PR 2**: D2.14, D2.15.
- **Phase 3 PR 3**: DA.6, DA.7 (UM and formal derivative).
- **Phase 3 PR 4**: D2.16, L2.17, T2.18.
- **Phase 3 PR 5**: D2.19, D2.20, L2.21.
- **Phase 4 PR 1**: D3.1, T3.2, C3.3.
- **Phase 4 PR 2**: L2.10 (interleaved-code list-size bound).
- **Phase 4 PR 3**: T3.4, C3.5, T3.6.
- **Phase 4 PR 4**: L3.7, C3.8, T3.9, T3.10, T3.11.
- **Phase 4 PR 5**: T3.12, T3.13, T3.14, T3.15.
- **Phase 5 PR 1**: T4.8.
- **Phase 5 PR 2**: T4.9.1, T4.9.2.
- **Phase 5 PR 3**: R4.10.
- **Phase 6 PR 1**: D4.20, T4.21.
- **Phase 6 PR 2**: T4.11, T4.12, T4.13, T4.14, T4.15.
- **Phase 6 PR 3**: T4.16, T4.17, T4.18, L4.19.
- **Phase 7 PR 1**: T5.1, T5.2, T5.3.
- **Phase 7 PR 2**: T5.4.
- **Phase 8** (deferred): D6.1, C6.2, D6.3, D6.4, L6.5, L6.6, R6.7, L6.8, C6.9, L6.10, D6.11, L6.12, L6.13, R6.14, B.1.
- **Phase 9 PR 1**: L2.1, D2.2, D2.4 (entropy / volume / poly identity wrapping).
- **Phase 9 PR 2**: D2.3, D2.5, D2.7, D2.9, D2.11 notation aliases, DA.1, RA.2, DA.3, DA.5 aliases.

Total: 28 PRs across 9 phases (Phase 8 deferred = 0 PRs in initial plan).

---

## 9. How to use this plan

1. Pick the next phase from §3 whose prereqs are satisfied.
2. Open the per-item entries in §7 covered by that PR.
3. Execute the sub-tasks in order, committing each numbered sub-task as a
   self-contained change where reasonable.
4. Update the audit doc row in the same PR.
5. Mark the item with a ✅ in §7 by replacing `Status: missing` with
   `Status: present (closed by PR #N)`.
6. Run `./scripts/validate.sh`. If green, open the PR.

---

*End of plan. Last revised: 2026-05-14.*
