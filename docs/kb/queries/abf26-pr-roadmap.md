# ABF26 PR — end goal and roadmap

**Branch:** `feat/abf26-plan` (PR #505) — formalises *Open Problems in
List Decoding and Correlated Agreement* (Arnon, Boneh, Fenzi, April 2026)
on top of ArkLib.

**Companion artefacts:**
- audit / paper↔Lean map:
  [`audits/open-problems-list-decoding-and-correlated-agreement.md`](../audits/open-problems-list-decoding-and-correlated-agreement.md)
- review findings (backward-looking):
  [`queries/abf26-review-2026-05.md`](abf26-review-2026-05.md)
- lint + drift harness: `scripts/abf26/{coverage,lint}.py`,
  `scripts/abf26/owned-files.txt`

## State snapshot (2026-05-20, mid Phase 2)

87 paper items audited; coverage:

| Status | Count | Δ since 2026-05-18 |
|---|---|---|
| present | **33** | **+3** (L2.1 via generalised SZ wrapper; D2.20 via Algebra/Basis refactor + basis-expansion proof close; B.1 via Cauchy-Schwarz + ENNReal contradiction route) |
| present-but-different | **10** | **−1** |
| present-but-incomplete | **9** | **−2** |
| deferred | 3 (blocked on missing primitives) | 0 |

The 10 `present-but-different` rows are **intentional**: each one is
either (a) realised by a more general ArkLib abstraction whose name
differs from the paper's, or (b) using ArkLib's matrix-/Submodule-based
shape rather than the paper's `Σ^n`-set shape. The paper↔Lean name
map is recorded in the audit doc's *Notes* column. Per the
no-duplication rule, ArkLib avoids paper-shape `alias` wrappers; use
the in-tree name directly when writing downstream code.

**Today's alias sweep was reverted.** Promoting A.1 / A.3 / A.5 / A.6
/ D2.7 from `present-but-different` to `present` via `ABF26.IOR.*`
aliases looked like coverage growth but was a cosmetic — the
underlying definitions never changed, the aliases just renamed them.
Per the durable rule "re-use existing ArkLib abstractions directly;
generalise originals safely instead of duplicating", these aliases
were anti-integration and have been removed. `Aliases.lean` is gone.

The harness got two defensive fixes during the sweep that *stay*:

  - `scripts/abf26/coverage.py` header detection now requires *all*
    canonical header keys on a line (was: `any`), so body prose
    mentioning the word "Status" no longer corrupts the table parse.
  - The `paper_ctx` regex used to strip "(paper notation …)"
    parentheticals now skips Markdown `.lean` link targets, so a path
    containing "Paper" is not silently dropped.
  - `alias` added to recognised declaration kinds and Mathlib-prefixed
    symbols silently skipped, so future paper-shape *generalisations*
    (not duplications) work cleanly.

- All review-driven H/M/L issues landed (see review query page).
- `scripts/abf26/coverage.py` reports 0 missing / 0 drift.
- `./scripts/validate.sh` green.
- ~30 paper-citation PDFs vendored locally under `references/`
  (disposition decision still open — see "Phase 1" below).

## End-goal levels

| Level | What "done" looks like | Status | Scope for this PR |
|---|---|---|---|
| **A** | Every ABF26 item has a paper-aligned Lean statement; in-tree-provable items closed; external results tagged sorries with citations. Audit doc is the canonical paper↔Lean map. | ~85–90% there | **Target** |
| B | All in-tree provables closed (`oracleReduction_perfectCompleteness`, `extensionCode_smul_mem`, L4.6, B.1, etc.). | partial | Stretch / follow-up PR |
| C | Soundness suite usable downstream (L6.6/L6.8 closed, FRS/IRS/multiplicity numeric error bounds working). | not started | Out of scope |

## Roadmap (priority-ordered)

### Phase 1 — draft → ready-for-review (housekeeping, hours)

- Decide `ABF26_REVIEW.md` (repo root) disposition: move to
  `docs/wiki/`, fold into audit doc, or delete after fixes landed.
  *Update (2026-05-19): filed under `docs/kb/queries/` instead, see
  the companion artefacts list above.*
- Decide `references/` disposition: vendor the PDFs (~20 MB) as a
  corpus, or `.gitignore` and rely on `MANIFEST.md` as a fetch script.
- ~~Walk the 10 `present-but-different` rows for cheap paper-shaped
  aliases that promote them to `present`.~~ **Reverted 2026-05-19**:
  paper-shape aliases are anti-integration; the in-tree ArkLib name
  IS the canonical Lean name, and the audit's Notes column already
  records the paper↔Lean name map. `present-but-different` is the
  correct label for pure-naming divergence and does not need
  promotion. See [`abf26-review-2026-05.md`](abf26-review-2026-05.md)
  for the policy.

### Phase 2 — close in-tree provables (1–2 days each)

- ✅ `prob_polynomial_identity_le` (ABF26 L2.1, paper individual-degree
  shape `m·(d-1)/|F|`) — landed 2026-05-20 via safe generalisation of
  the legacy `prob_schwartz_zippel_mv_polynomial` wrapper.
- ✅ `CodingTheory.extensionCode_smul_mem` (ABF26 D2.20 F-linearity) —
  landed 2026-05-20 via Algebra/Basis refactor of
  `ExtensionFieldPresentation` (commit `f190de47`) + basis-expansion +
  `Finset.sum_induction` proof close (commit `6124b8a7`).
- ⏳ `ToyProblem.Spec.oracleReduction_perfectCompleteness` —
  protocol-level wrapper around the already-closed
  `accepts_of_inputRelation`. ~50-100 lines of bespoke
  `simulateQ_bind` / `StateT.run_bind` unfold for the 3-round protocol
  (cf. Sumcheck `SingleRound.reduction_perfectCompleteness` for the
  2-round template). Better as a focused proof PR.
- ✅ `Probability.exists_large_image_of_pairwise_collision_bound`
  (ABF26 B.1) — landed 2026-05-20. Contradiction-form proof
  (Cauchy-Schwarz + ENNReal cross-multiplication + averaging, avoids
  Jensen). Helpers `sum_fiber_sq_eq` and `cauchy_schwarz_fiber`
  live alongside in [`Combinatorial.lean`](../../../ArkLib/Data/Probability/Combinatorial.lean).
  Unblocks `L6.12` downstream.
- ⏳ `T4.8` (AHIV17 general-code unique-decoding, paper-shape `ε_ca`
  form) — ε-wrap AHIV22's `prob_of_bad_pts` (PMF-over-rowspan) into
  `epsCA`'s PMF-over-γ form. ~50+ lines including the indexing
  translation.
- Predicate↔numeric bridges in
  `ArkLib/Data/CodingTheory/ProximityGap/Errors.lean` (L4.6 etc.).
- ~~Paper-shaped aliases sweep~~ (rejected — see
  [`abf26-review-2026-05.md`](abf26-review-2026-05.md)).

### Phase 3 — deferred & stretch (optional for this PR)

- Resolve the 3 deferred rows (T3.6, T4.15, R6.14) — need
  `Data/Probability/UniformSubset` primitive or explicit
  out-of-scope marker.
- ~~`Probability.Combinatorial.exists_large_image_of_pairwise_collision_bound`
  (Claim B.1)~~ closed 2026-05-20 (see Phase 2 entry above).

## Items not in scope for this PR

- Closing L6.6 / L6.8 / L6.10 soundness theorems (Phase C — needs the
  MCA stack and extractor machinery).
- Closing the 11 paper-cited external admits beyond their statements.
  Each one is a substantial proof effort (the corresponding source
  papers run 30–60 pages each).
- Building the `Data/Probability/UniformSubset` primitive needed by
  T3.6 / T4.15.

## How to use this page

- On returning to the branch after a break: start with the *immediate
  next step* under whichever phase is currently in-flight.
- When closing an item, update the audit doc row to `present` (and
  promote the corresponding Phase entry here if it unblocks a
  follow-up).
- When the audit doc shows ≥35 `present` rows and ≤7
  `present-but-different` rows, the PR has hit end-goal A and is
  ready to flip out of draft.

## References

- [ABF26 audit doc](../audits/open-problems-list-decoding-and-correlated-agreement.md)
- [ABF26 review findings, 2026-05](abf26-review-2026-05.md)
- [`scripts/abf26/coverage.py`](../../../scripts/abf26/coverage.py) — drift checker
- [`scripts/abf26/lint.py`](../../../scripts/abf26/lint.py) — style sweep
- [`scripts/abf26/owned-files.txt`](../../../scripts/abf26/owned-files.txt) — branch ownership manifest
