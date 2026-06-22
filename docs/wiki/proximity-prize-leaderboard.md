# Proximity-Prize "bits of security" leaderboard

A machine-checked leaderboard for the soundness of the ABF26 §6 toy protocol. It
turns the Ethereum Foundation **Proximity Prize** (proximityprize.org, $1M)
question — *how big is the gap between what we can prove and the best known
attack?* — into a single Lean scalar that contestants minimise.

- **Code:** [`ArkLib/ProofSystem/ToyProblem/Leaderboard.lean`](../../ArkLib/ProofSystem/ToyProblem/Leaderboard.lean)
  (the common quantity, interfaces, and the interleaved-RS anchors);
  [`ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean`](../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean)
  (the folded-RS entry).
- **Paper:** Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated
  Agreement* (eprint 2026/680), §6.2 (Lemma 6.8), §6.4 (Lemmas 6.10, 6.12,
  6.13), §6.3 ("Knowledge soundness upperbound" / "Soundness lowerbound"
  parheads + Tables 2–5; §6.3.2 the folded / subspace-design analysis). The
  attack side is also Fenzi–Sanso, eprint 2025/2197 (Lemma 4.4 ≈ Lemma 6.12)
  and the [KKH26]-backed list-size tables.

## The one quantity both sides bound: a δ-swept frontier

The two leaderboard sides must bound the **same** scalar or the gap between
them is meaningless. ABF26's §6.3 analysis is a *sweep over the proximity
parameter δ*: any round-by-round analysis of Construction 6.2 picks an
admissible `δ ∈ (0, δ_min(C))` (the L6.8/L6.10 range), after which round 1's
true error is `winningSetSoundness enc δ` (Definition 6.11 — the paper says
the simplified IOR's soundness error "is exactly" this) and round 2's is the
spot-check `(1-δ)^t`. The common quantity is the best error provable by *any*
such analysis — their **convex / union combination**, infimised over δ:

```
bestProvableError p
  = ⨅ δ ∈ (0, δ_min(C)),  (1-δ)^t + winningSetSoundness p.enc δ · (1 - (1-δ)^t)
```

Key design points:

- **Convex, not `max`.** The two round errors combine by the union bound
  `(1-δ)^t + ε₀·(1 - (1-δ)^t)`, not the paper's printed `max(ε₀, (1-δ)^t)`. The
  printed `max` is *false* as a round-by-round bound (`protocol62_knowledgeSound`,
  author-confirmed; the two differ by `winningSetSoundness·(1-δ)^t`, negligible
  in regime). The in-tree quantity uses the corrected convex form.
- **δ is swept, not pinned.** The two sides certify their bounds at *different*
  δ — the provable side optimizes near `δ = 1 − √ρ − η` (Johnson regime), the
  attack side works near `δ* = 0.468` (`tab:elias-lowerbound-thresholds`). A
  single shared δ cannot represent the paper's frontier. The `⨅` makes both
  legitimate bounds on the same scalar. The Y-side helper `le_bestProvableError`
  (the `le_iInf₂` dual of `bestProvableError_le`) reduces an attack ceiling to a
  per-δ floor over the whole admissible window.
- **Pinned encoding.** All Definition-6.11 objects use the fixed-encoding
  relations `relaxedRelationFor enc` / `winningSetFor enc` (the paper's code
  *is* its injective encoding `C : F^k → (F^s)^n`). `ToyParams` carries
  `enc` + `enc_injective` and derives the code as `p.code = Set.range p.enc`.
  The earlier existential-encoding relations (under which the linear constraint
  is reparameterisable and the supremum collapses) were deleted.
- **Generic over the codeword alphabet.** `ToyParams` carries an alphabet `A`
  (an `F`-module) with `enc : (Fin k → F) →ₗ[F] (ι → A)`. `A = F` is the scalar
  / **interleaved-RS** case (`koalaIRS`); `A = Fin s → F` is the **folded-RS**
  case (`koalaFRS`, `s`-folding). The challenge `γ` stays a scalar field element,
  so `winningSetFor … : Set F` and the soundness fraction `|Ω| / |F|` is over
  challenges regardless of `A`. The shared coding-theory layer (`epsCA`,
  `epsMCA`, `Lambda`, `interleavedCodeSet`, `minRelHammingDistCode`) is already
  alphabet-generic, so the same machinery serves both.
- **Honesty.** `bestProvableError` is what δ-relaxation round-by-round analyses
  can certify; the protocol's *true* security may exceed it. The leaderboard
  narrows **this** quantity, per §6.3.

Two bounds sandwich it (in `ℝ≥0∞`):

```
   2^(-Y)  ≤   bestProvableError p   ≤   2^(-X)
 (attack)      (δ-swept frontier)      (provable)
```

## How to submit

A submission is an *inhabitant* of one of two structures at a fixed parameter
point (e.g. `koalaIRS` or `koalaFRS`):

```lean
open ToyProblem

-- "We can prove ≥ 70 bits of security."
def myLowerBound : SecurityLowerBound koalaIRS where
  bits  := 70
  proof := by
    -- show  bestProvableError koalaIRS ≤ ↑((2 : ℝ≥0) ^ (-(70 : ℝ)))
    sorry

-- "No δ-relaxation analysis can prove > 110 bits."
def myAttack : SecurityUpperBound koalaIRS where
  bits  := 110
  proof := by
    -- show  ↑((2 : ℝ≥0) ^ (-(110 : ℝ))) ≤ bestProvableError koalaIRS
    sorry
```

**Lower entry (raise X).** Pick your δ, then:

1. `bestProvableError_le` reduces the goal to bounding the convex combination
   `(1-δ)^t + winningSetSoundness koalaIRS.enc δ · (1 - (1-δ)^t) ≤ 2^(-bits)`;
2. bound the `winningSetSoundness` term via the proven L6.10 bridge
   `winningSetSoundness_le_epsMCA_add` (`winningSetSoundness ≤ ε_mca + |Λ|/|F|`)
   plus your `ε_mca`/list-size analysis — a tighter Phase-1 `MCALowerWitness`
   feeds in here;
3. bound the spot-check term `(1-δ)^t` numerically.

**Upper entry (lower Y).** Use `le_bestProvableError` to reduce to flooring the
convex combination at *every* admissible δ (it dominates both terms):

- for large δ, floor `winningSetSoundness` via the two **proven, axiom-clean
  hooks**
  - `epsCA_le_winningSetSoundness` (Lemma 6.13): `ε_ca(C,δ) ≤ winningSetSoundness enc δ`,
  - `listDecoding_le_winningSetSoundness` (Lemma 6.12):
    `N/(|F|+2N) ≤ winningSetSoundness enc δ` with `N = |Λ(C^{≡2},δ)|`,

  so a numeric `ε_ca` or list-size lower bound plugs straight in;
- for small δ, the spot-check term `(1-δ)^t ≥ (1-δ₀)^t` floors the combination
  directly.

Notes:

- `bits : ℝ` (not `ℕ`) because the security level *is* `-log₂(error)`, a real
  for any error in `(0,1)` — ABF26's own §6.3 figures are fractional (the
  interleaved attack is `2^(-116.49)`, the spot-check `(1/√2+η)^128 ≈ 2^(-64.00)`).
- `(2 : ℝ≥0) ^ (-bits)` is `NNReal.rpow` (real exponent), coerced into `ℝ≥0∞`:
  `bestProvableError` lives in `ℝ≥0∞` so that a degenerate parameter point with
  an *empty* admissible δ-range gives `⊤` (the conservative direction). In `ℝ≥0`
  the binder infimum collapses to `0` on empty inner sets, making every lower
  bound trivially inhabitable (2026-06-10 review finding C1, fixed).
- A better lower-bound submission *raises* `X`; a better attack *lowers* `Y`.

## The metric

```lean
securityGap (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) : ℝ
  := hi.bits - lo.bits
```

This is the scalar contestants minimise. It is always `≥ 0`:
`SecurityLowerBound.bits_le_of` proves `lo.bits ≤ hi.bits` by pure transitivity
through the common scalar (`2^(-hi.bits) ≤ bestProvableError ≤ 2^(-lo.bits)` and
the strict antitonicity of `x ↦ 2^(-x)`), and `securityGap_nonneg` packages it.
Both are **axiom-clean** (`#print axioms` shows only `propext`/`Classical.choice`/
`Quot.sound`, no `sorryAx`) — the honesty of the metric does not depend on any
owed §6 proof.

## Current anchors

The carrier is the genuine KoalaBear *sextic* extension `KoalaSextic =
GaloisField (2^31 − 2^24 + 1) 6` (`|F| = q^6 ≈ 2^186`, large enough for the
`[2^(-117), 2^(-64)]` window to be representable). `koalaEnc` is a real
degree-`< 2` Reed–Solomon encoder on `4` points (`ι = Fin 4`, `k = 2`,
realised rate `ρ = k/|ι| = 1/2`), with `koalaEnc_injective` proven sorry-free.

### Interleaved Reed–Solomon — `koalaIRS` (`A = F`, `t = 128`)

| Anchor | `bits` | Basis |
|---|---|---|
| `arklib_lowerBound_irs_t128 : SecurityLowerBound koalaIRS` | **63.99** | ABF26 Lemmas 6.10 / 6.6 / 6.8 at `δ = 3/10`; full derivation reduced to one owed bound `ε_mca(C,3/10) + |Λ|/|F| ≤ 2^(-65)` |
| `listDecoding_upperBound_attack : SecurityUpperBound koalaIRS` | **117** | ABF26 Lemma 6.12 + Elias/[KKH26]; full derivation, band-split at `δ* = 117/250` (sorry-free spot-check `(133/250)^128 ≥ 2^(-117)` for small δ; proven L6.12 hook + owed list-size bound for large δ) |

so `securityGap = 117 − 63.99 = 53.01` (`securityGap_koalaIRS_anchors`).

- **The connective tissue is proven; only the coding-theory numerics are owed.**
  Both anchors are *full formalized reductions* (not opaque `sorry`s): the
  δ-window admissibility (`koalaIRS_minRelDist = 3/4`), the spot-check integer
  inequalities (`koala_spotcheck`, `koala_spotcheck_lb`), the L6.10 bridge, and
  the proven L6.12/L6.13 hooks are all axiom-clean. What remains `sorryAx` is
  exactly the external `ε_mca`/`ε_ca`/`Λ` bounds (BCHKS25/ACFY25/KKH26) — closing
  them means formalizing the prize's own coding theory, not session-level work
  (axiom-clean is infeasible *by design*: the Johnson RS bound is vacuous at the
  concrete `n = 4`).
- **Honest rounding** (2026-06-10 review): the X route certifies `≈ 2^(-63.9998)`
  — the paper notes `(1/√2+η)^128 > 2^(-64)` strictly, so `64.00` is unreachable
  and the anchor is `63.99`. The Y side is a *ceiling* and rounds **up**: the
  certified sweep floor is `≈ 2^(-116.6) < 2^(-116)` (the band `δ ∈ (0.46604,
  0.468)` is covered by neither branch at `116`), so the anchor is `117`.

### Folded Reed–Solomon — `koalaFRS` (`A = Fin s → F`, `s = 2^5`, `t = 128`)

[`Impl/FRS.lean`](../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean) instantiates
the *folded* code (a codeword symbol is a length-`s` tuple `Fin s → F`), the
`A = Fin s → F` case of the same machinery. Row: `s = 2^5 = 32`, evaluation
domain `|L| = 2^16`, message `k = 2^20`, rate `ρ = 1/2` (ABF26 §6.3.2, the
paper's worked example).

| Anchor | `bits` | Basis |
|---|---|---|
| `frsLowerBound : SecurityLowerBound koalaFRS` | **29.10** | §6.3.2 τ-subspace-design analysis, `tab:subspace-design-security-analysis`, `s = 2^5`, `r = 8` (`τ(r) = s·ρ/(s−r+1)`), at `δ = 7/48`. Now a **full reduction**: spot-check `(41/48)^128 ≤ 2^(−29)·(116/125)` (`koalaFRS_spotcheck`, integer fact `41^128·2^29·125 ≤ 116·48^128`) + the L6.10 bridge to `ε_mca + |Λ|/|F|` (one owed external admit), summed `≤ 2^(−29)·(933/1000) ≤ 2^(−29.10)` (`koalaFRS_combine`, integer fact `2·933^10 ≤ 10^30`). |
| `frsUpperBound_attack : SecurityUpperBound koalaFRS` | **128.01** | δ-sweep floor from the spot-check term alone: `⨅_δ (1−δ)^128 ≥ (1−δ_min)^128 ≈ 2^(−128.006)`, with the folded **MDS** relative distance `δ_min = 32769/65536 ≈ 0.50002`; rounds up to `128.01`. Now a **full reduction** via `le_bestProvableError` (drop the nonnegative `winningSetSoundness` term, floor `(1−δ)^128 ≥ (32767/65536)^128 ≥ 2^(−128.01)` by `koalaFRS_spotcheck_lb`, integer fact `256^100 ≤ 2·255^100`); the **only** owed external is the folded distance `koalaFRS_minRelDist`. (Stronger and *less owed* than the paper's per-`δ*` Elias point reading `2^(−127.63) = (1−0.499)^128` — that is not the sweep floor; no list-size bound enters.) |

so `securityGap_koalaFRS = 128.01 − 29.10 = 98.91`.

> **Round-down correction (`29.11 → 29.10`).** The spot-check term at the `r = 8`
> operating point is `(τ(9)+3/(2·8))^128 = (41/48)^128 = 2^(−29.1085)` *exactly*,
> and the convex combination always dominates it, so the strict provable ceiling
> is `2^(−29.1085)`. An honest **lower** bound must round the magnitude **down**:
> `29.10`, not the table's display-rounded `29.11` (`2^(−29.1085) > 2^(−29.11)`,
> so `29.11` is unprovable). This is the same discipline as the interleaved anchor
> (`64 → 63.99`); the gap is correspondingly `98.91`, not `98.90`.

- **Reading the gap honestly.** At a *fixed* `t = 128`, `s = 32` folding gives a
  *wider* gap than interleaving (`53.01`) — and for `s ≤ 2^4` *no* soundness is
  provable at all. This is faithful, not a defect: folding's payoff lives on axes
  the fixed-`t` δ-sweep does not capture — **larger folding closes the gap**
  (`s = 2^12`: provable `2^(-118.14)`, a `≈ 10`-bit gap) and **argument-size at
  enforced 128-bit security** (`s = 2^5` reaches `2^(-128.03)` at repetition
  `t = 563`, `r = 8`, `417.9 KiB`, `tab:subspace-design-128bit-security`), the
  metric on which folding genuinely beats interleaving.
- **Owed (cited, not fabricated).** Both anchors are now **full reductions** down
  to named externals (matching the `koalaIRS` anchors), not opaque sorries. The
  upper anchor owes a *single* external — the folded-Singleton distance
  `koalaFRS_minRelDist` (`δ_min = 32769/65536`; path (b): admitted because
  `ReedSolomon.Folded` has no minimum-distance lemma and the count rests on GR08
  admissibility of `koalaFoldω`). The lower anchor owes the τ-subspace-design
  `ε_mca` term (`≈ 2^(−166.8)` actual, capped `≤ 2^(−29)·(1/200)`), the FRS
  counterpart of the `koalaIRS` owed `ε_mca`. The spot-check integer leaves
  (`koalaFRS_spotcheck`, `koalaFRS_spotcheck_lb`, `koalaFRS_combine`) are
  **sorry-free**. `koalaFRSEnc_injective` is owed structurally:
  there is no in-tree `Admissible → injective` bridge for `frsEvalOnPoints`
  (`dim_frsCode` takes injectivity as a hypothesis), and concrete GR08
  admissibility needs multiplicative-order facts over the noncomputable
  `GaloisField` (the multiplicative analogue of `koalaDomain`'s additive
  argument). `koalaFRSDomain` is deliberately zero-free to keep admissibility a
  genuinely-owed, not provably-false, condition.
- **Protocol-reduction status.** `koalaFRS` is a leaderboard entry over the
  alphabet-generic soundness layer; it does *not* require the protocol
  *reduction* (`Spec/General.lean`, completeness) to be generalized to folded
  codewords — that is a separate, deferred follow-on gated by the pre-existing
  `simulateQ`/`OptionT` completeness frontier.

## Connection to the grand challenges (Phase 1)

The X side improves whenever `ε_mca` or the list size `|Λ|` shrinks. The Phase-1
framework in
[`ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean)
captures exactly this: a tighter `MCALowerWitness` (a verified `ε_mca(C,δ) ≤ ε*`)
shrinks the `ε_mca` term inside the L6.10 bridge
`winningSetSoundness_le_epsMCA_add`, which raises the provable lower bound `X`
and so narrows `securityGap`. Resolving the Grand MCA / List Decoding
Challenges feeds the leaderboard's lower side directly.

## Prior art

The only loose precedent is competition-style program verification (e.g.
VerifyThis), where entrants submit machine-checked artifacts judged against a
fixed specification. This leaderboard differs in that the *metric itself* — the
provable-vs-attack security gap — is a Lean scalar, and both "sides" are
adversarial inhabitants of opposing structures over one common soundness
quantity.
