# Proximity-Prize "bits of security" leaderboard

A machine-checked leaderboard for the soundness of the ABF26 §6 toy protocol. It
turns the Ethereum Foundation **Proximity Prize** (proximityprize.org, $1M)
question — *how big is the gap between what we can prove and the best known
attack?* — into a single Lean scalar that contestants minimise.

- **Code:** [`ArkLib/ProofSystem/ToyProblem/Leaderboard.lean`](../../ArkLib/ProofSystem/ToyProblem/Leaderboard.lean)
- **Paper:** Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated
  Agreement* (eprint 2026/680), §6.2 (Lemma 6.8), §6.4 (Lemmas 6.10, 6.12,
  6.13), §6.3 ("Knowledge soundness upperbound" / "Soundness lowerbound"
  parheads + Tables 2–5). The attack side is also Fenzi–Sanso, eprint
  2025/2197 (Construction 4.2 = C6.2, Lemma 4.4 ≈ Lemma 6.12) and the
  [KKH26]-backed list-size tables.

## The one quantity both sides bound: a δ-swept frontier

The two leaderboard sides must bound the **same** scalar or the gap between
them is meaningless. ABF26's §6.3 analysis is a *sweep over the proximity
parameter δ*: any round-by-round analysis of Construction 6.2 picks an
admissible `δ ∈ (0, δ_min(C))` (the L6.8/L6.10 range), after which round 1's
true error is `winningSetSoundness enc δ` (Definition 6.11 — the paper says
the simplified IOR's soundness error "is exactly" this) and round 2's is the
spot-check `(1-δ)^t`. The common quantity is the best error provable by *any*
such analysis:

```
bestProvableError p
  = ⨅ δ ∈ (0, δ_min(C)),  max (winningSetSoundness p.enc δ) ((1-δ)^t)
```

Key design points:

- **δ is swept, not pinned.** The two sides certify their bounds at
  *different* δ — the provable side optimizes near `δ = 1 − √ρ − η` (Johnson
  regime, `.tex` 2798–2825), the attack side works near `δ* = 0.468`
  (`tab:elias-lowerbound-thresholds`, `.tex` ~2925). A single shared δ cannot
  represent the paper's frontier (at the attack's δ the provable side's MCA
  bound is unavailable; at the provable side's δ the attack is far weaker).
  The `⨅` makes both legitimate bounds on the same scalar.
- **Pinned encoding.** All Definition-6.11 objects use the fixed-encoding
  relations `relaxedRelationFor enc` / `winningSetFor enc` (the paper's code
  *is* its injective encoding `C : F^k → F^n`). `ToyParams` carries
  `enc` + `enc_injective` and derives the code as `p.code = Set.range p.enc`.
  The earlier existential-encoding relations (under which the linear
  constraint is reparameterisable and the supremum collapses) were deleted.
- **Honesty.** `bestProvableError` is what δ-relaxation round-by-round
  analyses can certify; the protocol's *true* security may exceed it. The
  leaderboard narrows **this** quantity, per §6.3.

Two bounds sandwich it:

```
   2^(-Y)  ≤   bestProvableError p   ≤   2^(-X)
 (attack)      (δ-swept frontier)      (provable)
```

## How to submit

A submission is an *inhabitant* of one of two structures, both at the fixed
anchor parameter point `koalaIRS : ToyParams`:

```lean
open ToyProblem

-- "We can prove ≥ 70 bits of security."
def myLowerBound : SecurityLowerBound koalaIRS where
  bits  := 70
  proof := by
    -- show  bestProvableError koalaIRS ≤ (2 : ℝ≥0) ^ (-(70 : ℝ))
    sorry

-- "No δ-relaxation analysis can prove > 110 bits."
def myAttack : SecurityUpperBound koalaIRS where
  bits  := 110
  proof := by
    -- show  (2 : ℝ≥0) ^ (-(110 : ℝ)) ≤ bestProvableError koalaIRS
    sorry
```

**Lower entry (raise X).** Pick your δ, then:

1. `bestProvableError_le` reduces the goal to
   `max (winningSetSoundness koalaIRS.enc δ) ((1-δ)^t) ≤ 2^(-bits)`;
2. bound the first branch via the L6.10 bridge
   `winningSetSoundness_le_epsMCA_add` (`winningSetSoundness ≤ ε_mca + |Λ|/|F|`)
   plus your `ε_mca`/list-size analysis — a tighter Phase-1 `MCALowerWitness`
   feeds in here;
3. bound the spot-check branch `(1-δ)^t` numerically.

**Upper entry (lower Y).** You must floor the `max` at *every* admissible δ:

- for large δ, exhibit an attack on `winningSetSoundness` — the two **proven,
  axiom-clean hooks** are
  - `epsCA_le_winningSetSoundness` (Lemma 6.13): `ε_ca(C,δ) ≤ winningSetSoundness enc δ`,
  - `listDecoding_le_winningSetSoundness` (Lemma 6.12):
    `N/(|F|+2N) ≤ winningSetSoundness enc δ` with `N = |Λ(C^{≡2},δ)|`,

  so a numeric `ε_ca` or list-size lower bound plugs straight in;
- for small δ, the spot-check term `(1-δ)^t ≥ (1-δ₀)^t` floors the max
  directly.

Notes:

- `bits : ℝ` (not `ℕ`) because the security level *is* `-log₂(error)`, a real
  for any error in `(0,1)` — ABF26's own §6.3 figures are fractional (the
  attack is `2^(-116.49)`, the MCA branch `≈ 2^(-71.5)`).
- `(2 : ℝ≥0) ^ (-bits)` is `NNReal.rpow` (real exponent).
- A better lower-bound submission *raises* `X`; a better attack *lowers* `Y`.

## The metric

```lean
securityGap (lo : SecurityLowerBound p) (hi : SecurityUpperBound p) : ℝ
  := hi.bits - lo.bits
```

This is the scalar contestants minimise. It is always `≥ 0`:
`SecurityLowerBound.bits_le_of` proves `lo.bits ≤ hi.bits` by pure
transitivity through the common scalar
(`2^(-hi.bits) ≤ bestProvableError ≤ 2^(-lo.bits)` and the strict antitonicity
of `x ↦ 2^(-x)`), and `securityGap_nonneg` packages it. Both are
**axiom-clean** (`#print axioms` shows only `propext`/`Classical.choice`/
`Quot.sound`, no `sorryAx`) — the honesty of the metric does not depend on any
owed §6 proof.

## Current anchors (the 64 / 116 frontier)

At the KoalaBear-sextic regime (`q = 2^31 - 2^24 + 1`, sextic extension,
`ρ = 1/2`, `t = 128`):

| Anchor | `bits` | Basis |
|---|---|---|
| `arklib_lowerBound_irs_t128 : SecurityLowerBound koalaIRS` | ≈ **64** | ABF26 Lemmas 6.10 / 6.6 / 6.8 at `δ = 1 − 1/√2 − η`, `η ≈ 2^-18…2^-21` (`.tex` 2798–2825, `tab:interleaved-security-analysis`; spot-check-limited, MCA branch ≈ `2^-71.5`) |
| `listDecoding_upperBound_attack : SecurityUpperBound koalaIRS` | ≈ **116** | ABF26 Lemma 6.12 + Elias/[KKH26] at `δ* = 0.468` (`tab:elias-lowerbound-thresholds`, `2^-116.49`), spot-check floor `(0.532)^128 ≈ 2^-116.6` for `δ ≤ δ*` (cf. Fenzi–Sanso 2025/2197 Lemma 4.4) |

so `securityGap = 116 − 64 = 52` (the lemma `securityGap_koalaIRS_anchors`
evaluates this). Both anchors are `sorry`-tagged by design (`ABF26-§6.3.1` /
`ABF26-§6.3.1-lowerbound`) — the §6.3.1 numeric evaluations are Phase-5-owed.
Notes:

- **The attack→soundness chains are real.** Lemmas 6.12 and 6.13 are proven
  sorry-free and axiom-clean against the pinned relations
  (`simplified_iop_soundness_listDecoding_lb`, `simplified_iop_soundness_ca_lb`),
  and both are hosted on the leaderboard as the proven hooks
  `listDecoding_le_winningSetSoundness` / `epsCA_le_winningSetSoundness`.
  Only the Phase-5 *numerics* (and the genuine KoalaBear encoder) remain owed.
- The Y anchor's currently certified floor is `≈ 2^(-116.6)` (a ceiling of
  ≈116.5–116.6 bits); `bits := 116` is the paper's headline integer and owes
  the ≈0.5-bit sharpening to Phase 5 (flagged in the anchor's docstring).
- The anchor carrier is `GaloisField 2 128` (size `2^128`), a same-*order*
  stand-in for the `≈2^186`-element KoalaBear-sextic field, with an **opaque**
  placeholder encoding `koalaEnc` (injectivity is a tagged Phase-5 sorry). The
  large field is required for the `[2^(-117), 2^(-64)]` window to be
  representable, and opacity keeps `bestProvableError` irreducible so neither
  anchor is provably true or false. Phase 5 substitutes the genuine RS/IRS
  KoalaBear-sextic field and encoder.

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
