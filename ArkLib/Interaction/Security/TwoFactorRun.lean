/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Gomes
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.QueryTracking.SeededOracle
import VCVio.OracleComp.QueryTracking.CostModel
import VCVio.OracleComp.Constructions.GenerateSeed
import VCVio.OracleComp.SimSemantics.Append

/-!
# Two-factor runs for rewinding extractors

A rewinding extractor (`Security.Rewinding`) carries its program on the two-factor spec
`unifSpec + unifSpec`, separating its randomness by ownership:

- the *left* factor carries prover/verifier-side coins and computation;
- the *right* factor carries the extractor-owned draws.

The split is what makes the extractor's cost measurable without over-counting: following
[AFK21, Def. 2], a query to the prover is a single extractor step, while prover-internal
coins are not extractor work at all. `CostModel.sumRight` charges exactly the right factor.

This file provides the seeded reification of a two-factor program to a single-`unifSpec`
`ProbComp` — run under a left-factor coin tape, with right-factor queries answered by fresh
uniform draws (`sumHandler`, `seedRun2`, `runUnderSeed2`, `seedPushforward2`) — and the
right-factor cost model. `Extractor.Rewinding` derives its probabilistic run from its
program via `seedPushforward2` and measures the expected query cost of the unreified
program under `CostModel.sumRight`.

## References

- [AFK21] Attema, Fehr, Klooß, *Fiat–Shamir Transformation of Multi-Round Interactive
  Proofs*, ePrint 2021/1377.
-/

open OracleSpec OracleComp

/-- The right-factor unit cost model on a sum spec: a left-summand query costs `0`, a
right-summand query costs `1`. On the extractor's two-factor carrier this charges exactly
the extractor-owned draws and lets the prover/verifier coins ride for free — the
[AFK21, Def. 2] unit, where a query to the prover is a single extractor step and
prover-internal coins are none. -/
def CostModel.sumRight {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} :
    CostModel (spec₁ + spec₂) ℕ where
  queryCost := Sum.elim (fun _ => 0) (fun _ => 1)

namespace Interaction.Security

variable {α : Type}

/-- The two-factor seeded run handler over `unifSpec + unifSpec`. The left factor is the
`seededOracle` (reads and advances the tape `QuerySeed unifSpec`, falling back to a fresh
uniform draw when exhausted); the right factor is the `id` handler lifted into the same
`StateT (QuerySeed unifSpec) (OracleComp unifSpec)` target, which ignores the tape and
always issues a fresh uniform `unifSpec` query. -/
noncomputable def sumHandler :
    QueryImpl (unifSpec + unifSpec)
      (StateT (QuerySeed unifSpec) (OracleComp unifSpec)) :=
  (seededOracle (spec := unifSpec)) +
    (QueryImpl.id' unifSpec).liftTarget (StateT (QuerySeed unifSpec) (OracleComp unifSpec))

/-- The result-and-residual-tape two-factor run: runs `oa` under the two-factor handler
from tape `s`, returning the result together with the advanced left-factor tape. -/
noncomputable def seedRun2 (oa : OracleComp (unifSpec + unifSpec) α) (s : QuerySeed unifSpec) :
    OracleComp unifSpec (α × QuerySeed unifSpec) :=
  (simulateQ sumHandler oa).run s

/-- The two-factor seeded run (first projection of `seedRun2`). Seeds only the left (coin)
factor; the right (draw) factor is answered fresh-uniform. -/
noncomputable def runUnderSeed2 (oa : OracleComp (unifSpec + unifSpec) α) (s : QuerySeed unifSpec) :
    OracleComp unifSpec α :=
  Prod.fst <$> seedRun2 oa s

/-- The two-factor uniform-seed pushforward: pre-sample a uniform left-factor tape and run
`oa` under `runUnderSeed2`, giving a genuine `ProbComp α`. At the trivial table
`(fun _ => 0, [])` the seed prefix is `pure ∅` (by `generateSeed`'s defining equation), so
every query of either factor falls through to exactly one fresh uniform query — this is the
canonical reification used by `Extractor.Rewinding.run`. -/
noncomputable def seedPushforward2 (qc : ℕ → ℕ) (js : List ℕ)
    (oa : OracleComp (unifSpec + unifSpec) α) : ProbComp α := do
  let s ← generateSeed unifSpec qc js
  runUnderSeed2 oa s

end Interaction.Security
