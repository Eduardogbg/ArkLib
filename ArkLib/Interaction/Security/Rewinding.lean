/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Gomes
-/
import ArkLib.Interaction.Security.TranscriptForest
import ArkLib.Interaction.Security.TwoFactorRun
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Rewinding extractors and rewinding knowledge soundness

This file defines the rewinding lane of the `Interaction` security layer: prover-side
resumption, the rewinding-extractor carrier with a derived cost measure, and the
acceptance-conditioned rewinding knowledge-soundness notion of [AFK21, Def. 2].

## Prover-side resumption needs no new combinator

A rewinding extractor must fork a prover at a fixed prefix, feed a fresh challenge, and
continue. On this model that facility already exists structurally: a malicious prover is a
`Spec.Strategy.withRoles` value — a tree mirroring `Context : Spec` — and at a receiver
node (where the prover receives a challenge `x : X`) the strategy *is* a function
`(x : X) → m (continuation)` (`SyntaxOver.TwoParty.pairedSpec_focal_receiver`).
Re-applying that function to a fresh challenge is the prover-side rewind. `proverResumeAt`
packages this as the structural prefix-walk `StrategyOver.TwoParty.Focal.splitPrefix`: it
walks the focal strategy along a prefix protocol and returns, for each prefix transcript,
the prover's suffix strategy on the residual protocol. No extractor-managed environment or
prover-state monad is needed; the continuation is first-class in the strategy tree. The
verifier side of the same fork is `PublicCoinVerifier.replay`.

## The extractor carries a program, not a run or a cost

`Extractor.Rewinding` has a single field: the extractor's program on the two-factor spec
`unifSpec + unifSpec` (left factor: prover/verifier coins and computation; right factor:
extractor-owned draws — see `Security.TwoFactorRun`). Its probabilistic run is *derived*
from the program (`seedPushforward2` at the trivial table), and its expected query cost is
the genuine `expectedCost` of the unreified program at `CostModel.sumRight`. Deriving both
from one carried program is deliberate: a free `run` or cost field beside the program
would let one measure one program and execute another.

The cost unit follows [AFK21, Def. 2]: a query to the prover is a single extractor step,
prover-internal coins are none, and the expected-steps bound is stated per prover
(inside the "given input `x` and access to `P*`" scope), not as a supremum over the
prover carrier.

## The acceptance-conditioned notion

`rewindingKnowledgeSoundnessAccepting` bounds the *gap* between the honest run's
acceptance probability and the extractor's success probability:

`Pr[honest run accepts] − Pr[extractor succeeds] ≤ knowledgeError`.

Conditioning on acceptance is essential: bounding the unconditional extraction-failure
probability is unsatisfiable for an unrestricted prover (a never-accepting prover makes
extraction fail with probability one). The sanity lemmas at the end of the file witness
non-degeneracy in both directions.

The notion comes in two forms: `rewindingKnowledgeSoundnessAcceptingWith` pins the
extractor as a parameter, and `rewindingKnowledgeSoundnessAccepting` is its existential
closure. The pinned form is the one with algorithmic content — the existential admits a
non-executing `Classical.choose` witness that also satisfies the cost clause (cost `0`),
so anything downstream that runs the extractor must consume the pinned form.

## Main definitions

- `proverResumeAt` — prover-side resume-from-prefix.
- `AcceptPred` — the per-path acceptance convention on realized verifier outputs.
- `Extractor.Rewinding` — the extractor carrier (one two-factor program field), with
  derived `run` and `expectedQueriesAt`.
- `honestAcceptProb` / `extractSuccessProb` — the two sides of the knowledge gap.
- `rewindingKnowledgeSoundnessAcceptingWith` / `rewindingKnowledgeSoundnessAccepting` —
  the pinned notion and its existential closure.

## References

- [AFK21] Attema, Fehr, Klooß, *Fiat–Shamir Transformation of Multi-Round Interactive
  Proofs*, ePrint 2021/1377.
-/

universe u v w

namespace Interaction.Security

open Interaction Interaction.TwoParty
open scoped ENNReal

/-! ## Prover-side resumption -/

section ProverResume

variable {m : Type u → Type u} [Monad m]
  {Context : Spec.{u}} {roles : RoleDecoration Context}
  {OutputP : Spec.Transcript Context → Type u}

/-- Prover-side resume-from-prefix. The prover's protocol is presented as a prefix
protocol `preSpec` followed by a residual protocol `sufSpec tr₁` depending on the prefix
transcript. Given the prover's focal strategy over the whole `preSpec.append sufSpec`,
this walks it along the prefix and returns, for each prefix transcript `tr₁`, the prover's
suffix strategy on `sufSpec tr₁` — the prover's continuation at the fork.

This is definitionally the structural prefix-walk
`StrategyOver.TwoParty.Focal.splitPrefix`. At the first receiver node of the returned
suffix strategy, the strategy is literally a function `(x : X) → m (continuation)`
(`pairedSpec_focal_receiver`), so re-applying it to a fresh challenge yields the prover's
continuation at that fork — the rewind an extractor needs, with no extractor-managed
prover state. -/
def proverResumeAt
    {preSpec : Spec.{u}} {sufSpec : Spec.Transcript preSpec → Spec.{u}}
    {preRoles : RoleDecoration preSpec}
    {sufRoles : (tr₁ : Spec.Transcript preSpec) → RoleDecoration (sufSpec tr₁)}
    {Output : Spec.Transcript (preSpec.append sufSpec) → Type u}
    (prover : Spec.Strategy.withRoles m (preSpec.append sufSpec)
      (preRoles.append sufRoles) Output) :
    Spec.Strategy.withRoles m preSpec preRoles (fun tr₁ =>
      Spec.Strategy.withRoles m (sufSpec tr₁) (sufRoles tr₁)
        (fun tr₂ => Output (PFunctor.FreeM.Path.append preSpec sufSpec tr₁ tr₂))) :=
  StrategyOver.TwoParty.Focal.splitPrefix prover

end ProverResume

/-! ## Acceptance convention -/

section Acceptance

variable {m : Type u → Type u}
  {SharedIn : Type v} {Context : SharedIn → Spec.{u}}
  {StmtIn : SharedIn → Type u}
  {StmtOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u}

/-- The acceptance convention on this carrier: a caller-supplied predicate on the
verifier's `StatementOut` along a realized transcript path. `execute`/`replay` produce
`StatementOut`-valued outputs and the model has no built-in `Bool`/`OptionT` acceptance,
so the convention is chosen at instantiation (e.g. `StmtOut = fun _ _ => Bool` with
`accept := (· = true)`).

This per-path predicate is the acceptance hook of the probabilistic notions below. It is
deliberately distinct from the forest-level `accept` of `TreeSpeciallySound`, which must
thread folded statement instances down the forest spine (see
`Security.TranscriptForest`). -/
abbrev AcceptPred (Context : SharedIn → Spec.{u}) (StmtIn : SharedIn → Type u)
    (StmtOut : (i : SharedIn) → Spec.Transcript (Context i) → Type u) : Type _ :=
  (i : SharedIn) → StmtIn i → (tr : Spec.Transcript (Context i)) → StmtOut i tr → Prop

end Acceptance

/-! ## The rewinding extractor and rewinding knowledge soundness -/

section Rewinding

-- The interaction monad is instantiated at VCVio's `ProbComp`, which lives at universe 0,
-- so the carrier here is pinned to `Spec.{0}` / `Type 0`.
variable
  {SharedIn : Type v} {Context : SharedIn → Spec.{0}}
  {Roles : (i : SharedIn) → RoleDecoration (Context i)}
  {StmtIn WitIn : SharedIn → Type}
  {StmtOut : (i : SharedIn) → Spec.Transcript (Context i) → Type}

/-- A rewinding extractor: black-box access to a malicious prover strategy and the
public-coin verifier, producing an `Option` witness. Resumption is structural — the prover
side is `proverResumeAt`, the verifier side is `PublicCoinVerifier.replay`.

The single field `runProg` is the extractor's program on the two-factor spec
`unifSpec + unifSpec`, separating randomness by ownership (left: prover/verifier coins and
computation; right: extractor-owned draws). The probabilistic run and the expected query
cost are both *derived* from this one program (`Extractor.Rewinding.run` and
`Extractor.Rewinding.expectedQueriesAt` below), which ties the measured program to the
executed one. -/
structure Extractor.Rewinding
    (verifier : PublicCoinVerifier ProbComp SharedIn Context Roles StmtIn StmtOut) where
  /-- The extractor's two-factor program against a malicious prover strategy. Left-factor
  queries carry prover/verifier coins and computation (cost `0`); right-factor queries are
  the extractor-owned draws (cost `1`). -/
  runProg : (i : SharedIn) → StmtIn i →
        (prover : Spec.Strategy.withRoles ProbComp (Context i) (Roles i)
                    (fun tr => HonestProverOutput (StmtOut i tr) (WitIn i))) →
        OracleComp (unifSpec + unifSpec) (Option (WitIn i))

/-- The extractor's `ProbComp` run, derived from the two-factor program: the reification
`seedPushforward2` at the trivial table `(fun _ => 0, [])`, under which the seed prefix is
`pure ∅` and every query of either factor falls through to exactly one fresh uniform
query. Deriving `run` — rather than carrying it as a second field — ties the measured
program to the executed one. -/
noncomputable def Extractor.Rewinding.run
    {verifier : PublicCoinVerifier ProbComp SharedIn Context Roles StmtIn StmtOut}
    (E : Extractor.Rewinding (WitIn := WitIn) verifier)
    (i : SharedIn) (stmt : StmtIn i)
    (prover : Spec.Strategy.withRoles ProbComp (Context i) (Roles i)
                (fun tr => HonestProverOutput (StmtOut i tr) (WitIn i))) :
    ProbComp (Option (WitIn i)) :=
  seedPushforward2 (fun _ => 0) [] (E.runProg i stmt prover)

/-- The extractor's expected query cost against a fixed prover: the `expectedCost` of the
unreified two-factor program at the right-factor unit `CostModel.sumRight` — each
extractor-owned draw costs `1`, prover/verifier-side coins and computation ride for free.
This is the [AFK21, Def. 2] unit, stated per prover as in the paper (not as a supremum
over the prover carrier, which is unbounded over arbitrary `ProbComp` provers). -/
noncomputable def Extractor.Rewinding.expectedQueriesAt
    {verifier : PublicCoinVerifier ProbComp SharedIn Context Roles StmtIn StmtOut}
    (E : Extractor.Rewinding (WitIn := WitIn) verifier)
    (i : SharedIn) (stmt : StmtIn i)
    (prover : Spec.Strategy.withRoles ProbComp (Context i) (Roles i)
                (fun tr => HonestProverOutput (StmtOut i tr) (WitIn i))) : ℝ≥0∞ :=
  expectedCost (E.runProg i stmt prover) CostModel.sumRight (fun n => (n : ℝ≥0∞))

/-! ### The acceptance-conditioned notion -/

/-- The honest-run acceptance probability. Run the prover strategy against the verifier
via `Verifier.run` (the whole-protocol runner of `Interaction.Reduction`), then read the
`accept` predicate off the realized `(transcript, verifier output)` path. The prover
output component is discarded. -/
noncomputable def honestAcceptProb
    (verifier : PublicCoinVerifier ProbComp SharedIn Context Roles StmtIn StmtOut)
    (accept : AcceptPred Context StmtIn StmtOut)
    (i : SharedIn) (stmt : StmtIn i)
    (prover : Spec.Strategy.withRoles ProbComp (Context i) (Roles i)
                (fun tr => HonestProverOutput (StmtOut i tr) (WitIn i))) : ℝ≥0∞ :=
  Pr[ (fun (z : (tr : Spec.Transcript (Context i)) ×
                 HonestProverOutput (StmtOut i tr) (WitIn i) × StmtOut i tr) =>
        accept i stmt z.1 z.2.2)
      | Verifier.run verifier.toVerifier i stmt prover ]

/-- The extractor's success probability: the probability that `E.run` returns an
in-relation witness. -/
noncomputable def extractSuccessProb
    {verifier : PublicCoinVerifier ProbComp SharedIn Context Roles StmtIn StmtOut}
    (relIn : (i : SharedIn) → StmtIn i → WitIn i → Prop)
    (E : Extractor.Rewinding (WitIn := WitIn) verifier)
    (i : SharedIn) (stmt : StmtIn i)
    (prover : Spec.Strategy.withRoles ProbComp (Context i) (Roles i)
                (fun tr => HonestProverOutput (StmtOut i tr) (WitIn i))) : ℝ≥0∞ :=
  Pr[ (fun (ow : Option (WitIn i)) => ∃ w, ow = some w ∧ relIn i stmt w)
      | E.run i stmt prover ]

/-- Acceptance-conditioned rewinding knowledge soundness, existential form: some rewinding
extractor satisfies, for every input, statement, and prover, the per-prover expected-cost
bound together with the knowledge gap

`honestAcceptProb − extractSuccessProb ≤ knowledgeError`.

This is the [AFK21, Def. 2] shape. Conditioning on acceptance is what makes the notion
satisfiable: a never-accepting prover gives `honestAcceptProb = 0`, so the gap is `0`
regardless of the extractor, while for an always-accepting prover the gap is exactly the
extraction-failure probability. The cost conjunct sits inside the prover quantifier —
the paper's own placement — rather than as a supremum over the prover carrier.

Prefer the pinned form `rewindingKnowledgeSoundnessAcceptingWith` for anything that runs
the extractor; see the module docstring. -/
def rewindingKnowledgeSoundnessAccepting
    (relIn : (i : SharedIn) → StmtIn i → WitIn i → Prop)
    (verifier : PublicCoinVerifier ProbComp SharedIn Context Roles StmtIn StmtOut)
    (accept : AcceptPred Context StmtIn StmtOut)
    (polyBound knowledgeError : ℝ≥0∞) : Prop :=
  ∃ E : Extractor.Rewinding verifier,
    ∀ (i : SharedIn) (stmt : StmtIn i)
      (prover : Spec.Strategy.withRoles ProbComp (Context i) (Roles i)
                  (fun tr => HonestProverOutput (StmtOut i tr) (WitIn i))),
      E.expectedQueriesAt i stmt prover ≤ polyBound ∧
      honestAcceptProb verifier accept i stmt prover
          - extractSuccessProb relIn E i stmt prover
        ≤ knowledgeError

/-- Acceptance-conditioned rewinding knowledge soundness with a *pinned* extractor: the
same body as `rewindingKnowledgeSoundnessAccepting`, with the extractor a parameter
rather than existentially quantified.

This is the form with algorithmic content: it asserts that the concrete extractor `E`
satisfies the cost and gap bounds for every prover, so the degenerate non-executing
witness (`Classical.choose` of the gap statement, cost `0`) that closes the existential
form cannot arise. It matches [AFK21, Def. 2] read as "*this* black-box rewinding
extractor has an expected-query bound and an extraction gap `≤ knowledgeError`" — with
the caveat that the notion itself does not force black-box access (`runProg` receives the
prover as a plain argument); black-box behaviour is certified per pinned extractor by a
separate factoring lemma. Implies the existential form by `⟨E, ·⟩`
(`rewindingKnowledgeSoundnessAccepting_of_with`). -/
def rewindingKnowledgeSoundnessAcceptingWith
    (relIn : (i : SharedIn) → StmtIn i → WitIn i → Prop)
    (verifier : PublicCoinVerifier ProbComp SharedIn Context Roles StmtIn StmtOut)
    (E : Extractor.Rewinding (WitIn := WitIn) verifier)
    (accept : AcceptPred Context StmtIn StmtOut)
    (polyBound knowledgeError : ℝ≥0∞) : Prop :=
  ∀ (i : SharedIn) (stmt : StmtIn i)
    (prover : Spec.Strategy.withRoles ProbComp (Context i) (Roles i)
                (fun tr => HonestProverOutput (StmtOut i tr) (WitIn i))),
    E.expectedQueriesAt i stmt prover ≤ polyBound ∧
    honestAcceptProb verifier accept i stmt prover
        - extractSuccessProb relIn E i stmt prover
      ≤ knowledgeError

/-- The pinned form implies the existential form, witnessed by the pinned extractor. The
converse fails: the existential form admits a non-executing `Classical.choose` witness,
which the pinned form excludes. -/
theorem rewindingKnowledgeSoundnessAccepting_of_with
    (relIn : (i : SharedIn) → StmtIn i → WitIn i → Prop)
    (verifier : PublicCoinVerifier ProbComp SharedIn Context Roles StmtIn StmtOut)
    (E : Extractor.Rewinding (WitIn := WitIn) verifier)
    (accept : AcceptPred Context StmtIn StmtOut)
    (polyBound knowledgeError : ℝ≥0∞)
    (h : rewindingKnowledgeSoundnessAcceptingWith relIn verifier E accept
          polyBound knowledgeError) :
    rewindingKnowledgeSoundnessAccepting relIn verifier accept polyBound knowledgeError :=
  ⟨E, h⟩

/-! ### Non-degeneracy sanity lemmas

These witness that the acceptance event in `rewindingKnowledgeSoundnessAccepting` is
neither vacuous nor trivially unsatisfiable. -/

/-- If the prover's honest run never produces an accepting transcript, then
`honestAcceptProb = 0` — so the knowledge gap is `≤ 0 ≤ knowledgeError` regardless of the
extractor. (An unconditional failure bound would instead be forced to `1` here, which is
why the notion conditions on acceptance.) -/
theorem honestAcceptProb_eq_zero_of_neverAccept
    (verifier : PublicCoinVerifier ProbComp SharedIn Context Roles StmtIn StmtOut)
    (accept : AcceptPred Context StmtIn StmtOut)
    (i : SharedIn) (stmt : StmtIn i)
    (prover : Spec.Strategy.withRoles ProbComp (Context i) (Roles i)
                (fun tr => HonestProverOutput (StmtOut i tr) (WitIn i)))
    (hreject : ∀ z : (tr : Spec.Transcript (Context i)) ×
                 HonestProverOutput (StmtOut i tr) (WitIn i) × StmtOut i tr,
                 z ∈ support (Verifier.run verifier.toVerifier i stmt prover) →
                 ¬ accept i stmt z.1 z.2.2) :
    honestAcceptProb verifier accept i stmt prover = 0 := by
  unfold honestAcceptProb
  rw [probEvent_eq_zero_iff]
  intro z hz hacc
  exact hreject z hz hacc

/-- If the prover's honest run produces an accepting transcript on some realized path of
positive mass, then `honestAcceptProb > 0` — the acceptance event is genuinely
non-trivial. -/
theorem honestAcceptProb_pos_of_accepts
    (verifier : PublicCoinVerifier ProbComp SharedIn Context Roles StmtIn StmtOut)
    (accept : AcceptPred Context StmtIn StmtOut)
    (i : SharedIn) (stmt : StmtIn i)
    (prover : Spec.Strategy.withRoles ProbComp (Context i) (Roles i)
                (fun tr => HonestProverOutput (StmtOut i tr) (WitIn i)))
    (z : (tr : Spec.Transcript (Context i)) ×
           HonestProverOutput (StmtOut i tr) (WitIn i) × StmtOut i tr)
    (hz : z ∈ support (Verifier.run verifier.toVerifier i stmt prover))
    (hacc : accept i stmt z.1 z.2.2) :
    0 < honestAcceptProb verifier accept i stmt prover := by
  unfold honestAcceptProb
  rw [pos_iff_ne_zero]
  intro hzero
  rw [probEvent_eq_zero_iff] at hzero
  exact hzero z hz hacc

/-- Satisfiability witness: if some extractor succeeds with probability `1` for every
prover and meets the cost bound, then `rewindingKnowledgeSoundnessAccepting` holds for any
`knowledgeError`, since `honestAcceptProb ≤ 1 = extractSuccessProb` makes the gap `0`. -/
theorem rewindingKnowledgeSoundnessAccepting_of_alwaysExtract
    (relIn : (i : SharedIn) → StmtIn i → WitIn i → Prop)
    (verifier : PublicCoinVerifier ProbComp SharedIn Context Roles StmtIn StmtOut)
    (accept : AcceptPred Context StmtIn StmtOut)
    (polyBound knowledgeError : ℝ≥0∞)
    (E : Extractor.Rewinding (WitIn := WitIn) verifier)
    (hcost : ∀ (i : SharedIn) (stmt : StmtIn i)
      (prover : Spec.Strategy.withRoles ProbComp (Context i) (Roles i)
                  (fun tr => HonestProverOutput (StmtOut i tr) (WitIn i))),
      E.expectedQueriesAt i stmt prover ≤ polyBound)
    (hextract : ∀ (i : SharedIn) (stmt : StmtIn i)
      (prover : Spec.Strategy.withRoles ProbComp (Context i) (Roles i)
                  (fun tr => HonestProverOutput (StmtOut i tr) (WitIn i))),
      extractSuccessProb relIn E i stmt prover = 1) :
    rewindingKnowledgeSoundnessAccepting relIn verifier accept polyBound knowledgeError := by
  refine ⟨E, fun i stmt prover => ⟨hcost i stmt prover, ?_⟩⟩
  rw [hextract i stmt prover]
  -- honestAcceptProb ≤ 1, so honestAcceptProb − 1 = 0 ≤ knowledgeError.
  have h1 : honestAcceptProb verifier accept i stmt prover ≤ 1 := by
    unfold honestAcceptProb; exact probEvent_le_one
  rw [tsub_eq_zero_of_le h1]
  exact bot_le

end Rewinding

end Interaction.Security
