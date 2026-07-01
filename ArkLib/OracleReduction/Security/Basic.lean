/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Execution

/-!
  # Security Definitions for (Oracle) Reductions

  This file defines basic security notions for (oracle) reductions:

  - (Perfect) Completeness

  - (Straightline) (Knowledge) Soundness

  - (Honest-verifier) Zero-knowledge

  For each security notion, we provide a typeclass for it, so that security can be synthesized
  automatically with verified transformations.

  See other files in the same directory for more refined soundness notions (i.e. state-restoration,
  round-by-round, rewinding, etc.)
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  -- Note: `σ` may depend on the previous data, like `StmtIn`, `pSpec`, and so on
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited] : IsUniformSpec spec :=
  IsUniformSpec.ofFintypeInhabited spec

/-
TODO: the "right" factoring for the security definitions are the following:

- We have a two-layer interpretation approach: first, interpret the oracle queries into some monad
  `m` which admits a monad morphism into `PMF` (i.e. `HasEvalDist`); then we interpret the resulting
  monad into `PMF`.

  This does not preclude `m` from being the same oracle computation type, but more interesting
  possibilities are possible, such as `m = ReaderT ρ` for lazy sampling of the shared oracle.

  Another possibility: given `OracleInterface OStmt`, we have an interpretation map

  `interpOStmt : OracleComp (oSpec + [OStmt]ₒ) →ᵐ ReaderT OStmt (OracleComp oSpec)`

- Relations should be `Stmt → Wit → m Prop`, with `m` being the intermediate monad. When `m` is the
  result of `interpOStmt` above, for instance, we get `Stmt → Wit → OStmt → Prop`, which is what we
  want. Same for when we interpret `oSpec` into `Reader (QueryImpl oSpec Id)`; we then have
  `Stmt → Wit → QueryImpl oSpec Id → Prop`, which allows us to define relations that rely
  on the (randomly sampled, at the beginning) values of the shared oracle.
-/

namespace Reduction

section Completeness


/-- A reduction satisfies **completeness** with regards to:
  - an initialization function `init : ProbComp σ` for some ambient state `σ`,
  - a stateful query implementation `impl` (in terms of `StateT σ ProbComp`)
  for the shared oracles `oSpec`,
  - an input relation `relIn` and output relation `relOut` (represented as sets), and
  - an error `completenessError ≥ 0`,

  if for all valid statement-witness pair `(stmtIn, witIn) ∈ relIn`, the execution between the
  honest prover and the honest verifier will result in a tuple `((prvStmtOut, witOut), stmtOut)`
  such that

  - `(stmtOut, witOut) ∈ relOut`, (the output statement-witness pair is valid) and
  - `prvStmtOut = stmtOut`, (the output statements are the same from both prover and verifier)

  except with probability `completenessError`.
-/
def completeness (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (completenessError : ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  (stmtIn, witIn) ∈ relIn →
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      QueryImpl.addLift impl challengeQueryImpl
    Pr[fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
        ((stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut) | OptionT.mk do
          (simulateQ pImpl (reduction.run stmtIn witIn).run).run' (← init)] ≥ 1 - completenessError

/-- A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`. -/
def perfectCompleteness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  completeness init impl relIn relOut reduction 0

/-- Type class for completeness for a reduction -/
class IsComplete (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    where
  completenessError : ℝ≥0
  is_complete : completeness init impl relIn relOut reduction completenessError

/-- Type class for perfect completeness for a reduction -/
class IsPerfectComplete (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) where
  is_perfect_complete : perfectCompleteness init impl relIn relOut reduction

variable {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}

instance [reduction.IsPerfectComplete init impl relIn relOut] :
    IsComplete init impl relIn relOut reduction where
  completenessError := 0
  is_complete := IsPerfectComplete.is_perfect_complete

/-- If a reduction satisfies completeness with error `ε₁`, then it satisfies completeness with error
  `ε₂` for all `ε₂ ≥ ε₁`. -/
@[grind]
theorem completeness_error_mono {ε₁ ε₂ : ℝ≥0} (hε : ε₁ ≤ ε₂) :
      completeness init impl relIn relOut reduction ε₁ →
        completeness init impl relIn relOut reduction ε₂ := by
  intro h
  dsimp [completeness] at h ⊢
  intro stmtIn witIn hstmtIn
  have := h stmtIn witIn hstmtIn
  refine ge_trans this ?_
  exact tsub_le_tsub_left (by simp [hε]) 1

/-- If a reduction satisfies completeness with error `ε` for some relation `relIn`, then it
  satisfies completeness with error `ε` for any relation `relIn'` that is a subset of `relIn`. -/
@[simp, grind]
theorem completeness_relIn_mono {ε : ℝ≥0} {relIn' : Set (StmtIn × WitIn)}
    (hrelIn : relIn' ⊆ relIn) :
      completeness init impl relIn relOut reduction ε →
        completeness init impl relIn' relOut reduction ε := by
  intro h
  dsimp [completeness] at h ⊢
  intro stmtIn witIn hStmtIn
  exact h stmtIn witIn (hrelIn hStmtIn)

/-- If a reduction satisfies completeness with error `ε` for some relation `relIn`, then it
  satisfies completeness with error `ε` for any relation `relOut'` that is a superset of `relOut`.
-/

theorem completeness_relOut_mono {ε : ℝ≥0} {relOut' : Set (StmtOut × WitOut)}
    (hrelOut : relOut ⊆ relOut') :
      completeness init impl relIn relOut reduction ε →
        completeness init impl relIn relOut' reduction ε := by
  intro h stmtIn witIn hIn
  exact ge_trans (probEvent_mono fun _ _ ⟨h1, h2⟩ => ⟨hrelOut h1, h2⟩) (h stmtIn witIn hIn)

/-- Perfect completeness means that the probability of the reduction outputting a valid
  statement-witness pair is _exactly_ 1 (instead of at least `1 - 0`). -/
@[simp]
theorem perfectCompleteness_eq_prob_one :
    reduction.perfectCompleteness init impl relIn relOut ↔
    ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn →
      let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
        QueryImpl.addLift impl challengeQueryImpl
      Pr[fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
          ((stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut)
        | OptionT.mk do (simulateQ pImpl (reduction.run stmtIn witIn)).run' (← init)] = 1 := by
  simp only [perfectCompleteness, completeness, ENNReal.coe_zero, tsub_zero]
  exact forall_congr' fun _ => forall_congr' fun _ => imp_congr_right fun _ =>
    ⟨fun h => le_antisymm probEvent_le_one (ge_iff_le.mp h),
     fun h => ge_of_eq h⟩

-- /-- For a reduction without shared oracles (i.e. `oSpec = []ₒ`), perfect completeness occurs
--   when the reduction produces satisfying statement-witness pairs for all possible challenges. -/
-- theorem perfectCompleteness_forall_challenge [reduction.IsDeterministic] :
--       reduction.perfectCompleteness relIn relOut ↔
--         ∀ stmtIn witIn, relIn stmtIn witIn → ∀ chals : ∀ i, pSpec.Challenge i,
--           reduction.runWithChallenges stmtIn witIn chals = 1 := by

end Completeness

end Reduction

section Soundness

/-! We define 3 variants each of soundness and knowledge soundness:

  1. (Plain) soundness
  2. Knowledge soundness

  For adaptivity, we may want to seed the definition with a term
    `chooseStmtIn : OracleComp oSpec StmtIn`
  (though this is essentially the same as quantifying over all `stmtIn : StmtIn`).

  Note: all soundness definitions are really defined for the **verifier** only. The (honest)
prover does not feature into the definitions.
-/

namespace Extractor

/- We define different types of extractors here -/

variable (oSpec : OracleSpec ι) (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)

/-- A straightline, deterministic, non-oracle-querying extractor takes in the output witness, the
  initial statement, the IOR transcript, and the query logs from the prover and verifier, and
  returns a corresponding initial witness.

  Note that the extractor does not need to take in the output statement, since it can be derived
  via re-running the verifier on the initial statement, the transcript, and the verifier's query
  log.

  This form of extractor suffices for proving knowledge soundness of most hash-based IOPs.
-/
def Straightline :=
  StmtIn → -- input statement
  WitOut → -- output witness
  FullTranscript pSpec → -- reduction transcript
  QueryLog oSpec → -- prover's query log
  QueryLog oSpec → -- verifier's query log
  OptionT (OracleComp oSpec) WitIn -- input witness

end Extractor

namespace Verifier

/-- A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input
  language `langIn : Set StmtIn` and output language `langOut : Set StmtOut` if:
  - for all (malicious) provers with arbitrary types for `WitIn`, `WitOut`,
  - for all arbitrary `witIn`,
  - for all input statement `stmtIn ∉ langIn`,

  the execution between the prover and the honest verifier will result in an output statement
  `stmtOut` that is in `langOut` is at most `soundnessError`.

  (technical note: since execution may fail, this is _not_ equivalent to saying that
  `stmtOut ∉ langOut` with probability at least `1 - soundnessError`)
-/
def soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  ∀ WitIn WitOut : Type,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ stmtIn ∉ langIn,
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    letI reduction := Reduction.mk prover verifier
    Pr[fun ⟨_, stmtOut⟩ => stmtOut ∈ langOut | OptionT.mk do
      (simulateQ pImpl (reduction.run stmtIn witIn).run).run' (← init)] ≤ soundnessError

/-- Type class for soundness for a verifier -/
class IsSound (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  soundnessError : ℝ≥0
  is_sound : soundness init impl langIn langOut verifier soundnessError

-- How would one define a rewinding extractor? It should have oracle access to the prover's
-- functions (receive challenges and send messages), and be able to observe & simulate the prover's
-- oracle queries
#check Reduction.runWithLog
/-- A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and
  with respect to input relation `relIn` and output relation `relOut` if:
  - there exists a straightline extractor `E`, such that
  - for all input statement `stmtIn`, witness `witIn`, and (malicious) prover `prover`,
  - if the execution with the honest verifier results in a pair `(stmtOut, witOut)`,

  then the probability that `(stmtOut, witOut)` is valid and yet the extractor fails to produce
  a witness `witIn'` such that `(stmtIn, witIn')` is valid is at most `knowledgeError`.

  Implementation note: the extractor returns an `OptionT` computation, so it may fail. We run
  this `OptionT` layer explicitly (via `.run`) and keep the resulting `Option WitIn` in the
  game's output, so that extractor failure counts as a "bad" event (the adversary wins).

  This is essential for the definition to be meaningful: if instead the extractor were bound
  inside the surrounding `OptionT` computation, its failure would contribute to the failure
  mass of the whole game, which `probEvent` excludes (it only measures `some` outputs). The
  always-failing extractor `fun _ _ _ _ _ => failure` would then drive the game's event
  probability to `0`, vacuously discharging knowledge soundness (at error `0`!) for any
  verifier and any relations.

  In contrast, failures of the reduction execution itself (e.g. the verifier aborting) are
  still excluded from the event, matching the convention for (plain) soundness: a run in which
  the verifier does not accept imposes no obligation on the extractor.
-/
def knowledgeSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (knowledgeError : ℝ≥0) : Prop :=
  ∃ extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    let exec := do
      let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
        ← (Reduction.mk prover verifier).runWithLog stmtIn witIn
      let extractedWitIn? ←
        liftM (extractor stmtIn witOut transcript proveQueryLog.fst verifyQueryLog).run
      return (stmtIn, extractedWitIn?, stmtOut, witOut)
    Pr[fun ⟨stmtIn, extractedWitIn?, stmtOut, witOut⟩ =>
        (∀ extractedWitIn ∈ extractedWitIn?, (stmtIn, extractedWitIn) ∉ relIn) ∧
          (stmtOut, witOut) ∈ relOut
      | OptionT.mk do (simulateQ pImpl exec.run).run' (← init)] ≤ knowledgeError

/-- Type class for knowledge soundness for a verifier -/
class IsKnowledgeSound (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  knowledgeError : ℝ≥0
  is_knowledge_sound : knowledgeSoundness init impl relIn relOut verifier knowledgeError

/-- An extractor is **monotone** if its success probability on a given query log is the same as
  the success probability on any extension of that query log. -/
class Extractor.Straightline.IsMonotone
    (relIn : Set (StmtIn × WitIn))
    (E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec)
    [oSpec.Fintype] [oSpec.Inhabited]
    where
  is_monotone : ∀ witOut stmtIn transcript, ∀ proveQueryLog₁ proveQueryLog₂ : oSpec.QueryLog,
    ∀ verifyQueryLog₁ verifyQueryLog₂ : oSpec.QueryLog,
    proveQueryLog₁.Sublist proveQueryLog₂ →
    verifyQueryLog₁.Sublist verifyQueryLog₂ →
    -- Placeholder probability for now, probably need to consider the whole game
    Pr[fun witIn => (stmtIn, witIn) ∈ relIn |
      E stmtIn witOut transcript proveQueryLog₁ verifyQueryLog₁] ≤
    Pr[fun witIn => (stmtIn, witIn) ∈ relIn |
      E stmtIn witOut transcript proveQueryLog₂ verifyQueryLog₂]
    -- Pr[extraction game succeeds on proveQueryLog₁, verifyQueryLog₁]
    -- ≤ Pr[extraction game succeeds on proveQueryLog₂, verifyQueryLog₂]

end Verifier

/-! ## Adaptive, query-bounded security (generic)

`Verifier.soundness` / `Verifier.knowledgeSoundness` above are *selective* (statement fixed upfront,
`∀ stmtIn ∉ langIn`) and *unbounded* (one error bounds **every** prover).  Non-interactive arguments
in the ideal-permutation model (CO25 §6) instead need:

- **Adaptive** soundness: the prover *outputs* its statement and the break event is read off that
  output (`stmt ∉ langIn ∧ accept`).
- **Query-bounded** error: the error depends on the prover's query budget (the Key-Lemma `η★` term
  grows with the number of permutation/hash queries), so `∀ P` is restricted to a `bound` predicate
  — a single error for *all* provers is impossible.

The `Verifier.adaptiveNARG*` definitions below state this directly — `∀ P, bound P → Pr[evt | game
P] ≤ error` (soundness) and `∃ extractor, ∀ P, bound P → Pr[evt | game extractor P] ≤ error` (KS),
with the straightline extractor type written explicitly (its `auxSpecE` access is a `P`-independent
helper/sampler, never the prover).  `bound := fun _ => True` recovers the unbounded form; DSFS
instantiates these as the conclusions of `theorem_6_1_soundness` / `theorem_6_2_straightline`.

**Straightline firewall.** The KS extractor lives in `OptionT (OracleComp auxSpecE)` for *arbitrary*
`auxSpecE`, yet cannot rewind: `auxImplE : QueryImpl auxSpecE ProbComp` is a *leading* parameter
(fixed before `∃extractor, ∀P`, so no `P` is in scope) discharging every aux query into
`ProbComp = OracleComp unifSpec` — sampling only.  So even
`auxSpecE := Extractor.OracleSpec.proverOracle …` buys nothing: a prover-shaped query answered by a
`P`-independent handler is a meaningless symbol, not a real prover call — useless, not dangerous, so
no `[ProverFree auxSpecE]` is needed.  Contrast
`Extractor.Rewinding.runExt`, whose codomain *is* `OracleComp (OracleSpec.proverOracle …)` with the
real `P` plugged in — the one shape this straightline definition structurally cannot express. -/

/-! ### Concrete non-interactive (NARG) experiments — CO25 Def 3.5 / Def 3.6

The definitions below encode the CO25 Def 3.5/3.6 experiment — sample the oracle, run the adaptive
malicious prover for `(x, π)`, run the verifier, read the predicate off the sampled tuple — for a
**non-interactive argument in an oracle model**, then phrase soundness / KS as the `∀ P …` / `∃
extractor, ∀ P …` statements (so the experiment lives in the library, not the call site).

**Oracle access (`P̃^f`, `V^f`).** `oSpec` is *the random-oracle interface itself* (FS challenge /
duplex-sponge oracle), not a side-oracle.  The paper's `f ← 𝒟(λ,n)` is the handler pair
`(init, impl)`: `init` draws `f ~ 𝒟` into state `σ`, and `impl` answers **every `oSpec` query of
both `P` and the verifier against that one draw** (both run inside a single `simulateQ impl (do P;
verify)`), so they share `f` exactly as `P̃^f` / `V^f`.  When the prover's oracle interface is
larger than the verifier's (DSFS: prover has `p⁻¹`, verifier does not), take `oSpec` to be the
*prover's* spec and lift `verify` into it.

Modeling: the decision bit `V^f(x,π)=1` generalizes to "verifier produces `stmtOut ∈ langOut`"
(`langOut = {true}` recovers Boolean); the prover is the flat adaptive `OracleComp oSpec
(StmtIn × Proof)` (it *outputs* `x`); for KS the experiment additionally logs `tr` and feeds
`(x, π, tr)` to the extractor (`w ← E(x,π,tr)`). -/
section AdaptiveNARG

/-- **CO25 Def 3.5 experiment** — the adaptive NARG soundness game in an oracle model: sample the
oracle handler (`init`/`impl`), run the adaptive prover `P` for `(x, π)`, run the verifier
`verify x π`, and return `(x, stmtOut)` (the whole run `none`-aborts when the verifier rejects).

The inner computation is written in the **`OptionT`/abort** monad so that verifier rejection is
modeled by `OptionT` abort (the framework convention, matching `OracleVerifier` and the
duplex-sponge `dsfsGame`) rather than an in-band `Option` value — this keeps the structure identical
to the games it is compared against (e.g. `dsfsNargSoundnessExp_eq_dsfsGame`).  The `ProbComp`
result is unchanged (`OptionT (OracleComp oSpec) α` reduces to `OracleComp oSpec (Option α)`). -/
def adaptiveNARGSoundnessExp {ι : Type} {oSpec : OracleSpec ι} {σ StmtIn Proof StmtOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (P : OracleComp oSpec (StmtIn × Proof)) :
    ProbComp (Option (StmtIn × StmtOut)) := do
  (simulateQ impl (do
    let ⟨x, π⟩ ← P
    let stmtOut ← verifier.verify x (Fin.cons π (fun i => i.elim0))
    return (x, stmtOut) : OptionT (OracleComp oSpec) (StmtIn × StmtOut))).run' (← init)

/-- **CO25 Def 3.5 false-acceptance event** on the NARG soundness experiment output
`Option (StmtIn × StmtOut)`: the prover output a false statement (`x ∉ langIn`) the verifier
accepted into `stmtOut ∈ langOut`.  A *named* event (not an inline `match`) so the same term is
shared between
`adaptiveNARGSoundness` and downstream game-match lemmas (e.g. DSFS
`dsfsNargSoundnessExp_eq_dsfsGame`) — inline `match` lambdas compile to distinct per-declaration
aux-defs that block `rw`/`exact`. -/
def nargSoundFailEvent {StmtIn StmtOut : Type} (langIn : Set StmtIn) (langOut : Set StmtOut) :
    Option (StmtIn × StmtOut) → Prop
  | some (x, stmtOut) => x ∉ langIn ∧ stmtOut ∈ langOut
  | none => False

/-- **CO25 Def 3.5** — adaptive, query-bounded soundness of a non-interactive argument: every
`t`-query (i.e. `bound`-meeting) adaptive prover convinces the verifier of a false statement
(`x ∉ langIn ∧ stmtOut ∈ langOut`) with probability at most `error`. -/
def Verifier.adaptiveNARGSoundness {ι : Type} {oSpec : OracleSpec ι}
    {σ StmtIn Proof StmtOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (bound : OracleComp oSpec (StmtIn × Proof) → Prop) (error : ENNReal) : Prop :=
  ∀ P : OracleComp oSpec (StmtIn × Proof), bound P →
    Pr[ nargSoundFailEvent langIn langOut
      | adaptiveNARGSoundnessExp init impl verifier P ] ≤ error

/-- **CO25 Def 3.6 experiment** — the adaptive NARG straightline-KS game: the prover outputs
`(x, π, witOut)` (statement, proof, and claimed output witness — framework-composable shape), the
experiment captures the prover query log `tr` **and** the verifier query log `tr_V` (both via
`loggingOracle`), runs the verifier `verify x π` (`none` = reject) and the straightline extractor
`extractor x π tr tr_V`, returning `(x, extracted-witness?, stmtOut?, witOut)`.

The extractor receives the prover and verifier query logs **separately** (matching CO25
Construction 6.3's `𝓔(𝕩, π, tr, tr_𝒱, 𝓟̃)`, where `𝓔` internally forms `D2STrace(tr ‖ tr_𝒱)`), and
`Extractor.Straightline`'s two log slots.  Acceptance / extraction are gated in `nargKSFailEvent`
via `(stmtOut, witOut) ∈ relOut`. -/
def adaptiveNARGKnowledgeSoundnessExp
    {ι κE : Type} {oSpec : OracleSpec ι} {auxSpecE : OracleSpec κE}
    {σ StmtIn Proof StmtOut WitIn WitOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (auxImplE : QueryImpl auxSpecE ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp auxSpecE) WitIn)
    (P : OracleComp oSpec (StmtIn × Proof × WitOut)) :
    ProbComp (StmtIn × Option WitIn × Option StmtOut × WitOut) := do
  -- Prover + verifier share the sampled oracle `σ` (`impl`); their query logs `tr, tr_V` are read
  -- out and handed to the extractor as DATA.  Then the extractor runs **separately**, over only its
  -- own sampler `auxSpecE` (answered by the `P`-independent `auxImplE`) — it does NOT see `σ`, the
  -- challenge oracle, or `P`; it reads challenges from `tr, tr_V`.  This is CO25 Def 3.14 (the
  -- straightline extractor is deterministic given the trace) — straightline, not rewinding.
  let ⟨x, π, witOut, tr, stmtOut?, tr_V⟩ ←
    (simulateQ impl (do
      let ⟨⟨x, π, witOut⟩, tr⟩ ← (simulateQ loggingOracle P).run
      let ⟨stmtOut?, tr_V⟩ ←
        (simulateQ loggingOracle (verifier.verify x (Fin.cons π (fun i => i.elim0))).run).run
      pure (x, π, witOut, tr, stmtOut?, tr_V))).run' (← init)
  let witIn? ← simulateQ auxImplE (extractor x π tr tr_V).run
  pure (x, witIn?, stmtOut?, witOut)

/-- **CO25 Def 3.6 extraction-failure event** on the NARG-KS experiment output
`StmtIn × Option WitIn × Option StmtOut × WitOut`: the verifier accepted into the **output
relation** (`(stmtOut, witOut) ∈ relOut`, with `stmtOut = none` = verifier rejected) yet the
extracted input witness misses `relIn` (or none was produced).  Acceptance is
`(stmtOut, witOut) ∈ relOut` — the
OracleReduction framework convention (matching the library `knowledgeSoundness` and the SR-KS
`coinKSExperimentProb`), so the DSFS KS guarantee composes with downstream protocols.  A *named*
event (not an inline `match`) so the same term is shared between
`adaptiveNARGKnowledgeSoundness(WithCoins)` and downstream game-match lemmas (e.g. DSFS
`dsfsKSGame_hL1`/`dsfsKSGame_hL3`) — inline `match` lambdas compile to distinct per-declaration
aux-defs that block `exact`/`rw` unification, which a shared constant avoids. -/
def nargKSFailEvent {StmtIn WitIn StmtOut WitOut : Type}
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) :
    StmtIn × Option WitIn × Option StmtOut × WitOut → Prop
  | (x, some witIn, some stmtOut, witOut) => (stmtOut, witOut) ∈ relOut ∧ (x, witIn) ∉ relIn
  | (_, none, some stmtOut, witOut) => (stmtOut, witOut) ∈ relOut
  | _ => False

/-- **CO25 Def 3.6** — adaptive, query-bounded straightline knowledge soundness of a non-interactive
argument: there is a straightline extractor such that every `bound`-meeting adaptive prover makes
the extraction-failure event happen — the verifier accepts (the game returns `some`, i.e. `V=1`) yet
the extracted witness misses `relIn` (or no witness is produced) — with probability at most `error`.
(Acceptance is implicit in the game returning `some`, matching CO25 Def 3.6's `V^f(x,π)=1`; no
output language is needed.) -/
def Verifier.adaptiveNARGKnowledgeSoundness
    {ι κE : Type} {oSpec : OracleSpec ι} {auxSpecE : OracleSpec κE}
    {σ StmtIn Proof StmtOut WitIn WitOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (auxImplE : QueryImpl auxSpecE ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (bound : OracleComp oSpec (StmtIn × Proof × WitOut) → Prop) (error : ENNReal) : Prop :=
  ∃ extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp auxSpecE) WitIn,
  ∀ P : OracleComp oSpec (StmtIn × Proof × WitOut), bound P →
    Pr[ nargKSFailEvent relIn relOut
      | adaptiveNARGKnowledgeSoundnessExp init impl auxImplE verifier extractor P ] ≤ error

/-! ### Coin-bearing NARG experiments (compiled / randomized provers)

CO25 §6 reduces a NARG to its interactive proof via a *compiled* prover that samples its own private
randomness (DSFS's `D2SAlgo^f(P̃)` does lookahead/backtrack sampling).  Such a prover is not
coin-free, so the soundness/KS experiment must answer its coins.  Mirroring the SR layer's
`SoundnessWithCoins` / `coinSRExperimentProb`, the prover here queries `oSpec + auxSpec` (the random
oracle interface `oSpec` plus private coins `auxSpec`); `impl` serves `oSpec` against the
`init`-draw, `auxImpl` serves the coins at game time, and the verifier/extractor live over base
`oSpec`
(coin-blind), lifted into the game spec.  Taking `auxSpec := []ₒ` recovers the coin-free experiments
up to `+ []ₒ`. -/

/-- Coin-bearing CO25 Def 3.5 experiment: the prover may sample private coins `auxSpec` (answered by
`auxImpl`). -/
def adaptiveNARGSoundnessExpWithCoins
    {ι κ : Type} {oSpec : OracleSpec ι} {auxSpec : OracleSpec κ}
    {σ StmtIn Proof StmtOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (auxImpl : QueryImpl auxSpec ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (P : OracleComp (oSpec + auxSpec) (StmtIn × Proof)) :
    ProbComp (Option (StmtIn × StmtOut)) := do
  (simulateQ ((impl.addLift auxImpl) : QueryImpl (oSpec + auxSpec) (StateT σ ProbComp))
    ((do
      let ⟨x, π⟩ ← P
      let stmtOut ←
        OptionT.mk (liftComp (verifier.verify x
          (Fin.cons π (fun i => i.elim0))).run (oSpec + auxSpec))
      return (x, stmtOut)) :
    OptionT (OracleComp (oSpec + auxSpec)) (StmtIn × StmtOut))).run' (← init)

/-- Coin-bearing CO25 Def 3.5 — adaptive, query-bounded soundness against provers with private
coins. -/
def Verifier.adaptiveNARGSoundnessWithCoins
    {ι κ : Type} {oSpec : OracleSpec ι} {auxSpec : OracleSpec κ}
    {σ StmtIn Proof StmtOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (auxImpl : QueryImpl auxSpec ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (bound : OracleComp (oSpec + auxSpec) (StmtIn × Proof) → Prop) (error : ENNReal) : Prop :=
  ∀ P : OracleComp (oSpec + auxSpec) (StmtIn × Proof), bound P →
    Pr[ fun out => match out with
        | some (x, stmtOut) => x ∉ langIn ∧ stmtOut ∈ langOut
        | none => False
      | adaptiveNARGSoundnessExpWithCoins init impl auxImpl verifier P ] ≤ error

/-- Coin-bearing CO25 Def 3.6 experiment: like `adaptiveNARGSoundnessExpWithCoins`, but it captures
the prover's query log and, on an accepting run, runs the straightline extractor on it.

The prover `P` has full access to its private coins `auxSpec` (it runs over `oSpec + auxSpec`), and
its complete query log `tr` is captured.  But the **extractor is fed only the `oSpec` projection
`tr.fst`** — the prover's private-coin (`auxSpec`) queries are *excluded* from the log handed to the
extractor.  This matches CO25 Def 3.14: the straightline extractor reads the prover's transcript to
the *oracle* (the shared/challenge queries), never its private sampling coins.  It also keeps this
experiment consistent with the coin-free `adaptiveNARGKnowledgeSoundnessExp`, whose extractor
likewise receives only `QueryLog oSpec`. -/
def adaptiveNARGKnowledgeSoundnessExpWithCoins
    {ι κ κE : Type} {oSpec : OracleSpec ι} {auxSpec : OracleSpec κ} {auxSpecE : OracleSpec κE}
    {σ StmtIn Proof StmtOut WitIn WitOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (auxImpl : QueryImpl auxSpec ProbComp)
    (auxImplE : QueryImpl auxSpecE ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → WitOut → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp auxSpecE) WitIn)
    (P : OracleComp (oSpec + auxSpec) (StmtIn × Proof × WitOut)) :
    ProbComp (StmtIn × Option WitIn × Option StmtOut × WitOut) := do
  -- Prover (coins `auxSpec`) + verifier share `σ` (`impl.addLift auxImpl`); their logs `tr, tr_V`
  -- are read out as DATA.  Then the extractor runs **separately** over only its own sampler
  -- `auxSpecE` (the `P`-independent `auxImplE`) — it sees neither `σ`, `auxSpec` (coin-blind), the
  -- challenge oracle, nor `P`; it reads challenges from `tr.fst, tr_V`.  CO25 Def 3.14.
  -- `tr_V` is logged at the **narrow** `oSpec` (the verifier is coin-blind — never queries
  -- `auxSpec`).  The prover's `auxSpec`-coin queries in `tr` are dropped via `tr.fst` (the `oSpec`
  -- projection) before the extractor sees the log.
  let ⟨x, π, witOut, tr, stmtOut?, tr_V⟩ ←
    (simulateQ ((impl.addLift auxImpl) : QueryImpl (oSpec + auxSpec) (StateT σ ProbComp)) (do
      let ⟨⟨x, π, witOut⟩, tr⟩ ← (simulateQ loggingOracle P).run
      let ⟨stmtOut?, tr_V⟩ ←
        liftComp
          (simulateQ loggingOracle (verifier.verify x (Fin.cons π (fun i => i.elim0))).run).run
          (oSpec + auxSpec)
      pure (x, π, witOut, tr, stmtOut?, tr_V))).run' (← init)
  let witIn? ← simulateQ auxImplE (extractor x witOut π tr.fst tr_V).run
  pure (x, witIn?, stmtOut?, witOut)

/-- Coin-bearing CO25 Def 3.6 — adaptive, query-bounded straightline knowledge soundness against
provers with private coins. -/
def Verifier.adaptiveNARGKnowledgeSoundnessWithCoins
    {ι κ κE : Type} {oSpec : OracleSpec ι} {auxSpec : OracleSpec κ} {auxSpecE : OracleSpec κE}
    {σ StmtIn Proof StmtOut WitIn WitOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (auxImpl : QueryImpl auxSpec ProbComp)
    (auxImplE : QueryImpl auxSpecE ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (bound : OracleComp (oSpec + auxSpec) (StmtIn × Proof × WitOut) → Prop) (error : ENNReal) :
    Prop :=
  ∃ extractor : (stmtIn: StmtIn) → (witOut : WitOut) → (π: Proof) → (tr_P : QueryLog oSpec)
    → (tr_V : QueryLog oSpec) → OptionT (OracleComp auxSpecE) WitIn,
  ∀ P : OracleComp (oSpec + auxSpec) (StmtIn × Proof × WitOut), bound P →
    Pr[ nargKSFailEvent relIn relOut
      | adaptiveNARGKnowledgeSoundnessExpWithCoins init impl auxImpl auxImplE verifier
          extractor P ] ≤ error

end AdaptiveNARG

end Soundness

namespace Reduction

section ZeroKnowledge

/-- A simulator for a reduction needs to produce the same transcript as the prover (but potentially
  all at once, instead of sequentially). We also grant the simulator the power to program the shared
  oracles `oSpec` -/
structure Simulator (oSpec : OracleSpec ι) (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  SimState : Type
  oracleSim : QueryImpl oSpec (StateT SimState (OracleComp oSpec))
  proverSim : StmtIn → StateT SimState (OracleComp oSpec) pSpec.FullTranscript

/-
  We define honest-verifier zero-knowledge as follows:
  There exists a simulator such that for all (malicious) verifier, the distributions of transcripts
  generated by the simulator and the interaction between the verifier and the prover are
  (statistically) indistinguishable.
-/
-- def zeroKnowledge (prover : Prover pSpec oSpec) : Prop :=
--   ∃ simulator : Simulator,
--   ∀ verifier : Verifier pSpec oSpec,
--   ∀ stmtIn : Statement,
--   ∀ witIn : Witness,
--   relIn.isValid stmtIn witIn = true →
--     let result := (Reduction.mk prover verifier).run stmtIn witIn
--     let transcript := Prod.fst <$> Prod.snd <$> result
--     let simTranscript := simulator
--     -- let prob := spec.relOut.isValid' <$> output
--     sorry

end ZeroKnowledge

end Reduction

/-! Completeness and soundness are the same as for non-oracle reductions. Only zero-knowledge is
  different (but we haven't defined it yet) -/

open Reduction

section OracleProtocol

variable [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleReduction

open Classical in
/-- Completeness of an oracle reduction is the same as for non-oracle reductions. -/
def completeness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (completenessError : ℝ≥0) : Prop :=
  Reduction.completeness init impl relIn relOut oracleReduction.toReduction completenessError

open Classical in
/-- Perfect completeness of an oracle reduction is the same as for non-oracle reductions. -/
def perfectCompleteness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      Prop :=
  Reduction.perfectCompleteness init impl relIn relOut oracleReduction.toReduction

end OracleReduction

namespace OracleVerifier

/-- Soundness of an oracle reduction is the same as for non-oracle reductions. -/
def soundness
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  verifier.toVerifier.soundness init impl langIn langOut soundnessError

/-- Knowledge soundness of an oracle reduction is the same as for non-oracle reductions. -/
def knowledgeSoundness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  verifier.toVerifier.knowledgeSoundness init impl relIn relOut knowledgeError

end OracleVerifier

end OracleProtocol

variable {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type}
  [∀ i, OracleInterface (OStatement i)] {Witness : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace Proof

/-! All security notions are inherited from `Reduction`, with the output relation specialized to the
  trivial accept/reject one: `fun accRej _ => accRej`. -/

open Reduction Classical

@[reducible, simp]
def completeness (relation : Set (Statement × Witness)) (completenessError : ℝ≥0)
    (proof : Proof oSpec Statement Witness pSpec) : Prop :=
  Reduction.completeness init impl relation acceptRejectRel proof completenessError

@[reducible, simp]
def perfectCompleteness (relation : Set (Statement × Witness))
    (proof : Proof oSpec Statement Witness pSpec) : Prop :=
  Reduction.perfectCompleteness init impl relation acceptRejectRel proof

@[reducible, simp]
def soundness (langIn : Set Statement)
    (verifier : Verifier oSpec Statement Bool pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  verifier.soundness init impl langIn acceptRejectRel.language soundnessError

@[reducible, simp]
def knowledgeSoundness (relation : Set (Statement × Bool))
    (verifier : Verifier oSpec Statement Bool pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  verifier.knowledgeSoundness init impl relation acceptRejectRel knowledgeError

end Proof

namespace OracleProof

open OracleReduction Classical

/-- Completeness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def completeness
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (oracleProof : OracleProof oSpec Statement OStatement Witness pSpec)
    (completenessError : ℝ≥0) : Prop :=
  OracleReduction.completeness init impl
    relation acceptRejectOracleRel oracleProof completenessError

/-- Perfect completeness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def perfectCompleteness
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (oracleProof : OracleProof oSpec Statement OStatement Witness pSpec) :
      Prop :=
  OracleReduction.perfectCompleteness init impl relation acceptRejectOracleRel oracleProof

/-- Soundness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def soundness
    (langIn : Set (Statement × ∀ i, OStatement i))
    (verifier : OracleVerifier oSpec Statement OStatement Bool (fun _ : Empty => Unit) pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  verifier.toVerifier.soundness init impl langIn acceptRejectOracleRel.language soundnessError

/-- Knowledge soundness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def knowledgeSoundness
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (verifier : OracleVerifier oSpec Statement OStatement Bool (fun _ : Empty => Unit) pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  verifier.toVerifier.knowledgeSoundness init impl relation acceptRejectOracleRel knowledgeError

end OracleProof

section Trivial

-- We show that the trivial (oracle) reduction is perfectly complete, sound, and knowledge sound.

/-- The identity / trivial reduction is perfectly complete. -/
@[simp]
theorem Reduction.id_perfectCompleteness {rel : Set (StmtIn × WitIn)} :
    (Reduction.id : Reduction oSpec _ _ _ _ _).perfectCompleteness init impl rel rel := by
  simp only [perfectCompleteness, completeness, ENNReal.coe_zero, tsub_zero]
  intro stmtIn witIn hIn
  simp only [Reduction.id_run]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- Pr[⊥ | OptionT.mk ...] = 0
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _
    change none ∈ support
      (StateT.run' (simulateQ _ (pure (some ((default, stmtIn, witIn), stmtIn)) :
        OracleComp _ _)) s) → False
    rw [simulateQ_pure]
    change none ∈ support
      (Prod.fst <$> (pure (some ((default, stmtIn, witIn), stmtIn)) :
        StateT σ ProbComp _).run s) → False
    rw [StateT.run_pure]; simp [map_pure]
  · -- ∀ x ∈ support, event x
    intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ support
      (StateT.run' (simulateQ _ (pure (some ((default, stmtIn, witIn), stmtIn)) :
        OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ support
      (Prod.fst <$> (pure (some ((default, stmtIn, witIn), stmtIn)) :
        StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure, support_pure] at hx
    cases hx
    exact ⟨hIn, rfl⟩

private lemma Reduction.run_mk_verifier_id {WitIn WitOut : Type}
    (prover : Prover oSpec StmtIn WitIn StmtIn WitOut !p[])
    (stmtIn : StmtIn) (witIn : WitIn) :
    (Reduction.mk prover Verifier.id).run stmtIn witIn =
      (fun pr => (pr, stmtIn)) <$> prover.run stmtIn witIn := by
  simp only [Reduction.run, Verifier.run, Verifier.id, OptionT.run_pure,
    monadLift_bind, Function.comp_apply, monadLift_pure,
    pure_bind, Option.getM, map_eq_bind_pure_comp]

/-- The identity / trivial verifier is perfectly sound. -/
@[simp]
theorem Verifier.id_soundness {lang : Set StmtIn} :
    (Verifier.id : Verifier oSpec _ _ _).soundness init impl lang lang 0 := by
  sorry
  -- Approach: after Reduction.run_mk_verifier_id, stmtOut = stmtIn always.
  -- Needs StateT.run'_bind/pure or manual support reasoning through OptionT+simulateQ+StateT.

/-- The straightline extractor for the identity / trivial reduction, which just returns the input
  witness. -/
@[reducible]
def Extractor.Straightline.id : Extractor.Straightline oSpec StmtIn WitIn WitIn !p[] :=
  fun _ witOut _ _ _ => pure witOut

/-- The identity / trivial verifier is perfectly knowledge sound. -/
@[simp]
theorem Verifier.id_knowledgeSoundness {rel : Set (StmtIn × WitIn)} :
    (Verifier.id : Verifier oSpec _ _ _).knowledgeSoundness init impl rel rel 0 := by
  -- `Extractor.Straightline.id` returns the (adversarial) output witness. On the support of the
  -- game, the identity verifier outputs the input statement, so the bad event requires both
  -- `(stmtIn, witOut) ∉ rel` (extracted witness invalid) and `(stmtIn, witOut) ∈ rel`
  -- (output pair valid): a contradiction.
  refine ⟨Extractor.Straightline.id, fun stmtIn witIn prover => ?_⟩
  simp only [ENNReal.coe_zero, le_zero_iff]
  refine probEvent_eq_zero fun x hx => ?_
  rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
  simp only [support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _, hx⟩ := hx
  simp only [Reduction.runWithLog, Verifier.run, Verifier.id, Extractor.Straightline.id,
    OptionT.run_bind, OptionT.run_pure, Option.getM, Option.elimM,
    simulateQ_bind, StateT.run'_bind', support_bind, Set.mem_iUnion] at hx
  obtain ⟨⟨o, s'⟩, hi, hx2⟩ := hx
  cases o with
  | none =>
    simp only [Option.elim, simulateQ_pure, StateT.run'_pure', support_pure,
      Set.mem_singleton_iff] at hx2
    exact (Option.some_ne_none x hx2).elim
  | some x' =>
    -- From `hx2`: `x = (stmtIn, some witOut, x'.1.2, witOut)`
    simp only [Option.elim, simulateQ_pure, OptionT.run_pure, liftM_pure, pure_bind,
      StateT.run'_pure', support_pure, Set.mem_singleton_iff] at hx2
    -- From `hi`: the verifier is the identity, so `x'.1.2 = stmtIn`
    rw [show (pure stmtIn : OptionT (OracleComp oSpec) StmtIn) =
      (pure (some stmtIn) : OracleComp oSpec (Option StmtIn)) from rfl] at hi
    simp only [Option.elim, simulateQ_pure, OptionT.run_pure, WriterT.run_pure, liftM_pure,
      pure_bind, support_bind, Set.mem_iUnion, StateT.run_bind] at hi
    obtain ⟨⟨o2, s2⟩, _, hi2⟩ := hi
    cases o2 with
    | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hi2
      exact (Option.some_ne_none x' hi2.1).elim
    | some pr =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hi2
      obtain ⟨rfl, -⟩ := hi2
      simp only [Option.some.injEq] at hx2
      subst hx2
      rintro ⟨h1, h2⟩
      exact h1 _ rfl h2

/-- The identity / trivial reduction is perfectly complete. -/
@[simp]
theorem OracleReduction.id_perfectCompleteness
    {rel : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)} :
    (OracleReduction.id : OracleReduction oSpec _ _ _ _ _ _ _).perfectCompleteness
      init impl rel rel := by
  unfold OracleReduction.perfectCompleteness
  simp only [OracleReduction.id_toReduction, Reduction.id_perfectCompleteness]

/-- The identity / trivial verifier is perfectly sound. -/
@[simp, grind .]
theorem OracleVerifier.id_soundness {lang : Set (StmtIn × ∀ i, OStmtIn i)} :
    (OracleVerifier.id : OracleVerifier oSpec _ _ _ _ _).soundness
      init impl lang lang 0 := by
  simp [OracleVerifier.soundness]

/-- The identity / trivial verifier is perfectly knowledge sound. -/
@[simp, grind .]
theorem OracleVerifier.id_knowledgeSoundness {rel : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)} :
    (OracleVerifier.id : OracleVerifier oSpec _ _ _ _ _).knowledgeSoundness
      init impl rel rel 0 := by
  simp [OracleVerifier.knowledgeSoundness]

end Trivial

end
