/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Rewinding Knowledge Soundness

  This file defines rewinding knowledge soundness for (oracle) reductions.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Extractor

section Rewinding

/-! TODO: under development -/

/-- The oracle interface to call the prover as a black box -/
def OracleSpec.proverOracle (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) :
    OracleSpec ((i : pSpec.MessageIdx) × StmtIn × pSpec.Transcript i.val.castSucc) :=
  fun q => pSpec.Message q.1

/-- An opaque handle naming one execution of a prover.

Handles, rather than prover states or coins, are exposed to an extractor.  The
checkpoint-restore implementation allocates them and keeps their meaning private. -/
def RunId : Type := ℕ

/-- Queries against a black-box prover with explicit run identity.

The older `OracleSpec.proverOracle` is indexed by
`(message index, statement, partial transcript)`.  Repeating such a query can run the
prover afresh, so two transcript-indexed forks need not share their prefix coins.
Here a program can instead issue `feedChal h i c₁` and `feedChal h i c₂` for the same
handle `h`.  The implementation owns the checkpoint denoted by `h`, making that shared
prefix expressible without exposing any prover-dependent type in the query index. -/
inductive ProverRunQuery (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) : Type
  /-- Allocate a fresh run initialized for `stmt`. -/
  | start (stmt : StmtIn)
  /-- Realize the prover's next outgoing message and return the child run. -/
  | sendMsg (h : RunId) (i : pSpec.MessageIdx)
  /-- Fork a pending challenge checkpoint, applying `c` to its realized continuation. -/
  | feedChal (h : RunId) (i : pSpec.ChallengeIdx) (c : pSpec.Challenge i)

/-- The run-identified prover-oracle interface.

Its domain is prover-independent: indices contain only public protocol data and an
opaque natural-number handle.  Fresh handles are returned by the oracle itself. -/
def OracleSpec.seededProverOracle (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) :
    OracleSpec (ProverRunQuery StmtIn pSpec)
  | .start _ => RunId
  | .sendMsg _ i => pSpec.Message i × RunId
  | .feedChal _ _ _ => RunId

/-- A realized prover checkpoint.

At a challenge round the oracle effects of `receiveChallenge` have already run.
Consequently every child fork applies the same stored continuation `k`; it never
re-executes the computation that produced `k`. -/
inductive Prover.Checkpoint {ι} {oSpec : OracleSpec ι} {n} {pSpec : ProtocolSpec n}
    (P : ProverInteraction oSpec pSpec) : Type
  /-- A realized state parked before a prover-message round, or after the last round. -/
  | atRound (i : Fin (n + 1)) (s : P.PrvState i)
  /-- A challenge continuation whose oracle effects have already been realized. -/
  | pendingChal (i : pSpec.ChallengeIdx)
      (k : pSpec.Challenge i → P.PrvState i.1.succ)

/-- Append-only storage for the checkpoints denoted by `RunId`s. -/
def RunStore (P : ProverInteraction oSpec pSpec) : Type := List (Prover.Checkpoint P)

namespace ProverInteraction

/-- Normalize a realized state to the next externally actionable checkpoint.

If the state is before a challenge, `receiveChallenge` is run immediately and its
resulting continuation is stored.  At a send round or the end of the protocol, the
state itself is stored.  The direction test is computable for every flat
`ProtocolSpec`; no determinism or consistency condition is imposed on the prover. -/
def normalizeCheckpoint (P : ProverInteraction oSpec pSpec)
    (state : (i : Fin (n + 1)) × P.PrvState i) :
    OracleComp oSpec (Prover.Checkpoint P) := by
  let ⟨i, s⟩ := state
  if hi : i.val < n then
    let j : Fin n := ⟨i.val, hi⟩
    have hji : j.castSucc = i := Fin.ext rfl
    match hDir : pSpec.dir j with
    | .P_to_V => exact pure (.atRound i s)
    | .V_to_P => exact do
        let k ← P.receiveChallenge ⟨j, hDir⟩ (hji ▸ s)
        pure (.pendingChal ⟨j, hDir⟩ k)
  else
    exact pure (.atRound i s)

/-- Allocate `cp` at the next handle without changing any existing store entry. -/
@[inline]
def appendCheckpoint (P : ProverInteraction oSpec pSpec)
    (store : RunStore P) (cp : Prover.Checkpoint P) :
    RunId × RunStore P :=
  (store.length, List.append store [cp])

@[simp]
theorem appendCheckpoint_lookup (P : ProverInteraction oSpec pSpec)
    (store : RunStore P) (cp : Prover.Checkpoint P) :
    getElem?
        (show List (Prover.Checkpoint P) from (appendCheckpoint P store cp).2)
        (show ℕ from (appendCheckpoint P store cp).1) = some cp := by
  simp [appendCheckpoint, RunStore, RunId]

/-- The flat checkpoint-restore implementation (`BlackBox.CheckpointRestore`).

Only handles allocated by this implementation are meaningful.  Invalid or
round-mismatched handles are totalized by returning the supplied handle and, for
`sendMsg`, an inhabited junk message; those paths do not change the store.  Adequacy
theorems below use only oracle-allocated handles.

`sendMsg` executes fresh post-fork prover effects and normalizes the child checkpoint.
`feedChal` only applies a stored realized continuation before normalizing later rounds,
so sibling forks share all prefix coins by construction. -/
def seededImpl [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec) :
    QueryImpl (OracleSpec.seededProverOracle StmtIn pSpec)
      (StateT (RunStore P) (OracleComp oSpec)) :=
  fun q => StateT.mk fun store => match q with
    | .start _ => do
        let cp ← normalizeCheckpoint P ⟨0, P.init⟩
        pure (appendCheckpoint P store cp)
    | .sendMsg h i =>
        let entries : List (Prover.Checkpoint P) := store
        match entries[(show ℕ from h)]? with
        | some (Prover.Checkpoint.atRound j s) =>
            if hj : j = i.1.castSucc then do
              let ⟨msg, s'⟩ ← P.sendMessage i (hj ▸ s)
              let cp ← normalizeCheckpoint P ⟨i.1.succ, s'⟩
              let ⟨child, store'⟩ := appendCheckpoint P store cp
              pure ((msg, child), store')
            else
              pure ((default, h), store)
        | _ => pure ((default, h), store)
    | .feedChal h i c =>
        let entries : List (Prover.Checkpoint P) := store
        match entries[(show ℕ from h)]? with
        | some (Prover.Checkpoint.pendingChal j k) =>
            if hj : j = i then do
              let cp ← normalizeCheckpoint P ⟨i.1.succ, (hj ▸ k) c⟩
              pure (appendCheckpoint P store cp)
            else
              pure (h, store)
        | _ => pure (h, store)

/-- Every result of every handler query extends the input store.

The statement ranges over the support of the actual `seededImpl` computation, so it
covers effectful starts and send rounds as well as pure forks and junk paths.  Prefix
extension is the handler-level contract: no query can replace or mutate an existing
checkpoint. -/
theorem seededImpl_store_appendOnly [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec)
    (q : (OracleSpec.seededProverOracle StmtIn pSpec).Domain)
    (store : RunStore P) :
    ∀ z ∈ support ((seededImpl (StmtIn := StmtIn) P q).run store),
      (show List (Prover.Checkpoint P) from store) <+:
        (show List (Prover.Checkpoint P) from z.2) := by
  intro z hz
  cases q with
  | start stmt =>
      simp only [seededImpl, StateT.run_mk, mem_support_bind_iff,
        mem_support_pure_iff] at hz
      obtain ⟨cp, _, rfl⟩ := hz
      exact ⟨[cp], rfl⟩
  | sendMsg h i =>
      simp only [seededImpl, StateT.run_mk] at hz
      split at hz
      next j s hcp =>
        split at hz
        · simp only [mem_support_bind_iff, mem_support_pure_iff] at hz
          obtain ⟨⟨msg, s'⟩, _, cp, _, rfl⟩ := hz
          exact ⟨[cp], rfl⟩
        · simp only [mem_support_pure_iff] at hz
          subst z
          exact ⟨[], by simp⟩
      next hother =>
        simp only [mem_support_pure_iff] at hz
        subst z
        exact ⟨[], by simp⟩
  | feedChal h i c =>
      simp only [seededImpl, StateT.run_mk] at hz
      split at hz
      next j k hcp =>
        split at hz
        · simp only [mem_support_bind_iff, mem_support_pure_iff] at hz
          obtain ⟨cp, _, rfl⟩ := hz
          exact ⟨[cp], rfl⟩
        · simp only [mem_support_pure_iff] at hz
          subst z
          exact ⟨[], by simp⟩
      next hother =>
        simp only [mem_support_pure_iff] at hz
        subst z
        exact ⟨[], by simp⟩

/-- Feeding a challenge through a valid handle applies the continuation already stored
at that handle.  The only subsequent oracle effects are those of normalizing the child
state; the computation that produced `k` is not re-run. -/
theorem seededImpl_feedChal_pure [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec) (h : RunId) (i : pSpec.ChallengeIdx)
    (c : pSpec.Challenge i) (store : RunStore P)
    (k : pSpec.Challenge i → P.PrvState i.1.succ)
    (hstore :
      (show List (Prover.Checkpoint P) from store)[(show ℕ from h)]? =
        some (.pendingChal i k)) :
    (seededImpl (StmtIn := StmtIn) P (.feedChal h i c)).run store =
      (do
        let cp ← normalizeCheckpoint P ⟨i.1.succ, k c⟩
        pure (appendCheckpoint P store cp)) := by
  unfold seededImpl
  simp only [StateT.run_mk]
  rw [hstore]
  simp only
  split
  · rfl
  · contradiction

/-- One round of the canonical no-fork program. -/
def straightlineScriptStep (chals : pSpec.Challenges) (j : Fin n)
    (current : pSpec.Transcript j.castSucc × RunId) :
    OracleComp (OracleSpec.seededProverOracle StmtIn pSpec)
      (pSpec.Transcript j.succ × RunId) := do
  let ⟨transcript, h⟩ := current
  match hDir : pSpec.dir j with
  | .V_to_P =>
      let c := chals ⟨j, hDir⟩
      let child ← query
        (spec := OracleSpec.seededProverOracle StmtIn pSpec)
        (.feedChal h ⟨j, hDir⟩ c)
      pure (transcript.concat c, child)
  | .P_to_V => do
      let ⟨msg, child⟩ ← query
        (spec := OracleSpec.seededProverOracle StmtIn pSpec)
        (.sendMsg h ⟨j, hDir⟩)
      pure (transcript.concat msg, child)

/-- The canonical no-fork program up to round `i`.  It allocates one initial
handle and then advances only the most recently returned handle, recording exactly the
messages and caller-supplied challenges in the transcript. -/
def straightlineScriptTo (stmt : StmtIn) (chals : pSpec.Challenges)
    (i : Fin (n + 1)) :
    OracleComp (OracleSpec.seededProverOracle StmtIn pSpec)
      (pSpec.Transcript i × RunId) :=
  Fin.induction
    (do
      let h ← query (spec := OracleSpec.seededProverOracle StmtIn pSpec) (.start stmt)
      pure (default, h))
    (fun j prev => prev >>= straightlineScriptStep chals j)
    i

/-- The complete canonical no-fork prover-oracle program. -/
def straightlineScript (stmt : StmtIn) (chals : pSpec.Challenges) :
    OracleComp (OracleSpec.seededProverOracle StmtIn pSpec)
      (pSpec.FullTranscript × RunId) :=
  straightlineScriptTo stmt chals (Fin.last n)

/-- Direct flat execution with a fixed public challenge at every verifier round.

This is the fixed-challenge specialization of `Prover.runToRound`, stated for
`ProverInteraction`, whose initial state is already part of the structure. -/
def runToRoundFixed (P : ProverInteraction oSpec pSpec) (chals : pSpec.Challenges)
    (i : Fin (n + 1)) :
    OracleComp oSpec (pSpec.Transcript i × P.PrvState i) :=
  Fin.induction
    (pure (default, P.init))
    (fun j prev => do
      let ⟨transcript, state⟩ ← prev
      match hDir : pSpec.dir j with
      | .V_to_P => do
          let k ← P.receiveChallenge ⟨j, hDir⟩ state
          pure (transcript.concat (chals ⟨j, hDir⟩), k (chals ⟨j, hDir⟩))
      | .P_to_V => do
          let ⟨msg, state'⟩ ← P.sendMessage ⟨j, hDir⟩ state
          pure (transcript.concat msg, state'))
    i

/-- View a full prover as a fixed-initial-state interaction for one statement and witness. -/
@[reducible]
def _root_.Prover.toInteraction
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (stmt : StmtIn) (wit : WitIn) :
    ProverInteraction oSpec pSpec where
  PrvState := P.PrvState
  init := P.input (stmt, wit)
  sendMessage := P.sendMessage
  receiveChallenge := P.receiveChallenge

/-- Interpret the verifier-challenge oracle by a fixed public challenge vector and leave
the prover's ambient oracle unchanged. -/
def fixedChallengeRight (chals : pSpec.Challenges) :
    QueryImpl [pSpec.Challenge]ₒ (OracleComp oSpec) :=
  fun q => (pure (chals q.1) : OracleComp oSpec (pSpec.Challenge q.1))

/-- A canonical challenge query is interpreted by the corresponding entry of the
fixed challenge vector. -/
theorem simulateQ_fixedChallenge_getChallenge
    (chals : pSpec.Challenges) (i : pSpec.ChallengeIdx) :
    simulateQ (fixedChallengeRight (oSpec := oSpec) chals)
        (pSpec.getChallenge i) =
      (pure (chals i) : OracleComp oSpec (pSpec.Challenge i)) := by
  unfold ProtocolSpec.getChallenge
  change simulateQ (fixedChallengeRight (oSpec := oSpec) chals)
      (liftM ([pSpec.Challenge]ₒ.query ⟨i, ()⟩)) = _
  exact (simulateQ_spec_query
    (fixedChallengeRight (oSpec := oSpec) chals) ⟨i, ()⟩).trans rfl

/-- The combined fixed-challenge handler. -/
def fixedChallengeImpl (chals : pSpec.Challenges) :
    QueryImpl (oSpec + [pSpec.Challenge]ₒ) (OracleComp oSpec) :=
  (QueryImpl.id' oSpec) + fixedChallengeRight (oSpec := oSpec) chals

/-- Project a simulated run to its transcript and the checkpoint named by its returned
handle.  This observation retains the final prover state while hiding the private store. -/
def observeRunCheckpoint (P : ProverInteraction oSpec pSpec) (i : Fin (n + 1))
    (result : (pSpec.Transcript i × RunId) × RunStore P) :
    pSpec.Transcript i × Option (Prover.Checkpoint P) :=
  (result.1.1, (show List (Prover.Checkpoint P) from result.2)[(show ℕ from result.1.2)]?)

/-- The checkpoint-level direct semantics of one fixed-challenge round.  Junk
checkpoints reproduce the handler's totalized behavior. -/
def checkpointStep [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec) (chals : pSpec.Challenges) (j : Fin n)
    (current : pSpec.Transcript j.castSucc × Option (Prover.Checkpoint P)) :
    OracleComp oSpec (pSpec.Transcript j.succ × Option (Prover.Checkpoint P)) := by
  let ⟨transcript, checkpoint⟩ := current
  match hDir : pSpec.dir j with
  | .V_to_P =>
      let c := chals ⟨j, hDir⟩
      match checkpoint with
      | some (.pendingChal i k) =>
          if hi : i = ⟨j, hDir⟩ then
            exact do
              let cp ← normalizeCheckpoint P ⟨j.succ, (hi ▸ k) c⟩
              pure (transcript.concat c, some cp)
          else
            exact pure (transcript.concat c, checkpoint)
      | _ => exact pure (transcript.concat c, checkpoint)
  | .P_to_V =>
      match checkpoint with
      | some (.atRound i s) =>
          if hi : i = j.castSucc then
            exact do
              let ⟨msg, s'⟩ ← P.sendMessage ⟨j, hDir⟩ (hi ▸ s)
              let cp ← normalizeCheckpoint P ⟨j.succ, s'⟩
              pure (transcript.concat msg, some cp)
          else
            exact pure
              (transcript.concat (default : pSpec.Message ⟨j, hDir⟩), checkpoint)
      | _ =>
          exact pure
            (transcript.concat (default : pSpec.Message ⟨j, hDir⟩), checkpoint)

/-- Direct checkpoint semantics for the canonical straight-line program. -/
def checkpointRunToRound [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec) (chals : pSpec.Challenges)
    (i : Fin (n + 1)) :
    OracleComp oSpec (pSpec.Transcript i × Option (Prover.Checkpoint P)) :=
  Fin.induction
    (do
      let cp ← normalizeCheckpoint P ⟨0, P.init⟩
      pure (default, some cp))
    (fun j prev => prev >>= checkpointStep P chals j)
    i

/-- One straight-line oracle step depends on the private store only through the
checkpoint named by the current handle. -/
theorem seededImpl_observe_straightlineStep
    [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec) (chals : pSpec.Challenges) (j : Fin n)
    (transcript : pSpec.Transcript j.castSucc) (h : RunId) (store : RunStore P) :
    observeRunCheckpoint P j.succ <$>
        ((simulateQ (seededImpl (StmtIn := StmtIn) P)
          (straightlineScriptStep chals j (transcript, h))).run store) =
      checkpointStep P chals j
        (transcript,
          (show List (Prover.Checkpoint P) from store)[(show ℕ from h)]?) := by
  simp only [straightlineScriptStep]
  split <;> rename_i hScript
  all_goals simp only [checkpointStep]
  all_goals split <;> rename_i hCheckpoint
  all_goals
    have hDirections := hScript.symm.trans hCheckpoint
    cases hDirections
  all_goals
    simp_all [observeRunCheckpoint, seededImpl, appendCheckpoint]
  all_goals split <;>
    simp_all [observeRunCheckpoint, seededImpl, appendCheckpoint]
  all_goals split <;>
    simp_all [observeRunCheckpoint, seededImpl, appendCheckpoint]

/-- Simulating the canonical program through the seeded handler is exactly the direct
checkpoint semantics, at every round. -/
theorem seededImpl_straightlineTo_eq_checkpointRunToRound
    [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec) (stmt : StmtIn) (chals : pSpec.Challenges)
    (i : Fin (n + 1)) :
    observeRunCheckpoint P i <$>
        ((simulateQ (seededImpl (StmtIn := StmtIn) P)
          (straightlineScriptTo stmt chals i)).run []) =
      checkpointRunToRound P chals i := by
  induction i using Fin.induction with
  | zero =>
      simp [straightlineScriptTo, straightlineScriptStep, checkpointRunToRound,
        observeRunCheckpoint,
        seededImpl, appendCheckpoint]
  | succ j ih =>
      rw [show straightlineScriptTo stmt chals j.succ =
          straightlineScriptTo stmt chals j.castSucc >>= straightlineScriptStep chals j by
        simp [straightlineScriptTo]]
      simp only [simulateQ_bind, StateT.run_bind, map_bind]
      calc
        _ = (do
            let a ←
              (simulateQ (seededImpl (StmtIn := StmtIn) P)
                (straightlineScriptTo stmt chals j.castSucc)).run []
            checkpointStep P chals j (observeRunCheckpoint P j.castSucc a)) := by
              apply bind_congr
              intro a
              rcases a with ⟨⟨transcript, h⟩, store⟩
              exact seededImpl_observe_straightlineStep P chals j transcript h store
        _ = (checkpointRunToRound P chals j.castSucc >>= checkpointStep P chals j) := by
              rw [← bind_map_left, ih]
        _ = checkpointRunToRound P chals j.succ := by
              simp [checkpointRunToRound]

/-- Normalizing before one direct round gives exactly the checkpoint step used by the
seeded handler. -/
theorem normalize_bind_checkpointStep_eq_directRound
    [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec) (chals : pSpec.Challenges) (j : Fin n)
    (transcript : pSpec.Transcript j.castSucc) (state : P.PrvState j.castSucc) :
    (do
      let cp ← normalizeCheckpoint P ⟨j.castSucc, state⟩
      checkpointStep P chals j (transcript, some cp)) =
    (do
      let current ←
        (match hDir : pSpec.dir j with
          | .V_to_P => do
              let k ← P.receiveChallenge ⟨j, hDir⟩ state
              pure (transcript.concat (chals ⟨j, hDir⟩),
                k (chals ⟨j, hDir⟩))
          | .P_to_V => do
              let ⟨msg, state'⟩ ← P.sendMessage ⟨j, hDir⟩ state
              pure (transcript.concat msg, state') :
            OracleComp oSpec (pSpec.Transcript j.succ × P.PrvState j.succ))
      let cp ← normalizeCheckpoint P ⟨j.succ, current.2⟩
      pure (current.1, some cp)) := by
  simp [normalizeCheckpoint, checkpointStep]
  all_goals split <;> rename_i hNorm
  all_goals simp_all [normalizeCheckpoint, checkpointStep]
  all_goals split <;> rename_i hStep
  all_goals
    have hDirections := hNorm.symm.trans hStep
    cases hDirections
  all_goals simp_all [normalizeCheckpoint, checkpointStep]

/-- Checkpoint execution is the fixed-challenge specialization of direct prover
execution, followed by normalization of the current state. -/
theorem checkpointRunToRound_eq_runToRoundFixed
    [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec) (chals : pSpec.Challenges)
    (i : Fin (n + 1)) :
    checkpointRunToRound P chals i =
      (do
        let ⟨transcript, state⟩ ← runToRoundFixed P chals i
        let cp ← normalizeCheckpoint P ⟨i, state⟩
        pure (transcript, some cp)) := by
  induction i using Fin.induction with
  | zero =>
      simp [checkpointRunToRound, runToRoundFixed]
  | succ j ih =>
      rw [show checkpointRunToRound P chals j.succ =
          checkpointRunToRound P chals j.castSucc >>= checkpointStep P chals j by
        simp [checkpointRunToRound]]
      rw [show runToRoundFixed P chals j.succ =
          (runToRoundFixed P chals j.castSucc >>= fun current => do
            let ⟨transcript, state⟩ := current
            match hDir : pSpec.dir j with
            | .V_to_P => do
                let k ← P.receiveChallenge ⟨j, hDir⟩ state
                pure (transcript.concat (chals ⟨j, hDir⟩),
                  k (chals ⟨j, hDir⟩))
            | .P_to_V => do
                let ⟨msg, state'⟩ ← P.sendMessage ⟨j, hDir⟩ state
                pure (transcript.concat msg, state')) by
        simp [runToRoundFixed]]
      rw [ih]
      simp only [bind_assoc]
      apply bind_congr
      intro current
      rcases current with ⟨transcript, state⟩
      exact normalize_bind_checkpointStep_eq_directRound P chals j transcript state

/-- The fixed-challenge direct semantics is `Prover.runToRound` with the challenge
oracle interpreted by the supplied challenge vector. -/
theorem runToRoundFixed_eq_runToRound
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (chals : pSpec.Challenges)
    (i : Fin (n + 1)) :
    runToRoundFixed (P.toInteraction stmt wit) chals i =
      simulateQ (fixedChallengeImpl chals) (P.runToRound i stmt wit) := by
  induction i using Fin.induction with
  | zero =>
      simp [runToRoundFixed, Prover.runToRound, Prover.toInteraction]
  | succ j ih =>
      rw [show runToRoundFixed (P.toInteraction stmt wit) chals j.succ =
          (runToRoundFixed (P.toInteraction stmt wit) chals j.castSucc >>=
            fun current => do
              match hDir : pSpec.dir j with
              | .V_to_P => do
                  let k ← P.receiveChallenge ⟨j, hDir⟩ current.2
                  pure (current.1.concat (chals ⟨j, hDir⟩),
                    k (chals ⟨j, hDir⟩))
              | .P_to_V => do
                  let ⟨msg, state'⟩ ← P.sendMessage ⟨j, hDir⟩ current.2
                  pure (current.1.concat msg, state')) by
        simp [runToRoundFixed]]
      rw [show P.runToRound j.succ stmt wit =
          P.processRound j (P.runToRound j.castSucc stmt wit) by
        simp [Prover.runToRound]]
      unfold Prover.processRound
      rw [simulateQ_bind, ih]
      apply bind_congr
      intro current
      rcases current with ⟨transcript, state⟩
      dsimp only
      split <;> rename_i hDirect
      all_goals split <;> rename_i hSource
      all_goals
        have hDirections := hDirect.symm.trans hSource
        cases hDirections
      all_goals
        have hProof : hSource = hDirect := Subsingleton.elim _ _
        cases hProof
      all_goals
        simp_all [fixedChallengeImpl, QueryImpl.simulateQ_add_liftM_left]
      all_goals
        simp_all [fixedChallengeImpl, QueryImpl.simulateQ_add_liftM_right]
      let resumeWith := fun x : pSpec.Challenge ⟨j, hDirect⟩ =>
        (fun a => (transcript.concat x, a x)) <$>
          P.receiveChallenge ⟨j, hDirect⟩ state
      change
        (pure (chals ⟨j, hDirect⟩) :
            OracleComp oSpec (pSpec.Challenge ⟨j, hDirect⟩)) >>= resumeWith =
          simulateQ (fixedChallengeRight (oSpec := oSpec) chals)
              (pSpec.getChallenge ⟨j, hDirect⟩) >>= resumeWith
      exact congrArg (fun mx => mx >>= resumeWith)
        (simulateQ_fixedChallenge_getChallenge
          (oSpec := oSpec) chals ⟨j, hDirect⟩).symm

/-- Straight-line adequacy for the flat seeded handler.

The right side is the repository's actual `Prover.runToRound` execution with its
challenge oracle interpreted by `chals`; no independently reimplemented direct program
appears in the statement.  The observed checkpoint retains the final prover state, so a
handler that returns a constant transcript or ignores the prover cannot satisfy this
equality. -/
theorem seededImpl_straightline_eq_runToRound
    [∀ i, Inhabited (pSpec.Message i)]
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (chals : pSpec.Challenges) :
    observeRunCheckpoint (P.toInteraction stmt wit) (Fin.last n) <$>
        ((simulateQ (seededImpl (StmtIn := StmtIn) (P.toInteraction stmt wit))
          (straightlineScript stmt chals)).run []) =
      (fun result =>
        (result.1, some (Prover.Checkpoint.atRound (Fin.last n) result.2))) <$>
        simulateQ (fixedChallengeImpl chals)
          (P.runToRound (Fin.last n) stmt wit) := by
  change observeRunCheckpoint (P.toInteraction stmt wit) (Fin.last n) <$>
      ((simulateQ (seededImpl (StmtIn := StmtIn) (P.toInteraction stmt wit))
        (straightlineScriptTo stmt chals (Fin.last n))).run []) = _
  rw [seededImpl_straightlineTo_eq_checkpointRunToRound
      (StmtIn := StmtIn) (P.toInteraction stmt wit) stmt chals,
    checkpointRunToRound_eq_runToRoundFixed (P.toInteraction stmt wit) chals,
    runToRoundFixed_eq_runToRound P stmt wit chals]
  simp [normalizeCheckpoint]

/-- Two forks of the same valid handle apply one shared realized continuation.
The equations differ only in the challenge supplied to that same `k`. -/
theorem seededImpl_fork_shares_prefix [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec) (h : RunId) (i : pSpec.ChallengeIdx)
    (c₁ c₂ : pSpec.Challenge i) (store : RunStore P)
    (k : pSpec.Challenge i → P.PrvState i.1.succ)
    (hstore :
      (show List (Prover.Checkpoint P) from store)[(show ℕ from h)]? =
        some (.pendingChal i k)) :
    (seededImpl (StmtIn := StmtIn) P (.feedChal h i c₁)).run store =
        (do
          let cp ← normalizeCheckpoint P ⟨i.1.succ, k c₁⟩
          pure (appendCheckpoint P store cp)) ∧
      (seededImpl (StmtIn := StmtIn) P (.feedChal h i c₂)).run store =
        (do
          let cp ← normalizeCheckpoint P ⟨i.1.succ, k c₂⟩
          pure (appendCheckpoint P store cp)) :=
  ⟨seededImpl_feedChal_pure P h i c₁ store k hstore,
    seededImpl_feedChal_pure P h i c₂ store k hstore⟩

/-- Advancing a valid send checkpoint runs exactly `P.sendMessage` and normalizes the
returned state.  This is the send-round unfolding used by the direct
`runToRoundFixed` execution. -/
theorem seededImpl_sendMsg_eq_processRound [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec) (h : RunId) (i : pSpec.MessageIdx)
    (store : RunStore P) (s : P.PrvState i.1.castSucc)
    (hstore :
      (show List (Prover.Checkpoint P) from store)[(show ℕ from h)]? =
        some (.atRound i.1.castSucc s)) :
    (seededImpl (StmtIn := StmtIn) P (.sendMsg h i)).run store =
      (do
        let ⟨msg, s'⟩ ← P.sendMessage i s
        let cp ← normalizeCheckpoint P ⟨i.1.succ, s'⟩
        let ⟨child, store'⟩ := appendCheckpoint P store cp
        pure ((msg, child), store')) := by
  unfold seededImpl
  simp only [StateT.run_mk]
  rw [hstore]
  simp only
  split
  · rfl
  · contradiction

end ProverInteraction

/--
info: 'Extractor.ProverInteraction.appendCheckpoint_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.appendCheckpoint_lookup

/--
info: 'Extractor.ProverInteraction.seededImpl_store_appendOnly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.seededImpl_store_appendOnly

/--
info: 'Extractor.ProverInteraction.simulateQ_fixedChallenge_getChallenge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.simulateQ_fixedChallenge_getChallenge

/--
info: 'Extractor.ProverInteraction.seededImpl_observe_straightlineStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.seededImpl_observe_straightlineStep

/--
info: 'Extractor.ProverInteraction.seededImpl_straightlineTo_eq_checkpointRunToRound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.seededImpl_straightlineTo_eq_checkpointRunToRound

/--
info: 'Extractor.ProverInteraction.normalize_bind_checkpointStep_eq_directRound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.normalize_bind_checkpointStep_eq_directRound

/--
info: 'Extractor.ProverInteraction.checkpointRunToRound_eq_runToRoundFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.checkpointRunToRound_eq_runToRoundFixed

/--
info: 'Extractor.ProverInteraction.runToRoundFixed_eq_runToRound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.runToRoundFixed_eq_runToRound

/--
info: 'Extractor.ProverInteraction.seededImpl_straightline_eq_runToRound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.seededImpl_straightline_eq_runToRound

/--
info: 'Extractor.ProverInteraction.seededImpl_feedChal_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.seededImpl_feedChal_pure

/--
info: 'Extractor.ProverInteraction.seededImpl_fork_shares_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.seededImpl_fork_shares_prefix

/--
info: 'Extractor.ProverInteraction.seededImpl_sendMsg_eq_processRound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.seededImpl_sendMsg_eq_processRound

-- def SimOracle.proverImpl (P : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
--     SimOracle.Stateless (OracleSpec.proverOracle pSpec StmtIn) oSpec := sorry

structure Rewinding (oSpec : OracleSpec ι)
    (StmtIn StmtOut WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  /-- The state of the extractor -/
  ExtState : Type
  /-- Simulate challenge queries for the prover -/
  simChallenge : QueryImpl [pSpec.Challenge]ₒ (StateT ExtState (OracleComp [pSpec.Challenge]ₒ))
  /-- Simulate oracle queries for the prover -/
  simOracle : QueryImpl oSpec (StateT ExtState (OracleComp oSpec))
  /-- Run the extractor with the prover's oracle interface, allowing for calling the prover multiple
    times -/
  runExt : StmtOut → WitOut → StmtIn →
    StateT ExtState (OracleComp (OracleSpec.proverOracle StmtIn pSpec)) WitIn

-- Challenge: need environment to update & maintain the prover's states after each extractor query
-- This will hopefully go away after the refactor of prover's type to be an iterated monad

-- def Rewinding.run
--     (P : Prover.Adaptive pSpec oSpec StmtIn WitIn StmtOut WitOut)
--     (E : Extractor.Rewinding pSpec oSpec StmtIn StmtOut WitIn WitOut) :
--     OracleComp oSpec WitIn := sorry

end Rewinding

end Extractor
