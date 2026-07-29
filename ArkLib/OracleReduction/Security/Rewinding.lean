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

namespace RunId

/-- Reveal a handle only to the private implementation of the handle table. -/
@[inline]
def toNat (h : RunId) : ℕ := h

end RunId

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
        match entries[h.toNat]? with
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
        match entries[h.toNat]? with
        | some (Prover.Checkpoint.pendingChal j k) =>
            if hj : j = i then do
              let cp ← normalizeCheckpoint P ⟨i.1.succ, (hj ▸ k) c⟩
              pure (appendCheckpoint P store cp)
            else
              pure (h, store)
        | _ => pure (h, store)

/-- Every allocated checkpoint is appended after the existing store.  Since
`seededImpl` uses this operation for every successful allocation and leaves the store
unchanged on junk handles, no query can mutate an existing checkpoint. -/
theorem seededImpl_store_appendOnly (P : ProverInteraction oSpec pSpec)
    (store : RunStore P) (cp : Prover.Checkpoint P) :
    (appendCheckpoint P store cp).2 = List.append store [cp] :=
  rfl

/-- Feeding a challenge through a valid handle applies the continuation already stored
at that handle.  The only subsequent oracle effects are those of normalizing the child
state; the computation that produced `k` is not re-run. -/
theorem seededImpl_feedChal_pure [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec) (h : RunId) (i : pSpec.ChallengeIdx)
    (c : pSpec.Challenge i) (store : RunStore P)
    (k : pSpec.Challenge i → P.PrvState i.1.succ)
    (hstore :
      (show List (Prover.Checkpoint P) from store)[h.toNat]? =
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
    (fun j prev => do
      let ⟨transcript, h⟩ ← prev
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
          pure (transcript.concat msg, child))
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

/-- Two forks of the same valid handle apply one shared realized continuation.
The equations differ only in the challenge supplied to that same `k`. -/
theorem seededImpl_fork_shares_prefix [∀ i, Inhabited (pSpec.Message i)]
    (P : ProverInteraction oSpec pSpec) (h : RunId) (i : pSpec.ChallengeIdx)
    (c₁ c₂ : pSpec.Challenge i) (store : RunStore P)
    (k : pSpec.Challenge i → P.PrvState i.1.succ)
    (hstore :
      (show List (Prover.Checkpoint P) from store)[h.toNat]? =
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
      (show List (Prover.Checkpoint P) from store)[h.toNat]? =
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
info: 'Extractor.ProverInteraction.seededImpl_store_appendOnly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProverInteraction.seededImpl_store_appendOnly

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
