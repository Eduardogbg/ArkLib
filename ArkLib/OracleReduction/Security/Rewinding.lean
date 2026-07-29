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
