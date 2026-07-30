/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Gomes
-/

import ArkLib.CommitmentScheme.Basic
import ArkLib.OracleReduction.Security.Implications
import ArkLib.Interaction.Security.Rewinding
import ArkLib.Interaction.Security.TreeExtraction

/-!
# IPA polynomial-commitment opening (WIP skeleton)

This file only pins the intended interfaces. Every definition and theorem below is a stub with a
`sorry` body; no IPA extraction or knowledge-soundness result is proved here.

The final security proof will instantiate the coordinate-wise transcript-tree notion from
`ArkLib.OracleReduction.Security.SpecialSoundness` (`distinctShape` and
`Verifier.treeSpecialSound`) at arity five, then adapt that tree extractor to the rewinding
infrastructure in `Interaction.Security.TranscriptForest`, `Rewinding`, `TreeExtraction`, and
`TwoFactorRun`.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace Commitment.IPA

/-- Public input to an IPA polynomial-opening proof: a commitment and a claimed evaluation. WIP. -/
structure OpeningStatement (Commitment Point Scalar : Type) where
  commitment : Commitment
  point : Point
  value : Scalar

/-- Private input to an IPA polynomial-opening proof. The coefficient and blinding representations
are parameters until the concrete IPA commitment layer is fixed. WIP. -/
structure OpeningWitness (Polynomial Blinding : Type) where
  polynomial : Polynomial
  blinding : Blinding

/-- The IPA opening relation, separated from the interactive verifier so the algebraic extraction
lemma can be proved independently of the forest/rewinding adapter. WIP stub. -/
def openingRelation
    {Commitment Point Scalar Polynomial Blinding : Type}
    (commits : Polynomial → Blinding → Commitment)
    (evaluates : Polynomial → Point → Scalar) :
    Set (OpeningStatement Commitment Point Scalar × OpeningWitness Polynomial Blinding) := by
  sorry

/-- The interactive IPA opening verifier. Its concrete messages and challenges will be supplied by
the IPA protocol specification; this signature is the boundary consumed by `treeSpecialSound`.
WIP stub. -/
def openingVerifier
    {iota : Type} {oSpec : OracleSpec iota}
    {Commitment Point Scalar StmtOut : Type} {n : ℕ} {pSpec : ProtocolSpec n} :
    Verifier oSpec (OpeningStatement Commitment Point Scalar) StmtOut pSpec := by
  sorry

/-- Five siblings are requested at each IPA challenge coordinate. This is the arity passed to
`distinctShape`; pairwise distinctness remains the shape predicate supplied by #530. -/
def arityFive {n : ℕ} {pSpec : ProtocolSpec n} : pSpec.ChallengeIdx → ℕ := fun _ => 5

/-- Algebraic IPA extraction from an accepting `distinctShape arityFive` challenge tree.
This is the protocol-specific tree-special-soundness obligation and is entirely unproved. It uses
the merged #530 `Verifier.treeSpecialSound` interface. WIP stub. -/
theorem opening_treeSpecialSound
    {iota : Type} {oSpec : OracleSpec iota}
    {Commitment Point Scalar Polynomial Blinding StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    {sigma : Type} (init : ProbComp sigma) (impl : QueryImpl oSpec (StateT sigma ProbComp))
    (verifier : Verifier oSpec (OpeningStatement Commitment Point Scalar) StmtOut pSpec)
    (relIn : Set (OpeningStatement Commitment Point Scalar × OpeningWitness Polynomial Blinding))
    (relOut : Set (StmtOut × WitOut)) :
    verifier.treeSpecialSound init impl (distinctShape arityFive) relIn relOut := by
  sorry

/-- Knowledge-soundness adapter for the IPA opening verifier. The proof will translate the #530
coordinate-wise tree into PR #3's transcript-forest representation and invoke its rewinding run,
cost, and success bounds. No adapter or probability proof is implemented yet. WIP stub. -/
theorem opening_knowledgeSoundness_of_treeSpecialSound
    {iota : Type} {oSpec : OracleSpec iota}
    {Commitment Point Scalar Polynomial Blinding StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)]
    {sigma : Type} (init : ProbComp sigma) (impl : QueryImpl oSpec (StateT sigma ProbComp))
    (verifier : Verifier oSpec (OpeningStatement Commitment Point Scalar) StmtOut pSpec)
    (relIn : Set (OpeningStatement Commitment Point Scalar × OpeningWitness Polynomial Blinding))
    (relOut : Set (StmtOut × WitOut)) (knowledgeError : ℝ≥0)
    (hTree : verifier.treeSpecialSound init impl (distinctShape arityFive) relIn relOut) :
    verifier.knowledgeSoundness init impl relIn relOut knowledgeError := by
  sorry

end Commitment.IPA
