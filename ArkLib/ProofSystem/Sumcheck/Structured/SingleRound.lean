/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Sumcheck.Structured
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Structured (Witness-Mode) Sumcheck — Single-Round Primitives

This file collects single-round primitives for the structured (witness-mode) sumcheck:

- `getSumcheckRoundPoly` — derive the univariate `g_i(X)` sent by the prover from
  the multiquadratic round polynomial `H_i(X_i, ..., X_{ℓ-1})` by summing over the
  remaining boolean-hypercube directions.
- `pSpecSumcheckRound` — the two-message protocol spec for one round
  (`P_to_V : L⦃≤ 2⦄[X]`, `V_to_P : L`).
- `OracleInterface` and `SampleableType` instances for `pSpecSumcheckRound`.

These were originally housed in `Binius.BinaryBasefold.Prelude` and
`Binius.RingSwitching.Spec`. They are fully generic (no binary-tower or
ring-switching dependencies) and have been promoted here so that future
ring-switching protocols (Hachi, Galois-ring PCS) can reuse them without
depending on `Binius.*`.

PR 2b of `GENERIC_RING_SWITCHING_PLAN.md` will extend this file with the per-round
prover/verifier/reduction.
-/

namespace Sumcheck.Structured

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial

noncomputable section

section RoundPoly

variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ] (𝓑 : Fin 2 ↪ L)

/- `H_i(X_i, ..., X_{ℓ-1})` -> `g_i(X)` derivation -/
noncomputable def getSumcheckRoundPoly (i : Fin ℓ) (h : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)])
    : L⦃≤ 2⦄[X] := by
  have h_i_lt_ℓ : ℓ - ↑i.castSucc > 0 := by
    have hi := i.2
    exact Nat.zero_lt_sub_of_lt hi
  have h_count_eq : ℓ - ↑i.castSucc - 1 + 1 = ℓ - ↑i.castSucc := by
    omega
  let challenges : Fin 0 → L := fun (j : Fin 0) => j.elim0
  let curH_cast : L[X Fin ((ℓ - ↑i.castSucc - 1) + 1)] := by
    convert h.val
  let g := ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc - 1), curH_cast ⸨X ⦃0⦄, challenges, x⸩' (by omega)
  exact ⟨g, by
    have h_deg_le_2 : g ∈ L⦃≤ 2⦄[X] := by
      simp only [g]
      let hDegIn := Sumcheck.Spec.SingleRound.sumcheck_roundPoly_degreeLE
        (R := L) (D := 𝓑) (n := ℓ - ↑i.castSucc - 1) (deg := 2) (i := ⟨0, by omega⟩)
        (challenges := fun j => j.elim0) (poly := curH_cast)
      have h_in_degLE : curH_cast ∈ L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc - 1 + 1)] := by
        rw! (castMode := .all) [h_count_eq]
        dsimp only [Fin.coe_castSucc, eq_mpr_eq_cast, curH_cast]
        rw [eqRec_eq_cast, cast_cast, cast_eq]
        exact h.property
      let res := hDegIn h_in_degLE
      exact res
    rw [mem_degreeLE] at h_deg_le_2 ⊢
    exact h_deg_le_2
  ⟩

end RoundPoly

section ProtocolSpec

variable (L : Type) [Semiring L]

/-- Protocol spec for one round of the structured sumcheck:
P sends a degree-≤2 univariate `h_i(X) ∈ L⦃≤ 2⦄[X]`; V samples a challenge `r'_i ∈ L`. -/
@[reducible]
def pSpecSumcheckRound : ProtocolSpec 2 := ⟨![Direction.P_to_V, Direction.V_to_P], ![L⦃≤ 2⦄[X], L]⟩

instance : ∀ j, OracleInterface ((pSpecSumcheckRound L).Message j)
  | ⟨0, _⟩ => OracleInterface.instDefault -- h_i(X) polynomial
  | ⟨1, _⟩ => OracleInterface.instDefault -- challenge r'_i

variable [Fintype L] [DecidableEq L] [SampleableType L]

instance : ∀ j, SampleableType ((pSpecSumcheckRound L).Challenge j)
  | ⟨0, h0⟩ => by nomatch h0
  | ⟨1, _⟩ => by
    simp only [Challenge, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    infer_instance

end ProtocolSpec

/-! ## Iterated single round of the structured sumcheck

The per-round prover/verifier/reduction. Generic in:
- the underlying carrier `L` (anything `CommRing`),
- the protocol context `Context : Type` (Binius RingSwitching plugs in
  `RingSwitchingBaseContext κ L K ℓ`; Hachi will plug in its own),
- the external oracle statements `OStmtIn : ιₛᵢ → Type` (Binius plugs in
  `aOStmtIn.OStmtIn`).

The state machine has three states per round:
- `0`: before any messages — input statement + oracle product + witness.
- `1`: after P sends `h_i(X)` — adds the univariate.
- `2`: after V samples `r'_i` — adds the challenge.

The error bound `iteratedSumcheckRoundKnowledgeError` is the standard `2 / |L|`
Schwartz–Zippel bound; it doesn't depend on `Context` or `OStmtIn`. -/

section IteratedSumcheck

variable {L : Type} [CommRing L] [DecidableEq L] (ℓ : ℕ) [NeZero ℓ] (𝓑 : Fin 2 ↪ L)
variable (Context : Type) {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
  [Oₛᵢ : ∀ j, OracleInterface (OStmtIn j)]

/-- State machine for the per-round prover of the structured sumcheck.
- `0`: pre-message.
- `1`: after the prover has sent `h_i(X)`.
- `2`: after the verifier has sampled `r'_i`. -/
def iteratedSumcheckPrvState (i : Fin ℓ) : Fin (2 + 1) → Type := fun
  -- Initial : current witness x t_eval_point x challenges
  | ⟨0, _⟩ => (Statement (L := L) (ℓ := ℓ) Context i.castSucc
    × (∀ j, OStmtIn j)) × SumcheckWitness L ℓ i.castSucc
  -- After sending h_i(X)
  | ⟨1, _⟩ => Statement (L := L) (ℓ := ℓ) Context i.castSucc
    × (∀ j, OStmtIn j) × SumcheckWitness L ℓ i.castSucc × L⦃≤ 2⦄[X]
  -- After receiving r'_i
  | _ => Statement (L := L) (ℓ := ℓ) Context i.castSucc ×
    (∀ j, OStmtIn j) ×
    SumcheckWitness L ℓ i.castSucc × L⦃≤ 2⦄[X] × L

/-- Compute the final per-round output (statement-out, oracle statement-out, witness-out)
from the after-challenge prover state. -/
noncomputable def getIteratedSumcheckProverFinalOutput (i : Fin ℓ)
    (finalPrvState : iteratedSumcheckPrvState (L := L) ℓ Context (OStmtIn := OStmtIn) i 2) :
    ((Statement (L := L) (ℓ := ℓ) Context i.succ
      × (∀ j, OStmtIn j)) × SumcheckWitness L ℓ i.succ)
  := by
  let (stmtIn, oStmtIn, witIn, h_i, r_i') := finalPrvState
  let newSumcheckTarget : L := h_i.val.eval r_i'
  let stmtOut : Statement (L := L) (ℓ := ℓ) Context i.succ := {
    ctx := stmtIn.ctx,
    sumcheck_target := newSumcheckTarget,
    challenges := Fin.snoc stmtIn.challenges r_i'
  }
  let challenges : Fin (1) → L := fun _cId => r_i'
  let witOut : SumcheckWitness L ℓ i.succ := by
    let projectedH := fixFirstVariablesOfMQP (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
      (H := witIn.H.val) (challenges := challenges)
    exact {
      t' := witIn.t',
      H := ⟨projectedH, by
        have hp := witIn.H.property
        simpa using
          (fixFirstVariablesOfMQP_degreeLE (L := L) (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
            (poly := witIn.H.val) (challenges := challenges) (deg := 2) hp)
      ⟩
    }
  have _h_succ_val : i.succ.val = i.val + 1 := rfl
  exact ⟨⟨stmtOut, oStmtIn⟩, witOut⟩

/-- The prover for the `i`-th round of the structured sumcheck.

`sendMessage 0` runs `getSumcheckRoundPoly` to derive `h_i(X)` from the multiquadratic
`H_i`. `receiveChallenge 1` stores the verifier's challenge `r'_i`. `output` advances
the witness via `getIteratedSumcheckProverFinalOutput`. -/
noncomputable def iteratedSumcheckOracleProver (i : Fin ℓ) :
  OracleProver (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context i.castSucc)
    (OStmtIn := OStmtIn)
    (WitIn := SumcheckWitness L ℓ i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context i.succ)
    (OStmtOut := OStmtIn)
    (WitOut := SumcheckWitness L ℓ i.succ)
    (pSpec := pSpecSumcheckRound L) where

  PrvState := iteratedSumcheckPrvState (L := L) ℓ Context (OStmtIn := OStmtIn) i

  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => ((stmt, oStmt), wit)

  sendMessage -- There are 2 messages in the pSpec
  | ⟨0, _⟩ => fun ⟨⟨stmt, oStmt⟩, wit⟩ => do
    let curH : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)] := wit.H
    let h_i : L⦃≤ 2⦄[X] := by
      exact getSumcheckRoundPoly ℓ 𝓑 (i := i) curH
    pure ⟨h_i, (stmt, oStmt, wit, h_i)⟩
  | ⟨1, _⟩ => by contradiction

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction
  | ⟨1, _⟩ => fun ⟨stmt, oStmt, wit, h_i⟩ => do
    pure (fun r_i' => (stmt, oStmt, wit, h_i, r_i'))

  output := fun finalPrvState =>
    let res :=
      getIteratedSumcheckProverFinalOutput (L := L) ℓ Context (OStmtIn := OStmtIn) i finalPrvState
    pure res

/-- The oracle verifier for the `i`-th round of the structured sumcheck.

Receives `h_i(X)` from the prover, checks `s_i ?= h_i(0) + h_i(1)`, samples `r'_i ∈ L`
as the second message, and outputs the updated statement with `s_{i+1} := h_i(r'_i)`. -/
noncomputable def iteratedSumcheckOracleVerifier (i : Fin ℓ) :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context i.castSucc)
    (OStmtIn := OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context i.succ)
    (OStmtOut := OStmtIn)
    (pSpec := pSpecSumcheckRound L) where

  verify := fun stmtIn pSpecChallenges => do
    -- Message 0: receive h_i(X) from prover.
    let h_i : L⦃≤ 2⦄[X] ← query (spec := [(pSpecSumcheckRound L).Message]ₒ)
      ⟨⟨0, rfl⟩, ()⟩

    -- Sumcheck check: s_i ?= h_i(0) + h_i(1).
    let sumcheck_check := h_i.val.eval 0 + h_i.val.eval 1 = stmtIn.sumcheck_target
    unless sumcheck_check do
      let dummyStmt : Statement (L := L) (ℓ := ℓ) Context i.succ := {
        ctx := stmtIn.ctx,
        sumcheck_target := 0,
        challenges := Fin.snoc stmtIn.challenges 0
      }
      return dummyStmt

    -- Message 1: V samples r'_i and sends it to P.
    let r_i' : L := pSpecChallenges ⟨1, rfl⟩

    let stmtOut : Statement (L := L) (ℓ := ℓ) Context i.succ := {
      ctx := stmtIn.ctx,
      sumcheck_target := h_i.val.eval r_i',
      challenges := Fin.snoc stmtIn.challenges r_i'
    }
    pure stmtOut
  embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
  hEq := fun _ => rfl

/-- The oracle reduction bundling the per-round prover and verifier. -/
noncomputable def iteratedSumcheckOracleReduction (i : Fin ℓ) :
  OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context i.castSucc)
    (OStmtIn := OStmtIn)
    (WitIn := SumcheckWitness L ℓ i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context i.succ)
    (OStmtOut := OStmtIn)
    (WitOut := SumcheckWitness L ℓ i.succ)
    (pSpec := pSpecSumcheckRound L) where
  prover := iteratedSumcheckOracleProver (L := L) ℓ 𝓑 Context (OStmtIn := OStmtIn) i
  verifier := iteratedSumcheckOracleVerifier (L := L) ℓ Context (OStmtIn := OStmtIn) i

end IteratedSumcheck

section IteratedError

variable (L : Type) [Fintype L] (ℓ : ℕ)

/-- Round-by-round knowledge error for a single round of the structured sumcheck:
the standard Schwartz–Zippel bound `2 / |L|`. -/
def iteratedSumcheckRoundKnowledgeError (_ : Fin ℓ) : NNReal := (2 : NNReal) / (Fintype.card L)

end IteratedError

end

end Sumcheck.Structured
