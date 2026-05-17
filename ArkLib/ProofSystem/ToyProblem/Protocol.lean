/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.ToyProblem.Definitions

/-!
# Toy problem protocol (ABF26 Construction 6.2)

The interactive oracle reduction (IOR) `T[C, t]` of [ABF26] Construction
6.2 for the toy problem. The verifier holds an explicit input
`(v, μ₁, μ₂)` and has oracle access to the purported codewords
`f₁, f₂ : ι → F`. The protocol proceeds in three rounds:

  1. **Combination randomness** (V → P): the verifier sends `γ ←$ F`.
  2. **Prover claim** (P → V): the prover sends `g : Fin k → F`.
     In the honest case `g = F₁ + γ · F₂` is the combination of the
     underlying messages.
  3. **Spot-check randomness** (V → P): the verifier sends
     `x₁, …, xₜ ←$ ι`.

The verifier's decision is:

  * `⟨g, v⟩ = μ₁ + γ · μ₂` (linear constraint on the combined message),
  * for every `j ∈ Fin t`, the encoded message agrees with the
    combined oracle word at the spot-check positions:
      `C(g)(xⱼ) = f₁(xⱼ) + γ · f₂(xⱼ)`.

This file lays down the protocol's data shape (ProtocolSpec, statement
and witness types) and an explicit verifier matching the §6.1 decision
logic. The honest prover is stubbed; the soundness/completeness lemmas
(L6.6 / L6.8 of [ABF26]) are placed alongside their tagged sorries and
will be discharged in follow-up work.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (especially §6).

-/

namespace ToyProblem.Protocol

open ProtocolSpec OracleSpec OracleComp

variable {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F]
         [DecidableEq F]

section Spec

variable (k t : ℕ)

/-- Protocol specification for Construction 6.2: a three-round IOR with
verifier-first / verifier-last bracket.

  Round 0: `V → P` sends `γ : F` (combination randomness).
  Round 1: `P → V` sends `g : Fin k → F` (combined message claim).
  Round 2: `V → P` sends `(x₁, …, xₜ) : Fin t → ι` (spot-check positions).
-/
def pSpec : ProtocolSpec 3 :=
  { dir := ![.V_to_P, .P_to_V, .V_to_P]
    «Type» := ![F, Fin k → F, Fin t → ι] }

end Spec

section Stmt

variable (k : ℕ)

/-- Explicit input statement to the verifier: the linear-constraint
vector `v` and the two constraint values `μ₁, μ₂`. -/
structure StmtIn where
  /-- Linear-constraint vector `v ∈ F^k`. -/
  v : Fin k → F
  /-- First constraint value `μ₁`. -/
  μ₁ : F
  /-- Second constraint value `μ₂`. -/
  μ₂ : F

/-- Implicit oracle input statement: the two purported codewords
`f₁, f₂ : ι → F`. Verifier only queries them at spot-check positions. -/
def OStmtIn : Fin 2 → Type := fun _ ↦ ι → F

/-- Honest witness: a pair of underlying messages `M₁, M₂ : Fin k → F`
together with the (implicit) claim that `Fᵢ = encode(Mᵢ)` for both `i`.

We separate the messages from the codewords because the verifier in the
soundness game only sees the codewords (as oracles) and the prover (in
the knowledge-soundness game) is required to commit to the underlying
messages. -/
def WitIn : Type := Fin 2 → Fin k → F

/-- Output statement: the IOR is a *test* — the verifier outputs `Unit`
on accept (and short-circuits to `none` via `OptionT` on reject). -/
def StmtOut : Type := Unit

/-- The output of the IOR has no oracle component. -/
def OStmtOut : Fin 0 → Type := nofun

/-- Output witness: empty (the IOR doesn't reduce to a sub-claim with a
witness). -/
def WitOut : Type := Unit

end Stmt

section Verifier

variable {k t : ℕ} (encode : (Fin k → F) → (ι → F))

/-- The verifier's decision logic at the end of the protocol. Given the
explicit input `(v, μ₁, μ₂)`, the oracle codewords `(f₁, f₂)`, the
challenge `γ`, the prover's claim `g`, and the spot-check positions
`xs : Fin t → ι`, accept iff both checks pass:

  * `⟨g, v⟩ = μ₁ + γ · μ₂`
  * for every `j`, `encode(g)(xs j) = f₁(xs j) + γ · f₂(xs j)`.

This matches the decision in [ABF26] Construction 6.2. -/
def accepts
    (stmt : StmtIn (F := F) k) (f : Fin 2 → (ι → F))
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) : Prop :=
  (∑ j, g j * stmt.v j = stmt.μ₁ + γ * stmt.μ₂) ∧
  ∀ j : Fin t, encode g (xs j) = f 0 (xs j) + γ * f 1 (xs j)

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Honest completeness, point-form: if `stmt` and `wit` satisfy the
toy-problem relation and the oracle words are the honest encodings of
the underlying messages, then `accepts` holds for every `γ` and every
choice of spot-check positions.

This is the point-form version of perfect completeness for Construction
6.2 — it threads through the `OracleReduction` completeness theorem
once the prover object is wired up. -/
theorem accepts_of_relation {k t : ℕ} {encode : (Fin k → F) →ₗ[F] (ι → F)}
    (stmt : StmtIn (F := F) k)
    (wit : Fin 2 → Fin k → F)
    (_hwit : ∀ i, ∑ j, wit i j * stmt.v j = (if i = 0 then stmt.μ₁ else stmt.μ₂))
    (f : Fin 2 → (ι → F)) (_hf : ∀ i, f i = encode (wit i))
    (γ : F) (xs : Fin t → ι) :
    accepts (encode := (encode : (Fin k → F) → (ι → F))) stmt f γ
      (fun j ↦ wit 0 j + γ * wit 1 j) xs := by
  -- ABF26 C6.2 honest-completeness; bookkeeping proof, deferred.
  -- Linear-constraint side uses `Finset.sum_add_distrib + Finset.mul_sum`
  -- on the combined message `wit 0 + γ • wit 1`; spot-check side uses
  -- linearity of `encode`.
  sorry

end Verifier

section Soundness

/-- **Lemma 6.6 of [ABF26]** (knowledge soundness of Construction 6.2).

For any `δ ∈ (0, δ_min(C))`, the toy-problem IOR `T[C, t]` has knowledge
soundness with respect to the relaxed relation `R̃_{C,δ}^2` and error

    `max { ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|, (1 - δ)^t }`.

The proof exhibits an extractor that (i) erasure-decodes `(f₁, f₂)`
against the largest agreement set `S`, (ii) outputs the recovered
messages, and (iii) bounds the failure event by the union of the MCA
failure and the list-decoding cardinality bound (cf. **Remark 6.7**).

The formal statement is stubbed until `Protocol.lean` lands the prover
and the OracleReduction object proper. Tagged sorry. -/
theorem protocol62_knowledgeSound :
    -- Placeholder: real statement is "the OracleReduction object built
    -- from `accepts` has `rbrKnowledgeSoundness` with error as above".
    True := by
  -- ABF26-L6.6; in-paper proof, deferred until the protocol's
  -- OracleReduction object is wired (needs honest prover, then
  -- Verifier.knowledgeSoundness invocation).
  sorry

/-- **Remark 6.7 of [ABF26]**: the soundness argument for Lemma 6.6
relies on **mutual** correlated agreement (MCA), not merely correlated
agreement (CA). With CA, one could not prove that every codeword
`u ∈ Λ(C, f₁ + γ·f₂, δ)` decomposes as `u = u₁ + γ·u₂` for some
`(u₁, u₂) ∈ Λ(C^{≡2}, (f₁, f₂), δ)`, and the extractor would fail. MCA
gives exactly this decomposition with probability `≥ 1 − ε_mca`. This
remark is encoded in the L6.6 docstring above; no standalone lemma. -/
def remark67 : Unit := ()

/-- **Lemma 6.8 of [ABF26]** (round-by-round knowledge soundness of
Construction 6.2).

For any `δ ∈ (0, δ_min(C))`, the toy-problem IOR `T[C, t]` has
round-by-round knowledge soundness (in the sense of ArkLib's
`Verifier.rbrKnowledgeSoundness`, which matches paper Definition A.5)
with respect to `R̃_{C,δ}^2`, total extraction time
`O(enc_C + ecor_C)`, and per-round errors

  * `ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|` for the combination-randomness round,
  * `(1 - δ)^t` for the spot-check round.

The state function tracks, at each round, the largest agreement set
between `(f₁, f₂)` and a codeword-pair witness; the extractor erasure-
decodes against that set. Tagged sorry pending Protocol.lean wiring. -/
theorem protocol62_rbrKnowledgeSound :
    True := by
  -- ABF26-L6.8; awaits protocol object + KnowledgeStateFunction wiring.
  sorry

end Soundness

end ToyProblem.Protocol
