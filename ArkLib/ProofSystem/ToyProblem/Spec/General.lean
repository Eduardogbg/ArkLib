/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.ToyProblem.Definitions
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.ToVCVio.SimulateQ

/-!
# Toy problem oracle reduction (ABF26 Construction 6.2)

We describe the ABF26 §6 toy-problem IOR as an `OracleReduction` over
ArkLib's `OracleReduction` framework, following the conventions used by
`ArkLib/ProofSystem/Fri/Spec/SingleRound.lean` and
`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean`:

* `Statement`, `OracleStatement`, `Witness`, `OutputStatement` — input /
  oracle / witness / output type aliases (all `@[reducible]`).
* `pSpec` — the 3-round `ProtocolSpec` (`V → P` γ, `P → V` g, `V → P`
  spot-checks).
* `OracleInterface`, `Inhabited`, `Fintype` instances for the messages
  and challenges of `pSpec`.
* `inputRelationFor` / `outputRelationFor` — IOR input/output relations
  (Definitions 6.1 and 6.3, in IOR shape, pinned to the verifier's fixed
  encoder).
* `accepts` — the §6.1 decision predicate (extracted for use by the
  verifier and by completeness proofs).

The `prover` / `verifier` / `oracleReduction` triple is complete. The
soundness lemmas `protocol62_knowledgeSound` (L6.6) and
`protocol62_rbrKnowledgeSound` (L6.8) carry the **concrete** paper error
terms (`max (ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|) ((1-δ)^t)` and the
per-round split); only their *proofs* are admitted as tagged-sorries,
pending careful threading of the `OptionT (OracleComp …)` extractor
machinery. The IOR scaffolding is exactly what is needed downstream.

## Protocol description

The verifier holds an explicit input `(v, μ₁, μ₂)` and has oracle
access to two purported codewords `f₁, f₂ : ι → F`. The protocol runs:

  1. **Combination randomness** (V → P): the verifier sends `γ ←$ F`.
  2. **Prover claim** (P → V): the prover sends `g : Fin k → F`. In the
     honest case `g = M₁ + γ · M₂` is the combination of the underlying
     messages.
  3. **Spot-check randomness** (V → P): the verifier sends
     `x₁, …, xₜ ←$ ι`.

The verifier accepts iff `⟨g, v⟩ = μ₁ + γ · μ₂` (linear-constraint
check) and for every `j ∈ Fin t`, `encode(g)(xⱼ) = f₁(xⱼ) + γ · f₂(xⱼ)`
(spot-check).

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6).
-/

namespace ToyProblem

namespace Spec

open OracleSpec OracleComp ProtocolSpec
open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal

/-! ### Type-level definitions and relations

The relations need `[Fintype ι]` (for `relaxedRelationFor`'s
`Fintype.card ι` call) and `[Field F]` (for the `→ₗ[F]` encoder). The
heavier `[DecidableEq ι] [Fintype F] [DecidableEq F]` instances come
in below for the protocol-object definitions. -/

variable {ι F : Type} [Fintype ι] [Field F]
variable (k t : ℕ)

/-- Input (explicit) statement of Construction 6.2: the linear-constraint
vector `v ∈ F^k` and the two constraint values `(μ₁, μ₂) ∈ F²`. -/
@[reducible]
def Statement : Type := (Fin k → F) × F × F

/-- Oracle statements of Construction 6.2: the two purported codewords
`f₁, f₂ : ι → F`. The verifier only queries them at the spot-check
positions. -/
@[reducible]
def OracleStatement (ι F : Type) : Fin 2 → Type := fun _ ↦ ι → F

instance : ∀ i, OracleInterface (OracleStatement ι F i) :=
  fun _ ↦ inferInstance

/-- Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose
encodings are the oracle codewords `f₁, f₂`. -/
@[reducible]
def Witness : Type := Fin 2 → Fin k → F

/-- Output statement: the IOR is a yes/no test — accept (return `()`) or
short-circuit to `none` via `OptionT`. -/
@[reducible]
def OutputStatement : Type := Unit

/-- Output oracle statement: the IOR has no output oracle component. -/
@[reducible]
def OutputOracleStatement : (Fin 0) → Type := nofun

/-- Output witness: empty. -/
@[reducible]
def OutputWitness : Type := Unit

/-- Protocol specification for Construction 6.2: three rounds, in the
order

    V → P  (γ : F)            -- combination randomness
    P → V  (g : Fin k → F)    -- combined message claim
    V → P  (xs : Fin t → ι)   -- spot-check positions.

Marked `@[reducible]` so per-round type access `pSpec.Type i` reduces
in client code (cf. FRI / Sumcheck single-round specs). -/
@[reducible]
def pSpec : ProtocolSpec 3 :=
  ⟨!v[.V_to_P, .P_to_V, .V_to_P],
   !v[F, Fin k → F, Fin t → ι]⟩

instance : ∀ j, OracleInterface ((pSpec (ι := ι) (F := F) k t).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => OracleInterface.instDefault
  | ⟨2, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec (ι := ι) (F := F) k t).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/-- The challenges of the toy-problem `pSpec` are `SampleableType` when
the underlying field `F` and the codeword index `ι` are. This is needed
to instantiate the (round-by-round) knowledge-soundness games, which
sample challenges from the protocol's challenge spaces. -/
instance [SampleableType F] [SampleableType ι] :
    ∀ j, SampleableType ((pSpec (ι := ι) (F := F) k t).Challenge j)
  | ⟨0, _⟩ => (inferInstance : SampleableType F)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => (inferInstance : SampleableType (Fin t → ι))

/-- The §6.1 decision predicate, factored out so completeness proofs and
the verifier object share the same statement.

Given the explicit input `(v, μ₁, μ₂)`, the oracle codewords
`(f 0, f 1)`, the challenge `γ`, the prover's claim `g`, the spot-check
positions `xs`, and an encoding function `encode`, the verifier accepts
iff:

  * `⟨g, v⟩ = μ₁ + γ · μ₂` (linear constraint), and
  * `∀ j, encode(g)(xs j) = f 0 (xs j) + γ · f 1 (xs j)` (per-spot-check).
-/
def accepts (encode : (Fin k → F) → (ι → F))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι F i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) : Prop :=
  (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2) ∧
  ∀ j : Fin t, encode g (xs j) = f 0 (xs j) + γ * f 1 (xs j)

/-- The IOR-shaped **fixed-encoding** input relation (Definition 6.1).

`((v, μ₁, μ₂), (f₀, f₁)) ∈ inputRelationFor encode` with witness `M`
iff the oracle codewords are the `encode`-images of the witness messages
(`fᵢ = encode (M i)`) and the witness satisfies the linear constraint
(`⟨M i, v⟩ = μᵢ`). The encoding is the verifier's **fixed** `encode` (a plain
function, matching `oracleVerifier`), and the witness `M` is tied to the
statement — this is what the honest prover sends `g = M₀ + γ·M₁` against and
what `accepts_of_inputRelation` consumes.

This replaces the earlier existential-encoding form (`ToyProblem.relation`,
`∃ encode'`), under which honest completeness is unprovable / false: the honest
prover's `encode g` need not match `fᵢ = encode' (Mᵢ)` when `encode' ≠ encode`
(the same defect found for the L6.12 attack — see `ToyProblem.relationFor`). -/
def inputRelationFor (encode : (Fin k → F) → (ι → F)) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι F i)) ×
      Witness (F := F) k) :=
  fun input ↦
    (∀ i : Fin 2, input.1.2 i = encode (input.2 i)) ∧
    (∀ i : Fin 2, ∑ j, input.2 i j * input.1.1.1 j = ![input.1.1.2.1, input.1.1.2.2] i)

/-- The IOR-shaped **fixed-encoding** *relaxed* output relation (Definition 6.3).
The soundness statement of L6.6/6.8 is with respect to this: the verifier's
"accept" guarantee is that the input `(f₀, f₁)` is `δ`-close (on a common
agreement column set) to a valid instance `encode (M i)` for some constraint-
satisfying messages `M`. Uses the verifier's fixed plain `encode` (cf.
`ToyProblem.relaxedRelationFor`), and checks the witness component supplied by
the ArkLib knowledge extractor; this is a witness-bearing relation, not merely
language membership. -/
def outputRelationFor (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι F i)) ×
      Witness (F := F) k) :=
  fun input ↦
    (∀ i : Fin 2, ∑ j, input.2 i j * input.1.1.1 j =
      ![input.1.1.2.1, input.1.1.2.2] i) ∧
    ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
      ∀ i : Fin 2, ∀ j ∈ S, input.1.2 i j = encode (input.2 i) j

-- The 1-arity relaxed relation `R̃¹_{C,δ}` lives in
-- `Spec/SimplifiedIOR.lean :: outputRelationFor` (the C6.9 output relation).
-- We expose it from the simplified-IOR file rather than here so its
-- type signature aligns with `SimplifiedIOR.OutputStatement` /
-- `OutputOracleStatement` / `OutputWitness` rather than re-bundling.

/-! ### Honest prover, verifier, and reduction

This section mirrors the `foldProver` / `foldVerifier` / `foldOracleReduction`
pattern in [`Fri/Spec/SingleRound.lean`](../../../Fri/Spec/SingleRound.lean).
Because `OracleStatement ι F i = ι → F` is a plain function (not an
oracle that needs the `OracleQuery` machinery), we use the **non-oracle**
`Prover` / `Verifier` / `Reduction` triple with the oracle codewords
threaded through the bundled input `StmtIn = Statement × (∀ i, OracleStatement i)`.
This is sound — it's the same shape produced by
`OracleReduction.toReduction` — and avoids the `embed` / `hEq`
plumbing. An `OracleProver` / `OracleVerifier` flavour is a follow-up.
-/

section Protocol
variable [DecidableEq ι] [Fintype F] [DecidableEq F]

/-- Honest prover for Construction 6.2. After receiving the combination
randomness `γ`, the prover sends `g := M 0 + γ · M 1` (point-wise on
`Fin k`). The spot-check positions `xs` are not used by the prover —
they only feed the verifier's spot-check at the end.

State machine (`PrvState : Fin 4 → Type`):
  * `PrvState 0` — initial: the bundled `(stmt, oStmt) × witness`.
  * `PrvState 1, 2, 3` — same plus the combination randomness `γ`. -/
def prover :
    Prover []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) (Witness (F := F) k)
      OutputStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  PrvState
  | ⟨0, _⟩ =>
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k
  | _ =>
      F × (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st ↦ pure <| fun (γ : F) ↦ (γ, st)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun ⟨γ, st⟩ ↦ pure <| fun (_ : Fin t → ι) ↦ (γ, st)

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨γ, ⟨stmt, oStmt⟩, M⟩ ↦
      pure ((fun j ↦ M 0 j + γ * M 1 j), (γ, ⟨stmt, oStmt⟩, M))
  | ⟨2, h⟩ => nomatch h

  output := fun _ ↦ pure ((), ())

/-- The §6.1 decision predicate is decidable: it's a finite conjunction
of equalities in `F` (decidable via `DecidableEq F`) and a `Fin t`
universally-quantified equality (decidable via the `Fintype` `Decidable`
instance). Marking explicitly so the `verifier` below can stay
computable (cf. FRI's `foldVerifier`, which is plain `def`). -/
instance accepts.instDecidable
    (encode : (Fin k → F) → (ι → F))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι F i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) :
    Decidable (accepts (k := k) (t := t) encode stmt f γ g xs) := by
  unfold accepts; infer_instance

/-- Honest verifier for Construction 6.2. Takes the bundled input
`(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂))` and the full transcript
`(γ, g, xs)`; accepts iff `accepts` holds for the supplied encoding.

Computable — `accepts` is decidable, so no `Classical.dec` is needed.
This mirrors FRI's `foldVerifier`, which is also a plain `def`. -/
def verifier (encode : (Fin k → F) → (ι → F)) :
    Verifier []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i))
      OutputStatement
      (pSpec (ι := ι) (F := F) k t) where
  verify := fun ⟨stmt, oStmt⟩ tr ↦ do
    let γ : F := tr ⟨0, by decide⟩
    let g : Fin k → F := tr ⟨1, by decide⟩
    let xs : Fin t → ι := tr ⟨2, by decide⟩
    if accepts (k := k) (t := t) encode stmt oStmt γ g xs
    then pure () else failure

/-- Honest reduction for Construction 6.2: the package
`{prover, verifier}` over the bundled-input `Reduction` type. -/
def reduction (encode : (Fin k → F) → (ι → F)) :
    Reduction []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) (Witness (F := F) k)
      OutputStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  prover := prover (ι := ι) (F := F) (k := k) (t := t)
  verifier := verifier (k := k) (t := t) encode

/-! ### Oracle-flavour prover, verifier, reduction

These are the `OracleProver` / `OracleVerifier` / `OracleReduction`
flavours of the same protocol, exposing `(f₁, f₂)` as oracle inputs
rather than bundling them into `StmtIn`. They match FRI/Sumcheck's
exact idiom and are necessary to make the *query complexity* of the
verifier explicit (`2t + 1` queries per execution: one for `g`, two
per spot-check).

The honest-completeness, knowledge-soundness, and round-by-round
knowledge-soundness lemmas below are stated against this oracle-flavour
reduction, since that's the form ArkLib's
`Verifier.knowledgeSoundness` / `Verifier.rbrKnowledgeSoundness`
machinery is designed for.
-/

/-- Same as `prover` but exposed at the `OracleProver` signature. The
underlying `Prover` is identical (after the `OracleProver` type-alias
unfolds to a `Prover` on bundled in/out types). The output is the
trivial `(((), nofun), ())` since the IOR has no output oracle
statements (`OutputOracleStatement : Fin 0 → Type`). -/
def oracleProver :
    OracleProver []ₒ
      (Statement (F := F) k) (OracleStatement ι F) (Witness (F := F) k)
      OutputStatement OutputOracleStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  PrvState
  | ⟨0, _⟩ =>
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k
  | _ =>
      F × (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st ↦ pure <| fun (γ : F) ↦ (γ, st)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun ⟨γ, st⟩ ↦ pure <| fun (_ : Fin t → ι) ↦ (γ, st)

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨γ, ⟨stmt, oStmt⟩, M⟩ ↦
      pure ((fun j ↦ M 0 j + γ * M 1 j), (γ, ⟨stmt, oStmt⟩, M))
  | ⟨2, h⟩ => nomatch h

  output := fun _ ↦ pure (((), nofun), ())

/-- Query helper: fetch the prover's combined-message claim `g`
(`pSpec` round 1 — the `P → V` direction). Mirrors FRI's `getConst`. -/
def queryG : OracleComp [(pSpec (ι := ι) (F := F) k t).Message]ₒ (Fin k → F) :=
  liftM <| OracleSpec.query
    (show [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain from
      ⟨⟨1, by rfl⟩, (by simpa using ())⟩)

/-- Query helper: read codeword `f i` at position `x : ι`. Mirrors
FRI's `queryCodeword`. -/
def queryF (i : Fin 2) (x : ι) : OracleComp [OracleStatement ι F]ₒ F :=
  liftM <| OracleSpec.query
    (show [OracleStatement ι F]ₒ.Domain from ⟨i, (by simpa using x)⟩)

/-- Oracle verifier for Construction 6.2.

Queries the prover's message `g` once and the two oracle codewords
`f₁, f₂` at each of the `t` spot-check positions (query complexity:
`2t + 1`), then `guard (accepts …)` to decide.

`embed` and `hEq` are trivial — `OutputOracleStatement : Fin 0 → Type`
is empty, so the output-oracle family is vacuously a subset of input
oracles + prover messages. -/
def oracleVerifier (encode : (Fin k → F) → (ι → F)) :
    OracleVerifier []ₒ
      (Statement (F := F) k) (OracleStatement ι F)
      OutputStatement OutputOracleStatement
      (pSpec (ι := ι) (F := F) k t) where
  verify := fun stmt challenges ↦ do
    let γ : F := challenges ⟨⟨0, by decide⟩, by rfl⟩
    let xs : Fin t → ι := challenges ⟨⟨2, by decide⟩, by rfl⟩
    let g : Fin k → F ← liftM <| queryG (ι := ι) (F := F) (k := k) (t := t)
    guard (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2)
    for j in (List.finRange t) do
      let f₀ : F ← liftM <| queryF (ι := ι) (F := F) 0 (xs j)
      let f₁ : F ← liftM <| queryF (ι := ι) (F := F) 1 (xs j)
      guard (encode g (xs j) = f₀ + γ * f₁)
    pure ()
  embed := ⟨fun i ↦ i.elim0, fun a _ _ ↦ a.elim0⟩
  hEq := fun i ↦ i.elim0

/-- Honest oracle reduction for Construction 6.2: the
`OracleProver` / `OracleVerifier` pair packaged as `OracleReduction`. -/
def oracleReduction (encode : (Fin k → F) → (ι → F)) :
    OracleReduction []ₒ
      (Statement (F := F) k) (OracleStatement ι F) (Witness (F := F) k)
      OutputStatement OutputOracleStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  prover := oracleProver (ι := ι) (F := F) (k := k) (t := t)
  verifier := oracleVerifier (k := k) (t := t) encode

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Honest completeness for ABF26 Construction 6.2, point form: if
`((v, μ₁, μ₂), (f₁, f₂))` lies in `inputRelation` with the underlying
messages `M = (M₀, M₁)` (and `fᵢ` is the `encode`-image of `Mᵢ`), then
for any verifier challenges `(γ, xs)` the §6.1 decision `accepts` holds
against the honest prover's message `g = M₀ + γ · M₁`.

This is the point-form companion to the
`OracleReduction.perfectCompleteness` theorem that wraps the prover and
verifier objects below. -/
theorem accepts_of_inputRelation {k t : ℕ}
    {encode : (Fin k → F) →ₗ[F] (ι → F)}
    (stmt : Statement (F := F) k)
    (M : Witness (F := F) k)
    (hM : ∀ i, ∑ j, M i j * stmt.1 j =
        (if i = (0 : Fin 2) then stmt.2.1 else stmt.2.2))
    (f : ∀ i, OracleStatement ι F i)
    (hf : ∀ i, f i = encode (M i))
    (γ : F) (xs : Fin t → ι) :
    accepts (k := k) (t := t) (encode := (encode : (Fin k → F) → (ι → F)))
      stmt f γ (fun j ↦ M 0 j + γ * M 1 j) xs := by
  refine ⟨?_, ?_⟩
  · -- Linear-constraint: ∑ j, (M 0 j + γ * M 1 j) * v j = μ₁ + γ * μ₂.
    have h0 : ∑ j, M 0 j * stmt.1 j = stmt.2.1 := by
      have := hM 0; simpa using this
    have h1 : ∑ j, M 1 j * stmt.1 j = stmt.2.2 := by
      have := hM 1
      have hne : (1 : Fin 2) ≠ 0 := by decide
      simpa [if_neg hne] using this
    calc ∑ j, (M 0 j + γ * M 1 j) * stmt.1 j
        = ∑ j, (M 0 j * stmt.1 j + γ * (M 1 j * stmt.1 j)) := by
          apply Finset.sum_congr rfl; intros j _; ring
      _ = (∑ j, M 0 j * stmt.1 j) + ∑ j, γ * (M 1 j * stmt.1 j) :=
          Finset.sum_add_distrib
      _ = (∑ j, M 0 j * stmt.1 j) + γ * ∑ j, M 1 j * stmt.1 j := by
          rw [← Finset.mul_sum]
      _ = stmt.2.1 + γ * stmt.2.2 := by rw [h0, h1]
  · -- Spot-check: encode(g) x = f 0 x + γ * f 1 x.
    intro j
    have hg_eq : (fun i ↦ M 0 i + γ * M 1 i) = M 0 + γ • M 1 := by
      funext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hg_eq, map_add, map_smul, hf 0, hf 1]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- **Honest completeness for Construction 6.2** (protocol-level form).

The honest oracle reduction is perfectly complete from `inputRelationFor encode`
to the trivial output relation `Set.univ`. The load-bearing fact is
`accepts_of_inputRelation` above: under any verifier challenges, the
honest prover's message `g = M₀ + γ M₁` makes `accepts` hold, so the
verifier's `if accepts then pure () else failure` never fails.

**Status: statement complete and faithful, proof structurally unfolded with one
documented residual `sorry` (the probabilistic/monadic support bookkeeping).**
The point-form mathematical content (`accepts_of_inputRelation`) is fully
closed. The proof below unfolds `OracleReduction.perfectCompleteness` through
`toReduction`, expands the prover's three-round `runToRound` via
`Fin.induction_three`, and resolves all three round directions.

The two original framework blockers are now both addressed at the lemma level:

  1. **`simulateQ_forIn`.** Closed by `simulateQ_list_forIn`
     (`ArkLib/ToVCVio/SimulateQ.lean`), which commutes `simulateQ` past the
     verifier's spot-check `forIn (List.finRange t) …`.
  2. **A `simulateQ`/`SubSpec` query-resolution simp set.** Closed by
     `simulateQ_addLift_add_liftM_left` / `_right`
     (`ArkLib/ToVCVio/SimulateQ.lean`): these route the `queryG`/`queryF`
     double-`liftM`'d queries through the `simOracle2` layer to the correct
     inner oracle in one rewrite, so the verifier body resolves to a query-free
     `guard`/`forIn` computation.

**Statement faithfulness (fixed 2026-06-04).** The input relation is the
**fixed-encoding** `inputRelationFor encode` (the verifier's own `encode`, with
the witness `M` tied to the codewords `fᵢ = encode (M i)`). An earlier
existential-encoding form (`ToyProblem.relation`, `∃ encode'`) made completeness
*unprovable / false* — the honest prover's `encode g` need not match
`fᵢ = encode' (Mᵢ)` when `encode' ≠ encode` (the same defect found for the L6.12
attack). With `inputRelationFor encode` the discharge to `accepts_of_inputRelation`
(`hf : fᵢ = encode (M i)`, `hM : ⟨M i, v⟩ = μᵢ`) goes through.

**Precise residual.** After the unfolding, the goal is
`probEvent (OptionT.mk do let s ← init; (simulateQ pImpl (…)).run' s) … = 1`,
with the `simulateQ`/`forIn`/query binds *underneath* the `OptionT.mk` /
`probEvent` / `StateT.run'` layers. Closing it requires the support-membership
argument of `Sumcheck/Spec/SingleRound.lean :: reduction_perfectCompleteness`
(`one_le_probEvent_iff` → `probEvent_eq_one_iff` → `OptionT.run_mk` →
`StateT.run'_eq` → iterated `support_bind` + `simulateQ_bind` peeling), adapted
from that (loopless, two-round, *itself still admitted*) proof to this
three-round protocol *with* the spot-check loop — a sizeable mechanical peel
(~250+ lines) discharging to `accepts_of_inputRelation`. -/
theorem oracleReduction_perfectCompleteness
    [SampleableType F] [SampleableType ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (encode : (Fin k → F) →ₗ[F] (ι → F)) :
    (oracleReduction (ι := ι) (F := F) (k := k) (t := t)
        (encode : (Fin k → F) → (ι → F))).perfectCompleteness
      init impl
      (inputRelationFor (encode := (encode : (Fin k → F) → (ι → F))))
      (Set.univ : Set (((OutputStatement × ∀ i, OutputOracleStatement i)) ×
        OutputWitness)) := by
  unfold OracleReduction.perfectCompleteness
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro stmtIn witIn hRel
  -- Unfold the reduction run, expand the 3-round prover (`Fin.induction_three`),
  -- and inline the oracle verifier's `toVerifier` wrapper.
  simp only [OracleReduction.toReduction, Reduction.run, oracleReduction,
    oracleProver, OracleVerifier.toVerifier, oracleVerifier,
    Prover.run, Prover.runToRound, Fin.induction_three, Prover.processRound,
    Verifier.run, pSpec, bind_pure_comp]
  -- Resolve round 0 direction (`V_to_P`, the combination randomness `γ`).
  split <;> rename_i hDir0
  swap
  · exact absurd hDir0 (by decide)
  try simp only [pure_bind, map_pure, Functor.map_map, Function.comp, bind_pure_comp]
  -- Resolve round 1 direction (`P_to_V`, the prover's claim `g`).
  split <;> rename_i hDir1
  · exact absurd hDir1 (by decide)
  try simp only [pure_bind, map_pure, Functor.map_map, Function.comp, bind_pure_comp]
  -- Resolve round 2 direction (`V_to_P`, the spot-check positions `xs`).
  split <;> rename_i hDir2
  swap
  · exact absurd hDir2 (by decide)
  -- ABF26-C6.2; framework-residual. The prover/verifier are unfolded (above) and
  -- the query-resolution lemmas are landed (`simulateQ_list_forIn`,
  -- `simulateQ_addLift_add_liftM_*`); the statement is now the faithful
  -- fixed-encoding `inputRelationFor encode`. The only remaining gap is the
  -- ~250-line `OptionT`/`StateT`/`simulateQ` support-peel discharging to
  -- `accepts_of_inputRelation` — see the theorem docstring's "Precise residual".
  sorry

omit [DecidableEq ι] in
/-- **Lemma 6.6 of [ABF26]** (knowledge soundness of Construction 6.2).

For any `δ ∈ (0, δ_min(C))` and fixed linear encoder with range `C`,
the toy-problem IOR has knowledge soundness against the relaxed relation
`R̃_{C,δ}^2` with error

  `max { ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|, (1 − δ)^t }`.

Stated against ArkLib's `Verifier.knowledgeSoundness` (cf.
`OracleReduction/Security/Basic.lean :: Verifier.knowledgeSoundness`).

**Naming convention — paper vs API.** The ArkLib API's
`Verifier.knowledgeSoundness` takes `(relIn, relOut)` where `relIn`
is the relation the extracted witness satisfies and `relOut` is the
relation the verifier's output must satisfy. In this file `relIn` is
*our* `outputRelationFor` (paper's `R̃²_{C,δ}`, checked against the
messages returned by the extractor) and `relOut` is `Set.univ` (paper's
C6.2 has trivial output `Unit`). The name `outputRelationFor` reflects
the **paper's** "this is the protocol's output relation" perspective; do
not be misled by the API parameter named `relIn`.

The proof exhibits an extractor that (i) erasure-decodes `(f₁, f₂)`
against the largest agreement set, (ii) outputs the recovered messages,
and (iii) bounds the failure event by the union of the MCA failure and
the list-decoding cardinality bound (cf. Remark 6.7).

Tagged sorry. -/
theorem protocol62_knowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → F)) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → F))
    (_hC : Set.range encode = C)
    (_hδ_pos : 0 < δ)
    (_hδ_lt_min : δ < (minRelHammingDistCode C : ℝ≥0)) :
      (verifier (k := k) (t := t) (encode : (Fin k → F) → (ι → F))).knowledgeSoundness
        (WitOut := OutputWitness)
        init impl (outputRelationFor k (encode : (Fin k → F) → (ι → F)) δ)
        (Set.univ : Set (OutputStatement × OutputWitness))
        (max ((epsMCA (F := F) (A := F) C δ).toNNReal +
                ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
                  / (Fintype.card F : ℝ≥0))
             ((1 - δ) ^ t)) := by
  -- ABF26-L6.6; paper-proof-owed [ABF26 Lemma 6.6, §6.2]. This is the paper's
  -- OWN result (it proves it in full in §6.2), not an imported external result;
  -- we owe a Lean proof. The knowledge error is the concrete paper bound
  -- `max (ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|) ((1-δ)^t)`. The `δ < δ_min(C)`
  -- hypothesis is load-bearing: the proof uses it to force `g = f₁ + γ·f₂`
  -- from agreement on `> (1 - δ_min)·n` points (see paper eq. (3)).
  sorry

/-- **Remark 6.7 of [ABF26]**: the L6.6 soundness argument depends on
**mutual** correlated agreement (MCA). With only correlated agreement
(CA), one cannot prove every codeword `u ∈ Λ(C, f₁ + γ·f₂, δ)`
decomposes as `u = u₁ + γ·u₂` for some
`(u₁, u₂) ∈ Λ(C^{≡2}, (f₁, f₂), δ)`, so the extractor would fail. MCA
provides exactly this decomposition with probability `≥ 1 − ε_mca`. -/
def remark67 : Unit := ()

omit [DecidableEq ι] in
/-- **Lemma 6.8 of [ABF26]** (round-by-round knowledge soundness of
Construction 6.2).

For any `δ ∈ (0, δ_min(C))` and fixed linear encoder with range `C`,
the IOR has round-by-round knowledge soundness (paper Definition A.5 ≡
ArkLib's `Verifier.rbrKnowledgeSoundness`) against `R̃_{C,δ}^2`, with
per-round errors

  * `ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|` after the γ round,
  * `(1 − δ)^t` after the spot-check round.

The `KnowledgeStateFunction` tracks the largest current agreement set;
the extractor erasure-decodes against it. Tagged sorry. -/
theorem protocol62_rbrKnowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → F)) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → F))
    (_hC : Set.range encode = C)
    (_hδ_pos : 0 < δ)
    (_hδ_lt_min : δ < (minRelHammingDistCode C : ℝ≥0)) :
      (verifier (k := k) (t := t) (encode : (Fin k → F) → (ι → F))).rbrKnowledgeSoundness
        (WitOut := OutputWitness)
        init impl (outputRelationFor k (encode : (Fin k → F) → (ι → F)) δ)
        (Set.univ : Set (OutputStatement × OutputWitness))
        (fun i ↦
          -- round 0 (combination randomness γ): MCA + list-decoding term;
          -- round 2 (spot checks): `(1-δ)^t`.
          if i.1 = 0 then
            (epsMCA (F := F) (A := F) C δ).toNNReal +
              ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
                / (Fintype.card F : ℝ≥0)
          else (1 - δ) ^ t) := by
  -- ABF26-L6.8; paper-proof-owed [ABF26 Lemma 6.8, §6.2]. Paper's OWN result
  -- (proved in full via a KnowledgeStateFunction in §6.2), not an external
  -- import. `δ < δ_min(C)` is load-bearing (same forcing step as L6.6).
  sorry

end Protocol

end Spec

end ToyProblem
