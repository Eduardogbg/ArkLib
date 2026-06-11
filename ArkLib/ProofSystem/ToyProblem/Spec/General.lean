/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.ToyProblem.Definitions
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ

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

## Paper ↔ framework mapping

How each step of Construction 6.2 lands on an ArkLib / VCV-io primitive:

* `γ ←$ F` (combination randomness) ↦ `pSpec` round 0 (`.V_to_P`); the
  security games sample it via the `SampleableType F` instance on the
  challenge type.
* prover claim `ḡ ∈ F^k` ↦ `pSpec` round 1 (`.P_to_V`), with
  `OracleInterface.instDefault` as its message-oracle interface.
* spot-check positions `x₁, …, xₜ` ↦ `pSpec` round 2 (`.V_to_P`), of
  type `Fin t → ι`.
* oracle access to `f₁, f₂` ↦ `OracleStatement` queried via `queryF`,
  routed through the per-index `OracleInterface` instances.
* the §6.1 decision predicate ↦ `accepts`.
* verifier query routing ↦ `OracleInterface.simOracle2` / `simulateQ`
  (VCV-io's query-simulation semantics).
* completeness game ↦ `OracleReduction.perfectCompleteness`.
* knowledge-soundness games (paper App A.1, Defs A.2 / A.4 / A.5) ↦
  `OracleVerifier.knowledgeSoundness` / `OracleVerifier.rbrKnowledgeSoundness`.
  Two caveats: extraction **time** (the paper's `O(enc + ecor)` extractor
  cost) is outside ArkLib's cost-free model, and the verifier's query
  complexity (`2t + 1`) is documented, not enforced
  (`OracleVerifier.numQueries` is upstream-sorried).

## Alphabet restriction (`s = 1`)

The paper's Construction 6.1/6.2 inputs are `f : [n] → F^s` for a folding
parameter `s` (and the §6.3 tables sweep `s = 2^0, …, 2^12`). This
formalization fixes `s = 1`: words are `ι → F`, not `ι → F^s`. This is a
genuine scope restriction, not mere notational choice — reindexing
`ι := [n] × [s]` does **not** recover the general case, because the
relative Hamming metric over the alphabet `F^s` (one symbol = one
`F^s`-coordinate) differs from the metric over `F` on the flattened
index set. The §6.3 `s`-sweep therefore needs the `F^s` generalization,
planned for Phase-5 `Impl/FRS`. The `s = 2^0` rows of the paper's tables
fall squarely inside the current form, so the `s = 1` formalization is
non-vacuous for the prize regime.

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
plumbing. The `OracleProver` / `OracleVerifier` flavour (the target of
the completeness and soundness statements) follows in the next section.
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
knowledge-soundness lemmas below are all stated against these
oracle-flavour objects: completeness via
`OracleReduction.perfectCompleteness`, L6.6 via
`OracleVerifier.knowledgeSoundness`, and L6.8 via
`OracleVerifier.rbrKnowledgeSoundness`. The latter two are
definitionally `toVerifier.knowledgeSoundness` /
`toVerifier.rbrKnowledgeSoundness`, so the oracle-flavour statements
carry no extra proof burden over the bundled-input forms.

**Framework vacuity (KS) — RESOLVED 2026-06-11.** The historical trap —
`Verifier.knowledgeSoundness` admitted an always-failing `OptionT`
extractor that drove the bad-event probability to `0` — was fixed by
PR #569 (`fix/knowledge-soundness-failing-extractor`), now merged and
synced into this branch: extraction failure (`extractedWitIn? = none`)
is scored against the prover. The KS sorries below
(`protocol62_knowledgeSound`, and `simplifiedIOR_knowledgeSound` in
`Spec/SimplifiedIOR.lean`) may be closed on their mathematical merits.
`Verifier.rbrKnowledgeSoundness` was never affected, so
`protocol62_rbrKnowledgeSound` is provable as-is (and is the natural
first target; KS then follows via the rbrKS → KS implication).
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
/-- The honest oracle verifier's body, simulated through `simOracle2` against the prover's
messages `msgs` and the input codewords `oStmt`, resolves to `pure (some ())` whenever the two
accept conditions hold for the supplied challenge `γ`, spot-check positions `xs`, and prover
message `g = msgs ⟨1, rfl⟩`:

  * `hAcc1`: the linear-constraint check `∑ j, g j · v j = μ₁ + γ · μ₂`, and
  * `hAcc2`: the per-spot-check `encode g (xs j) = f₀(xs j) + γ · f₁(xs j)`.

This is the monadic core of `oracleReduction_perfectCompleteness`: the residual support obligation
after the `Pr[…] = 1` goal is reduced via `OptionT.probEvent_eq_one_of_simulateQ_support_bind`
forces every honest-run output to be `some` of an accepting output, which this lemma certifies by
resolving each query (the prover claim `g` and the `2t` codeword reads) against `simOracle2` and
discharging both guards. The query/loop routing uses the staged `simulateQ`/`OptionT` toolkit
(`OracleComp.monadLift_liftM_OptionT`, `simulateQ_optionT_bind`/`_lift`,
`simulateQ_optionT_forIn_yield_pure_some`); the `change`/`conv` steps bridge the definitional —
but not syntactic — equalities between the elaborated verifier's `MonadLift`/`ForIn` instance
trees and the toolkit lemmas' canonical spellings. -/
lemma verifierBody_simulateQ_eq_pure
    (encode : (Fin k → F) → (ι → F))
    (oStmt : (i : Fin 2) → OracleStatement ι F i)
    (msgs : (j : (pSpec (ι := ι) (F := F) k t).MessageIdx) →
      (pSpec (ι := ι) (F := F) k t).Message j)
    (stmt1 : Fin k → F) (mu1 mu2 : F) (γ : F) (xs : Fin t → ι)
    (hAcc1 : ∑ j, (msgs ⟨1, rfl⟩) j * stmt1 j = mu1 + γ * mu2)
    (hAcc2 : ∀ j : Fin t, encode (msgs ⟨1, rfl⟩) (xs j)
      = oStmt 0 (xs j) + γ * oStmt 1 (xs j)) :
    simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
      (do
        let g : Fin k → F ← liftM (queryG (ι := ι) (F := F) (k := k) (t := t))
        guard (∑ j, g j * stmt1 j = mu1 + γ * mu2)
        (fun _ ↦ ()) <$>
          forIn (List.finRange t) PUnit.unit fun j _ ↦ do
            let f₀ : F ← liftM (queryF (ι := ι) (F := F) 0 (xs j))
            let f₁ : F ← liftM (queryF (ι := ι) (F := F) 1 (xs j))
            (fun _ ↦ ForInStep.yield PUnit.unit) <$>
              guard (encode g (xs j) = f₀ + γ * f₁)
        : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) Unit)
      = pure (some ()) := by
  -- Bridge each OptionT-lifted query helper to `OptionT.lift` of its OracleComp lift.
  rw [show (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
      = OptionT.lift (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
          OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
        (OracleComp.monadLift_liftM_OptionT _).symm]
  simp only [show ∀ (i : Fin 2) (x : ι), (liftM (queryF (ι := ι) (F := F) i x) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) F)
      = OptionT.lift (liftM (queryF (ι := ι) (F := F) i x) :
          OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) F) from
        fun i x ↦ (OracleComp.monadLift_liftM_OptionT _).symm]
  -- Push `simulateQ` through the OptionT bind / lift / map structure.
  simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
    queryG, queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
  -- Resolve the `g`-query to its oracle answer `msgs ⟨1, rfl⟩` by defeq.
  conv_lhs =>
    enter [1, 1]
    change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
        QueryImpl.liftTarget (OracleComp []ₒ)
          ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
            (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
      (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
        [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
    rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
        QueryImpl.liftTarget (OracleComp []ₒ)
          ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
            (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
      (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
        [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
      = (pure (msgs ⟨1, rfl⟩) : OracleComp []ₒ (Fin k → F)) from rfl]
  rw [show (OptionT.lift (pure (msgs ⟨1, rfl⟩)) : OptionT (OracleComp []ₒ) (Fin k → F))
      = (pure (msgs ⟨1, rfl⟩) : OptionT (OracleComp []ₒ) (Fin k → F)) from rfl, pure_bind]
  -- Guard 1 passes (hAcc1): `guard True = pure ()`, then `simulateQ impl (pure …) = pure …`.
  rw [show (guard (∑ j, msgs ⟨1, rfl⟩ j * stmt1 j = mu1 + γ * mu2) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
      = pure PUnit.unit from by rw [hAcc1]; simp [guard]]
  conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
        ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
      = OptionT.lift (pure PUnit.unit) from rfl]
  rw [simulateQ_optionT_lift, simulateQ_pure]
  rw [show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
      = pure PUnit.unit from rfl, pure_bind]
  -- Resolve the spot-check `forIn` to `pure (some ())` via the yield-pure induction lemma.
  -- `hForIn`'s type is checked against the goal-shaped equation by `isDefEq` (bridging the
  -- lift-instance gaps); a `conv … change` then re-spells the goal's loop to `hForIn`'s LHS.
  have hForIn :
      simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
        ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
          (OptionT.lift (liftM (queryF (ι := ι) (F := F) 0 (xs j))) >>= fun f₀ ↦
            OptionT.lift (liftM (queryF (ι := ι) (F := F) 1 (xs j))) >>= fun f₁ ↦
              guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ * f₁) >>=
                pure ∘ fun _ ↦ ForInStep.yield PUnit.unit)
            : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
      = (pure (some PUnit.unit) : OracleComp (emptySpec.{0, 0}) (Option PUnit)) := by
    apply simulateQ_optionT_forIn_yield_pure_some
    intro j
    simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
      queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
    -- Resolve the two `queryF` reads (`f₀ = oStmt 0 (xs j)`, `f₁ = oStmt 1 (xs j)`) by defeq.
    conv_lhs =>
      enter [1, 1]
      change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
      rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
        = (pure (oStmt 0 (xs j)) : OracleComp []ₒ F) from rfl]
    rw [show (OptionT.lift (pure (oStmt 0 (xs j))) : OptionT (OracleComp []ₒ) F)
        = (pure (oStmt 0 (xs j)) : OptionT (OracleComp []ₒ) F) from rfl, pure_bind]
    conv_lhs =>
      enter [1, 1]
      change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
      rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
        = (pure (oStmt 1 (xs j)) : OracleComp []ₒ F) from rfl]
    rw [show (OptionT.lift (pure (oStmt 1 (xs j))) : OptionT (OracleComp []ₒ) F)
        = (pure (oStmt 1 (xs j)) : OptionT (OracleComp []ₒ) F) from rfl, pure_bind]
    -- Guard passes by hAcc2; then `simulateQ impl (pure …) = pure …`.
    rw [show (guard (encode (msgs ⟨1, rfl⟩) (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j)) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
        = pure PUnit.unit from by rw [hAcc2 j]; simp [guard]]
    conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
          ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
        = OptionT.lift (pure PUnit.unit) from rfl]
    rw [simulateQ_optionT_lift, simulateQ_pure,
      show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
        = pure PUnit.unit from rfl, pure_bind]
    -- Trailing `(pure ∘ yield) unit = pure (yield unit)`, simulated to `pure (some (yield unit))`.
    show simulateQ _ ((pure (ForInStep.yield PUnit.unit) : OptionT (OracleComp ([]ₒ +
        ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ)))
          (ForInStep PUnit)) : OracleComp _ (Option (ForInStep PUnit))) = _
    conv_lhs => rw [show (pure (ForInStep.yield PUnit.unit) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (ForInStep PUnit))
        = OptionT.lift (pure (ForInStep.yield PUnit.unit)) from rfl]
    rw [simulateQ_optionT_lift, simulateQ_pure]
    rfl
  -- Collapse the loop. The goal's bound `simulateQ … (forIn …)` is defeq to `hForIn`'s LHS but
  -- not `rw`-matchable (the `ForIn`/`MonadLift` instance trees differ syntactically). A
  -- `conv … change` re-spells the focused loop as `hForIn`'s exact LHS (the universes are pinned
  -- to `0` by the `emptySpec.{0,0}` ascription in the statement), after which `rw [hForIn]` fires.
  conv_lhs =>
    enter [1]
    change simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
        ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
          (OptionT.lift (liftM (queryF (ι := ι) (F := F) 0 (xs j))) >>= fun f₀ ↦
            OptionT.lift (liftM (queryF (ι := ι) (F := F) 1 (xs j))) >>= fun f₁ ↦
              guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ * f₁) >>=
                pure ∘ fun _ ↦ ForInStep.yield PUnit.unit)
            : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
  rw [hForIn]
  -- After collapsing the loop the goal is `(pure (some ()) : OracleComp []ₒ _) >>= …`; the bind
  -- runs the constant `(pure ∘ id)` continuation, leaving
  -- `simulateQ impl (pure ()) = pure (some ())`.
  show ((pure (some PUnit.unit) : OracleComp []ₒ (Option PUnit)) >>= fun _ ↦
      simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
        ((pure PUnit.unit : OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit) :
          OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Option PUnit))) = _
  rw [pure_bind]
  exact simulateQ_pure _ (some PUnit.unit)

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- **Honest completeness for Construction 6.2** (protocol-level form).

The honest oracle reduction is perfectly complete from `inputRelationFor encode`
to the trivial output relation `Set.univ`. The load-bearing fact is
`accepts_of_inputRelation` above: under any verifier challenges, the
honest prover's message `g = M₀ + γ M₁` makes `accepts` hold, so the
verifier's `if accepts then pure () else failure` never fails.

**Status: fully proven (sorry-free, axiom-clean: `propext`, `Classical.choice`,
`Quot.sound` only; closed 2026-06-11).** The proof unfolds
`OracleReduction.perfectCompleteness` through `toReduction`, expands the
prover's three-round `runToRound` via `Fin.induction_three`, resolves the three
round directions, and reduces the `Pr[…] = 1` goal to a support-membership
obligation via `OptionT.probEvent_eq_one_of_simulateQ_support_bind`
(`ArkLib/ToVCVio/OracleComp/SimSemantics/SimulateQ.lean`). The support
obligation splits into:

  1. **The monadic core** — resolving the verifier body's `queryG`/`queryF`
     against `simOracle2` through the composed `MonadLiftT`/`OptionT` instance
     chains and collapsing the spot-check `forIn` — packaged as
     `verifierBody_simulateQ_eq_pure` (above), built on the staged toolkit
     (`simulateQ_optionT_bind`/`_lift`, `simulateQ_optionT_forIn_yield_pure_some`,
     `OracleComp.monadLift_liftM_OptionT`); the query routing itself is done by
     manual definitional bridges, not by the staged `simulateQ_add_add_liftM_*`
     simp family (whose `implA + implB` left-hand sides do not match
     `simOracle2`'s `addLift`/`liftTarget` spelling — that family remains an
     upstream-candidate for canonically-spelled goals). The recurrent obstacle —
     elaborated `MonadLift`/`ForIn` instance trees that are *definitionally* but
     not *syntactically* equal to the toolkit lemmas' canonical spellings — is
     bridged by `conv … change`/`show … from rfl` steps and a universe-pinned
     `emptySpec.{0,0}` ascription (the `[]ₒ` notation otherwise leaves a free
     universe metavariable that blocks `rw`).
  2. **Support plumbing** — peeling the `Reduction.run` OptionT-bind chain
     (challenge sampling, `Transcript.concat` layers, final `Option.getM`) via
     the `obtain`-friendly defeq peelers (`OptionT.mem_support_run_bind`,
     `OracleComp.mem_support_bind_peel`, …, same staged file), landing each
     support element on `verifierBody_simulateQ_eq_pure` with the accept
     hypotheses supplied by `accepts_of_inputRelation` from `hRel`.

**Statement faithfulness (fixed 2026-06-04).** The input relation is the
**fixed-encoding** `inputRelationFor encode` (the verifier's own `encode`, with
the witness `M` tied to the codewords `fᵢ = encode (M i)`). An earlier
existential-encoding form (`ToyProblem.relation`, `∃ encode'`) made completeness
*unprovable / false* — the honest prover's `encode g` need not match
`fᵢ = encode' (Mᵢ)` when `encode' ≠ encode` (the same defect found for the L6.12
attack). With `inputRelationFor encode` the discharge to `accepts_of_inputRelation`
(`hf : fᵢ = encode (M i)`, `hM : ⟨M i, v⟩ = μᵢ`) goes through. -/
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
  -- Reduce `Pr[…] = 1` to a support-membership obligation on the (pre-simulation)
  -- `OracleComp` body via the toolkit lemma, which peels the `(← init)` bind, the
  -- `simulateQ`/`StateT.run'` layers, and the `OptionT.mk` failure bookkeeping.
  apply OptionT.probEvent_eq_one_of_simulateQ_support_bind
  intro x hx
  -- The output relation is trivial: `OutputStatement = OutputWitness = Unit`, so both
  -- conjuncts (`(a.2, a.1.2.2) ∈ Set.univ` and `a.1.2.1 = a.2`) hold for *every* `a`
  -- (`Subsingleton Unit`). It therefore suffices to show `x = some a` for some `a`.
  refine (fun ⟨a, ha⟩ ↦ ⟨a, ha, Set.mem_univ _, Subsingleton.elim _ _⟩) (?_ : ∃ a, x = some a)
  -- The monadic-simulation core (the historical C6.2 blocker — routing `queryG`/`queryF` through
  -- the composed `simOracle2` `MonadLift` chain and collapsing the `OptionT` spot-check `forIn`) is
  -- now **closed**, packaged as `verifierBody_simulateQ_eq_pure` (above) on top of the staged
  -- toolkit (`simulateQ_optionT_bind`/`_lift`, `simulateQ_optionT_forIn_yield_pure_some`,
  -- `OracleComp.monadLift_liftM_OptionT`). The defeq-vs-syntactic lift-instance gaps are bridged
  -- there by `conv … change` + universe-pinned `emptySpec.{0,0}` ascriptions.
  --
  -- The verifier body resolves to `pure (some ())` by `verifierBody_simulateQ_eq_pure` (above) —
  -- this is the load-bearing C6.2 content, now **fully proven**: for *any* sampled challenge `γ`
  -- and spot-check positions `xs`, the honest prover's round-1 message `g = M₀ + γ·M₁` makes both
  -- guards pass (`accepts_of_inputRelation`, supplied via `hRel : … ∈ inputRelationFor encode`),
  -- so the simulated verifier body never fails and yields `some ()`. Concretely, in `hx`'s run the
  -- verifier subterm is `simulateQ (simOracle2 []ₒ stmtIn.2 proverResult.1.messages) (do let g ←
  -- queryG; guard …; for … ; …).run`, which is exactly `verifierBody_simulateQ_eq_pure` at
  -- `oStmt := stmtIn.2`, `msgs := proverResult.1.messages`, `g := proverResult.1.messages ⟨1,rfl⟩`.
  --
  -- The remaining work (ABF26-C6.2, now **closed**) is generic support plumbing: decompose
  -- `support (Reduction.run …)` through the `Prover.run` challenge-sampling binds (`getChallenge`
  -- for the two `V_to_P` rounds), the `Transcript.concat`/`liftM` coercion layers, and the final
  -- `OptionT.run`/`Option.getM`. The elaborated `liftM`/`OptionT`/`Fin.induction` bind tree is
  -- defeq but not syntactically `>>=`, so the syntactic `support_bind`/`mem_support_liftComp_iff`
  -- `rw`s do not engage; instead the peel is driven by the *definitional*-unification `obtain`
  -- helpers `OracleComp.mem_support_bind_peel`/`mem_support_map_peel`/`eq_of_mem_support_pure` and
  -- `OptionT.mem_support_run_bind`/`_lift_bind` (`ArkLib/ToVCVio/.../SimulateQ.lean`). Each support
  -- element fixes a sampled `(γ₀, xs₂)` and the deterministic honest message
  -- `proverResult.1.messages ⟨1,rfl⟩ = fun j => witIn 0 j + γ₀ · witIn 1 j`; under that message
  -- `verifierBody_simulateQ_eq_pure` (via `accepts_of_inputRelation`) collapses the verifier body
  -- to `pure (some ())`, forcing `stmtOut = some _` and hence `x = some _`.
  obtain ⟨proverResult, hPR, hx⟩ := OptionT.mem_support_run_lift_bind _ _ hx
  -- Characterize the honest prover's transcript from `hPR`.
  rw [show (monadLift : OracleComp ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ) _ →
        OracleComp ([]ₒ + [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ) _) = id from rfl,
      id_eq] at hPR
  -- Peel the prover-run binds by *definitional*-unification `obtain` (the elaborated
  -- `Fin.induction` bind tree is defeq but not syntactically `>>=`, so `rw`-based
  -- peelers do not engage).
  -- `prover.run = let r ← runToRound (last 3); ⟨r.1, ← output r.2⟩`.
  obtain ⟨r3, hr3, hPR⟩ := OracleComp.mem_support_bind_peel _ _ hPR
  obtain ⟨out, _, hPR⟩ := OracleComp.mem_support_bind_peel _ _ hPR
  -- `hPR : proverResult ∈ support (pure (r3.1, out))`.
  have hPReq : proverResult = (r3.1, out) := by
    have := (mem_support_pure_iff (m := OracleComp ([]ₒ +
      [(pSpec (ι := ι) (F := F) k t).Challenge]ₒ)) proverResult (r3.1, out)).mp hPR
    simpa using this
  -- runToRound = processRound 2 (processRound 1 (processRound 0 (pure base))).
  -- Peel the round-2 bind: `r3 ∈ support (let r2 ← (rounds 0-1); round2body r2)`.
  obtain ⟨r2, hr2, hr3⟩ := OracleComp.mem_support_bind_peel _ _ hr3
  -- Peel the round-1 bind from `hr2`: `r2 ∈ support (let r1 ← (round 0); round1body r1)`.
  obtain ⟨r1, hr1, hr2⟩ := OracleComp.mem_support_bind_peel _ _ hr2
  -- Peel the round-0 bind from `hr1`: `r1 ∈ support (let r0 ← pure base; round0body r0)`.
  obtain ⟨r0, hr0, hr1⟩ := OracleComp.mem_support_bind_peel _ _ hr1
  -- Resolve `r0` to the pure base value (kept symbolic to avoid spelling `default`).
  have hr0 := OracleComp.eq_of_mem_support_pure _ hr0
  subst hr0
  -- round 0: peel the challenge `γ₀`, then resolve `r1`.
  obtain ⟨γ₀, hγ₀, hr1⟩ := OracleComp.mem_support_bind_peel _ _ hr1
  -- round 2: peel the challenge `xs₂`, then resolve `r3`.
  obtain ⟨xs₂, hxs₂, hr3⟩ := OracleComp.mem_support_bind_peel _ _ hr3
  -- Resolve `r1`, `r2`, `r3` from their `map`-of-`liftM (pure …)` supports.
  obtain ⟨f1, hf1, hr1⟩ := OracleComp.mem_support_map_peel _ _ hr1
  obtain ⟨f2, hf2, hr2⟩ := OracleComp.mem_support_map_peel _ _ hr2
  obtain ⟨f3, hf3, hr3⟩ := OracleComp.mem_support_map_peel _ _ hr3
  have hf1 := OracleComp.eq_of_mem_support_pure _ hf1
  have hf2 := OracleComp.eq_of_mem_support_pure _ hf2
  have hf3 := OracleComp.eq_of_mem_support_pure _ hf3
  subst hf1 hf2 hf3 hr1 hr2 hr3 hPReq
  -- Reduce the transcript accessors (`Fin.snoc` at indices 0/1/2) inside the verifier subterm.
  simp only [id_eq, FullTranscript.challenges, Transcript.concat,
    Fin.snoc, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.lt_iff_val_lt_val, Fin.val_zero,
    Fin.val_one, Fin.val_two, Nat.lt_irrefl, lt_self_iff_false, Fin.coe_castLT,
    Fin.castSucc_castLT, show (0 : ℕ) < 2 from by norm_num, show (0 : ℕ) < 1 from by norm_num,
    show ¬ ((2 : ℕ) < 0) from by norm_num, dif_pos, dif_neg, cast_eq,
    dite_false, dite_eq_ite, if_false, ite_false] at hx
  -- Extract the witness facts from the input relation.
  obtain ⟨hf, hM⟩ := hRel
  -- Rewrite the verifier subterm in `hx` to `pure (some ())` via `verifierBody_simulateQ_eq_pure`.
  -- `msgs`, `γ`, `xs` are inferred by unification; `hAcc1`/`hAcc2` come from
  -- `accepts_of_inputRelation` after identifying round-1 message `msgs ⟨1, rfl⟩` with honest `g`.
  rw [verifierBody_simulateQ_eq_pure (encode := (encode : (Fin k → F) → (ι → F)))
      (stmt1 := stmtIn.1.1) (mu1 := stmtIn.1.2.1) (mu2 := stmtIn.1.2.2)
      (hAcc1 := ?hAcc1) (hAcc2 := ?hAcc2)] at hx
  · -- After the rewrite the verifier round-1 query produces `pure (some ())`, so the second bind's
    -- first computation never fails. Peel it: the `none` branch is contradicted by `pure (some _)`.
    rcases OptionT.mem_support_run_bind _ _ hx with ⟨hverNone, _⟩ | ⟨stmtOut, hSO, hx⟩
    · exact absurd (OracleComp.eq_of_mem_support_pure _ hverNone) (by simp)
    -- `hSO : some stmtOut ∈ support (liftM (g <$> pure (some ())))` is defeq `pure (g (some ()))`,
    -- forcing `stmtOut = ((), embed)`; then `stmtOut.getM` succeeds and `x = some _`.
    have hSO := OracleComp.eq_of_mem_support_pure _ hSO
    rw [Option.some.injEq] at hSO
    subst hSO
    have hx := OracleComp.eq_of_mem_support_pure _ hx
    exact ⟨_, hx⟩
  case hAcc1 =>
    have hacc := accepts_of_inputRelation (encode := encode) stmtIn.1 witIn
      (fun i ↦ by have := hM i; fin_cases i <;> simpa using this) stmtIn.2
      (fun i ↦ by have := hf i; simpa using this) (cast (by rfl) γ₀) xs₂
    simp only [FullTranscript.messages, Fin.snoc, Nat.reduceLT, ↓reduceDIte, cast_eq] at *
    exact hacc.1
  case hAcc2 =>
    have hacc := accepts_of_inputRelation (encode := encode) stmtIn.1 witIn
      (fun i ↦ by have := hM i; fin_cases i <;> simpa using this) stmtIn.2
      (fun i ↦ by have := hf i; simpa using this) (cast (by rfl) γ₀) xs₂
    intro j
    simp only [FullTranscript.messages, Fin.snoc, Nat.reduceLT, ↓reduceDIte, cast_eq] at *
    exact hacc.2 j

omit [DecidableEq ι] in
/-- **Lemma 6.6 of [ABF26]** (knowledge soundness of Construction 6.2).

For any `δ ∈ (0, δ_min(C))` and fixed linear encoder with range `C`,
the toy-problem IOR has knowledge soundness against the relaxed relation
`R̃_{C,δ}^2` with error

  `max { ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|, (1 − δ)^t }`.

The `(Lambda …).toNat` in the error term is faithful: `Lambda` is never
`⊤` over a finite alphabet (`ListDecodable.Lambda_ne_top`), so `toNat`
loses nothing.

Stated against ArkLib's `OracleVerifier.knowledgeSoundness` (cf.
`OracleReduction/Security/Basic.lean :: OracleVerifier.knowledgeSoundness`,
definitionally `toVerifier.knowledgeSoundness`) — the faithful object
for an IOPP whose inputs `f₁, f₂` are oracles.

**Naming convention — paper vs API.** The ArkLib API's
`OracleVerifier.knowledgeSoundness` takes `(relIn, relOut)` where `relIn`
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
      (oracleVerifier (k := k) (t := t) (encode : (Fin k → F) → (ι → F))).knowledgeSoundness
        (WitOut := OutputWitness)
        init impl (outputRelationFor k (encode : (Fin k → F) → (ι → F)) δ)
        (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) ×
          OutputWitness))
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
  -- The former vacuity gate has CLEARED (2026-06-11): PR #569
  -- (`fix/knowledge-soundness-failing-extractor`) is merged and synced into this
  -- branch — `Verifier.knowledgeSoundness` now scores an extraction failure
  -- (`extractedWitIn? = none`) against the prover, so the always-failing
  -- `OptionT` extractor no longer discharges the game. This sorry may now be
  -- closed on its mathematical merits (paper §6.2; or via the rbrKS → KS
  -- implication once L6.8 below is proven).
  sorry

/-! ### Remark 6.7 of [ABF26] — MCA, not just CA

The L6.6 soundness argument depends on **mutual** correlated agreement
(MCA). With only correlated agreement (CA), one cannot prove every
codeword `u ∈ Λ(C, f₁ + γ·f₂, δ)` decomposes as `u = u₁ + γ·u₂` for some
`(u₁, u₂) ∈ Λ(C^{≡2}, (f₁, f₂), δ)`, so the extractor would fail. MCA
provides exactly this decomposition with probability `≥ 1 − ε_mca`. -/

omit [DecidableEq ι] in
/-- **Lemma 6.8 of [ABF26]** (round-by-round knowledge soundness of
Construction 6.2).

For any `δ ∈ (0, δ_min(C))` and fixed linear encoder with range `C`,
the IOR has round-by-round knowledge soundness (paper Definition A.5 ≡
ArkLib's `OracleVerifier.rbrKnowledgeSoundness`, definitionally
`toVerifier.rbrKnowledgeSoundness`) against `R̃_{C,δ}^2`, with
per-round errors

  * `ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|` after the γ round,
  * `(1 − δ)^t` after the spot-check round.

The `(Lambda …).toNat` in the γ-round error is faithful: `Lambda` is
never `⊤` over a finite alphabet (`ListDecodable.Lambda_ne_top`).

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
      (oracleVerifier (k := k) (t := t) (encode : (Fin k → F) → (ι → F))).rbrKnowledgeSoundness
        (WitOut := OutputWitness)
        init impl (outputRelationFor k (encode : (Fin k → F) → (ι → F)) δ)
        (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) ×
          OutputWitness))
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
