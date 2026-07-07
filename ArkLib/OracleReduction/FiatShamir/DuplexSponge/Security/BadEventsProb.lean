/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.QueryCounting

/-!
# Probabilistic analysis of the duplex-sponge bad event `E` (CO25 Lemma 5.8, Layer B)

`BadEvents.lean` defines the trace-only bad event `E := E_dup ∨ E_func` (Def 5.7), where each
component is an existential `∃ j : Fin (getBaseTrace tr).length, …` over the deduped base trace
`tr̄`.  To prove the CO25 Lemma 5.8 birthday bound
`max{Pr[E | 𝒟_𝔖], Pr[E | 𝒟_Σ]} ≤ (7T² − 3T)/(2|Σ|^c)` we first refactor `E` into a **per-index**
family and apply a union bound over `Finset.range T`.

This file provides that Layer-B scaffolding:

- **Per-index predicates** `E_h_at` / `E_p_at` / `E_pinv_at` / `E_func_at` / `E_at` — the body of the
  corresponding `BadEvents.lean` predicate with the outer `∃ j` stripped and `j : ℕ` carrying an
  explicit `j < length` proof.
- **Refactor lemmas** `E_h_iff_exists_at` … and `E_iff_exists_E_at` — `E tr ↔ ∃ j, E_at tr j`.
- **Union bound** `probEvent_E_le_sum_range` — for any experiment whose combined base trace has
  length `≤ T` on its support, `Pr[E] ≤ ∑_{j < T} Pr[E_at · j]`, plus the four-way split
  `probEvent_E_at_le` via subadditivity.

The per-index probability bounds (`Pr[E_h_at · j] ≤ 2(j−1)/|Σ|^c`, …) and the closed-form sum are
Layers C/D, developed separately.  See `Lemma_5_8_proof_plan.md`.
-/

open OracleComp OracleSpec ProtocolSpec

open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))

/-! ## Per-index bad-event predicates (outer `∃ j` stripped) -/

/-- Per-index form of `E_h` (`capacitySegmentDupHash`) at base-trace position `j`. -/
def E_h_at (j : ℕ) : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ hj : j < baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stmt : StmtIn, baseTrace[j] = ⟨.inl stmt, capSeg⟩) ∧
    isDuplicatedPriorCapacity baseTrace ⟨j, hj⟩ capSeg

/-- Per-index form of `E_p` (`capacitySegmentDupPerm`) at base-trace position `j`. -/
def E_p_at (j : ℕ) : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ hj : j < baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateIn stateOut, baseTrace[j] = ⟨.inr <| .inl stateIn, stateOut⟩ ∧
      stateOut.capacitySegment = capSeg) ∧
    isDuplicatedPriorCapacity baseTrace ⟨j, hj⟩ capSeg

/-- Per-index form of `E_pinv` (`capacitySegmentDupPermInv`) at base-trace position `j`. -/
def E_pinv_at (j : ℕ) : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ hj : j < baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateOut stateIn, baseTrace[j] = ⟨.inr <| .inr stateOut, stateIn⟩ ∧
      stateIn.capacitySegment = capSeg) ∧
    isDuplicatedPriorCapacity baseTrace ⟨j, hj⟩ capSeg

/-- Per-index form of `E_func` at base-trace position `j`. -/
def E_func_at (j : ℕ) : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ hj : j < baseTrace.length, ∃ stateIn stateOut : CanonicalSpongeState U,
    (baseTrace[j] = ⟨.inr <| .inl stateIn, stateOut⟩ ∧
      ∃ j' < (⟨j, hj⟩ : Fin baseTrace.length),
        (∃ stateOut1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <| .inl stateIn, stateOut1⟩ ∧ stateOut1 ≠ stateOut) ∨
        (∃ stateOut2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <| .inr stateOut2, stateIn⟩ ∧ stateOut2 ≠ stateOut)) ∨
    (baseTrace[j] = ⟨.inr <| .inr stateOut, stateIn⟩ ∧
      ∃ j' < (⟨j, hj⟩ : Fin baseTrace.length),
        (∃ stateIn1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <| .inr stateOut, stateIn1⟩ ∧ stateIn1 ≠ stateIn) ∨
        (∃ stateIn2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <| .inl stateIn2, stateOut⟩ ∧ stateIn2 ≠ stateIn))

/-- Per-index combined bad event: `E_h_at ∨ E_p_at ∨ E_pinv_at ∨ E_func_at` at position `j`. -/
def E_at (j : ℕ) : Prop :=
  E_h_at trace j ∨ E_p_at trace j ∨ E_pinv_at trace j ∨ E_func_at trace j

/-! ## Refactor: `E ↔ ∃ j, E_at` -/

/-- A per-index bad event fires only at a valid base-trace index. -/
lemma E_at_lt_length {j : ℕ} (h : E_at trace j) : j < (getBaseTrace trace).length := by
  rcases h with h | h | h | h
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1

lemma E_h_iff_exists_at : E_h trace ↔ ∃ j, E_h_at trace j := by
  unfold E_h capacitySegmentDupHash E_h_at
  rw [Fin.exists_iff]; simp only [Fin.getElem_fin]

lemma E_p_iff_exists_at : E_p trace ↔ ∃ j, E_p_at trace j := by
  unfold E_p capacitySegmentDupPerm E_p_at
  rw [Fin.exists_iff]; simp only [Fin.getElem_fin]

lemma E_pinv_iff_exists_at : E_pinv trace ↔ ∃ j, E_pinv_at trace j := by
  unfold E_pinv capacitySegmentDupPermInv E_pinv_at
  rw [Fin.exists_iff]; simp only [Fin.getElem_fin]

lemma E_func_iff_exists_at : E_func trace ↔ ∃ j, E_func_at trace j := by
  unfold E_func E_func_at
  rw [Fin.exists_iff]; simp only [Fin.getElem_fin]

/-- **Layer B refactor.** The trace-only bad event `E` is the pointwise disjunction of the
per-index events over all base-trace positions. -/
lemma E_iff_exists_E_at : E trace ↔ ∃ j, E_at trace j := by
  constructor
  · rintro ((hh | hp | hpi) | hfunc)
    · obtain ⟨j, hj⟩ := (E_h_iff_exists_at trace).mp hh
      exact ⟨j, Or.inl hj⟩
    · obtain ⟨j, hj⟩ := (E_p_iff_exists_at trace).mp hp
      exact ⟨j, Or.inr (Or.inl hj)⟩
    · obtain ⟨j, hj⟩ := (E_pinv_iff_exists_at trace).mp hpi
      exact ⟨j, Or.inr (Or.inr (Or.inl hj))⟩
    · obtain ⟨j, hj⟩ := (E_func_iff_exists_at trace).mp hfunc
      exact ⟨j, Or.inr (Or.inr (Or.inr hj))⟩
  · rintro ⟨j, hj | hj | hj | hj⟩
    · exact Or.inl (Or.inl ((E_h_iff_exists_at trace).mpr ⟨j, hj⟩))
    · exact Or.inl (Or.inr (Or.inl ((E_p_iff_exists_at trace).mpr ⟨j, hj⟩)))
    · exact Or.inl (Or.inr (Or.inr ((E_pinv_iff_exists_at trace).mpr ⟨j, hj⟩)))
    · exact Or.inr ((E_func_iff_exists_at trace).mpr ⟨j, hj⟩)

/-! ## Union bound: `Pr[E] ≤ ∑_{j < T} Pr[E_at · j]`

Both stated generically over an experiment `exp : ProbComp α` and a base-trace extraction
`f : α → QueryLog (…)`.  For Lemma 5.8's combined trace `tr_P̃ ‖ tr_V` take
`f := fun tr => tr.1 ++ tr.2`. -/

variable {α : Type}

/-- Per-index subadditivity: split `E_at` into its four disjuncts. -/
lemma probEvent_E_at_le
    (exp : ProbComp α) (f : α → QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Pr[ fun x => E_at (f x) j | exp]
      ≤ Pr[ fun x => E_h_at (f x) j | exp] + Pr[ fun x => E_p_at (f x) j | exp]
        + Pr[ fun x => E_pinv_at (f x) j | exp] + Pr[ fun x => E_func_at (f x) j | exp] := by
  calc Pr[ fun x => E_at (f x) j | exp]
      ≤ Pr[ fun x => E_h_at (f x) j | exp]
          + Pr[ fun x => (E_p_at (f x) j ∨ E_pinv_at (f x) j ∨ E_func_at (f x) j) | exp] :=
        probEvent_or_le exp _ _
    _ ≤ Pr[ fun x => E_h_at (f x) j | exp]
          + (Pr[ fun x => E_p_at (f x) j | exp]
              + Pr[ fun x => (E_pinv_at (f x) j ∨ E_func_at (f x) j) | exp]) := by
          gcongr; exact probEvent_or_le exp _ _
    _ ≤ Pr[ fun x => E_h_at (f x) j | exp]
          + (Pr[ fun x => E_p_at (f x) j | exp]
              + (Pr[ fun x => E_pinv_at (f x) j | exp] + Pr[ fun x => E_func_at (f x) j | exp])) := by
          gcongr; exact probEvent_or_le exp _ _
    _ = _ := by ring

/-- **Layer B union bound.** For any experiment whose combined base trace has length `≤ T` on its
support, the bad-event probability is dominated by the sum of the per-index probabilities over
`Finset.range T`. -/
lemma probEvent_E_le_sum_range
    (exp : ProbComp α) (f : α → QueryLog (duplexSpongeChallengeOracle StmtIn U)) (T : ℕ)
    (hlen : ∀ x ∈ support exp, (getBaseTrace (f x)).length ≤ T) :
    Pr[ fun x => E (f x) | exp] ≤ ∑ j ∈ Finset.range T, Pr[ fun x => E_at (f x) j | exp] := by
  have hmono :
      Pr[ fun x => E (f x) | exp]
        ≤ Pr[ fun x => ∃ j ∈ Finset.range T, E_at (f x) j | exp] := by
    apply probEvent_mono
    intro x hx hE
    obtain ⟨j, hj⟩ := (E_iff_exists_E_at (f x)).mp hE
    exact ⟨j, Finset.mem_range.mpr (lt_of_lt_of_le (E_at_lt_length (f x) hj) (hlen x hx)), hj⟩
  exact le_trans hmono
    (probEvent_exists_finset_le_sum (Finset.range T) exp (fun j x => E_at (f x) j))

/-- **Layer B, fully split.** Combines `probEvent_E_le_sum_range` with `probEvent_E_at_le`: the
bad-event probability is dominated by the sum over `j < T` of the four per-index sub-event
probabilities. -/
lemma probEvent_E_le_sum_range_split
    (exp : ProbComp α) (f : α → QueryLog (duplexSpongeChallengeOracle StmtIn U)) (T : ℕ)
    (hlen : ∀ x ∈ support exp, (getBaseTrace (f x)).length ≤ T) :
    Pr[ fun x => E (f x) | exp]
      ≤ ∑ j ∈ Finset.range T,
          (Pr[ fun x => E_h_at (f x) j | exp] + Pr[ fun x => E_p_at (f x) j | exp]
            + Pr[ fun x => E_pinv_at (f x) j | exp] + Pr[ fun x => E_func_at (f x) j | exp]) := by
  refine le_trans (probEvent_E_le_sum_range exp f T hlen) ?_
  exact Finset.sum_le_sum (fun j _ => probEvent_E_at_le exp f j)

/-! ## Layer D core: the per-index count sums to `(7T² − 3T)/2`

With `Finset.range T` running over base-trace positions `0, …, T−1`, position `j` contributes
`2j` (from `E_h`, ≤ `2j` prior output/input caps) `+ (2j+1)` (`E_p`) `+ (2j+1)` (`E_pinv`) `+ j`
(`E_func`) `= 7j + 2` collision targets (paper's `2(j−1)+(2j−1)+(2j−1)+(j−1)` under the
`0`-indexed shift). Summing: `∑_{j<T} (7j+2) = 7·T(T−1)/2 + 2T = (7T²−3T)/2`, matching
`lemma5_8Bound`'s numerator `(7·T² − 3·T)`. -/
omit [SpongeUnit U] [SpongeSize] in
lemma sum_range_perIndexCount (T : ℕ) :
    ∑ j ∈ Finset.range T, (7 * (j : ℝ) + 2) = (7 * (T : ℝ) ^ 2 - 3 * T) / 2 := by
  induction T with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

omit [SpongeUnit U] [SpongeSize] in
/-- `ℝ≥0∞` form of `sum_range_perIndexCount`, packaged as `ENNReal.ofReal` of the closed form. -/
lemma sum_range_perIndexCount_ennreal (T : ℕ) :
    ∑ j ∈ Finset.range T, (7 * (j : ℝ≥0∞) + 2)
      = ENNReal.ofReal ((7 * (T : ℝ) ^ 2 - 3 * T) / 2) := by
  have hnn : ∀ j ∈ Finset.range T, (7 * (j : ℝ) + 2) = ((7 * j + 2 : ℕ) : ℝ) := by
    intro j _; push_cast; ring
  rw [← sum_range_perIndexCount T, ENNReal.ofReal_sum_of_nonneg (by intro j _; positivity)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show (7 * (j : ℝ≥0∞) + 2) = ((7 * j + 2 : ℕ) : ℝ≥0∞) by push_cast; ring,
    show (7 * (j : ℝ) + 2) = ((7 * j + 2 : ℕ) : ℝ) by push_cast; ring,
    ENNReal.ofReal_natCast]

/-! ## Generic combiner (Layer E core)

Given, for a fixed experiment, the per-index freshness bounds
`Pr[E_h_at · j] ≤ 2j/|Σ|^c`, `Pr[E_p_at · j] ≤ (2j+1)/|Σ|^c`, `Pr[E_pinv_at · j] ≤ (2j+1)/|Σ|^c`,
`Pr[E_func_at · j] ≤ j/|Σ|^c`, together with the trace-length bound `≤ T`, the bad-event
probability is at most `lemma5_8Bound = (7T² − 3T)/(2|Σ|^c)`.  This packages Layers B+D into the
final numeric bound; only the four per-index bounds and the length bound remain experiment-specific
(Layers A/C). -/

variable [Fintype U] [Nonempty U] {α : Type}

/-- `|Σ|^c` as an `ℝ≥0∞`, the common denominator of the per-index bounds. -/
private noncomputable abbrev capPow : ℝ≥0∞ := (Fintype.card U : ℝ≥0∞) ^ SpongeSize.C

omit [SpongeUnit U] in
private lemma capPow_pos : 0 < (Fintype.card U : ℝ) ^ SpongeSize.C := by
  have : 0 < Fintype.card U := Fintype.card_pos
  positivity

/-- **Layer E core.** Assemble the per-index bounds + length bound into `lemma5_8Bound`. -/
lemma probEvent_E_le_lemma5_8Bound
    (exp : ProbComp α) (f : α → QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (tₕ tₚ tₚᵢ L : ℕ)
    (hlen : ∀ x ∈ support exp, (getBaseTrace (f x)).length ≤ tₕ + 1 + tₚ + L + tₚᵢ)
    (hh : ∀ j, Pr[ fun x => E_h_at (f x) j | exp] ≤ (2 * (j : ℝ≥0∞)) / capPow (U := U))
    (hp : ∀ j, Pr[ fun x => E_p_at (f x) j | exp] ≤ (2 * (j : ℝ≥0∞) + 1) / capPow (U := U))
    (hpi : ∀ j, Pr[ fun x => E_pinv_at (f x) j | exp] ≤ (2 * (j : ℝ≥0∞) + 1) / capPow (U := U))
    (hfunc : ∀ j, Pr[ fun x => E_func_at (f x) j | exp] ≤ (j : ℝ≥0∞) / capPow (U := U)) :
    Pr[ fun x => E (f x) | exp]
      ≤ ENNReal.ofReal (lemma5_8Bound U tₕ tₚ tₚᵢ L) := by
  set T := tₕ + 1 + tₚ + L + tₚᵢ with hT
  set K : ℝ≥0∞ := capPow (U := U) with hK
  calc Pr[ fun x => E (f x) | exp]
      ≤ ∑ j ∈ Finset.range T,
          (Pr[ fun x => E_h_at (f x) j | exp] + Pr[ fun x => E_p_at (f x) j | exp]
            + Pr[ fun x => E_pinv_at (f x) j | exp] + Pr[ fun x => E_func_at (f x) j | exp]) :=
        probEvent_E_le_sum_range_split exp f T hlen
    _ ≤ ∑ j ∈ Finset.range T,
          ((2 * (j : ℝ≥0∞)) / K + (2 * (j : ℝ≥0∞) + 1) / K
            + (2 * (j : ℝ≥0∞) + 1) / K + (j : ℝ≥0∞) / K) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        gcongr
        · exact hh j
        · exact hp j
        · exact hpi j
        · exact hfunc j
    _ = ∑ j ∈ Finset.range T, ((7 * (j : ℝ≥0∞) + 2) / K) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [div_eq_mul_inv]
        ring
    _ = (∑ j ∈ Finset.range T, (7 * (j : ℝ≥0∞) + 2)) / K := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
    _ = ENNReal.ofReal ((7 * (T : ℝ) ^ 2 - 3 * T) / 2) / K := by
        rw [sum_range_perIndexCount_ennreal]
    _ = ENNReal.ofReal (lemma5_8Bound U tₕ tₚ tₚᵢ L) := by
        have hKeq : K = ENNReal.ofReal ((Fintype.card U : ℝ) ^ SpongeSize.C) := by
          rw [hK]
          simp only [capPow]
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
        rw [hKeq, ← ENNReal.ofReal_div_of_pos (capPow_pos (U := U))]
        congr 1
        rw [lemma5_8Bound]
        push_cast [hT]
        rw [div_div]

/-! ## Assembly of Lemma 5.8

`lemma_5_8` is now proven **modulo** the two experiment-specific inputs to
`probEvent_E_le_lemma5_8Bound` — the trace-length bound (Layer A) and the four per-index freshness
bounds (Layer C) — for each of the real (`𝒟_𝔖`) and simulator (`𝒟_Σ`) sides.  Those obligations are
factored out as the named `sorry`-lemmas below so each can be attacked independently; the numeric
`max`-assembly (Layers B/D/E) is complete and verified. -/

variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : Codec pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-! ### Layer A core — the log grows by at most the number of DS queries

Running any computation under `lemma5_8CombinedImpl` appends one log entry per *successful*
DS (`Sum.inr`) query and nothing else; aborts keep the log.  So on the support of the run, the
final log length is bounded by the initial length plus the computation's total DS-query bound. -/

/-- Support-level log-length bound for the Lemma-5.8 combined implementation. -/
lemma logLength_le_of_isQueryBoundP {σ : Type}
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ (OptionT ProbComp)))
    {α : Type} {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α} {n : ℕ}
    (hb : OracleComp.IsQueryBoundP oa (fun t => t.isRight = true) n)
    (st : σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    {r : Option α × (σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))}
    (hr : r ∈ support (((simulateQ (lemma5_8CombinedImpl impl) oa).run).run st)) :
    r.2.2.length ≤ st.2.length + n := by
  induction oa using OracleComp.inductionOn generalizing st n r with
  | pure x =>
    simp only [simulateQ_pure] at hr
    have : r = (some x, st) := by simpa using hr
    subst this
    exact Nat.le_add_right _ _
  | query_bind t mx ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hb
    match t with
    | Sum.inl q => exact PEmpty.elim q
    | Sum.inr q =>
      have hn : 0 < n := hb.1.resolve_left (by simp)
      simp only [simulateQ_query_bind, lemma5_8CombinedImpl, OracleQuery.input_query,
        OracleQuery.cont_query, QueryImpl.add_apply_inr, lemma5_8WrappedDSImpl,
        Option.elimM, monadLift_self, OptionT.run_bind, OptionT.run_mk, StateT.run_bind,
        support_bind, Set.mem_iUnion] at hr
      obtain ⟨i, hi, hri⟩ := hr
      have hi' : i ∈ support ((impl q st.1).run >>= fun r₀ =>
          match r₀ with
          | none => (pure (none, st) :
              ProbComp (Option (([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q)) ×
                (σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))))
          | some (a, s') => pure (some a, (s', st.2 ++ [⟨Sum.inr q, a⟩]))) := hi
      rw [mem_support_bind_iff] at hi'
      obtain ⟨r₀, hr₀, hi'⟩ := hi'
      match r₀ with
      | none =>
        rw [mem_support_pure_iff] at hi'
        subst hi'
        have hri' : r ∈ support ((pure ((none : Option α), st) :
            ProbComp (Option α × (σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))))) :=
          hri
        rw [mem_support_pure_iff] at hri'
        subst hri'
        exact Nat.le_add_right _ _
      | some (a, s') =>
        rw [mem_support_pure_iff] at hi'
        subst hi'
        have hri' : r ∈ support ((simulateQ (lemma5_8CombinedImpl impl) (mx a)).run.run
            (s', st.2 ++ [⟨Sum.inr q, a⟩])) := hri
        have hbnd := hb.2 a
        rw [if_pos (by simp : (Sum.inr q : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain
          ).isRight = true)] at hbnd
        have hlen := ih a hbnd _ hri'
        simp only [List.length_append, List.length_singleton] at hlen
        omega

/-- The empty oracle spec is (vacuously) finite and inhabited per query point. -/
instance : (([]ₒ : OracleSpec.{0, 0} PEmpty.{1})).Fintype where
  fintype_B t := t.elim

instance : (([]ₒ : OracleSpec.{0, 0} PEmpty.{1})).Inhabited where
  inhabited_B t := t.elim

/-- The concrete `IsUniformSpec` instances for the Lemma-5.8 oracle surfaces (uniform
challenge/permutation answers are well-defined since `U` is a finite nonempty sponge unit). -/
noncomputable instance : IsUniformSpec (duplexSpongeForwardOracle StmtIn U) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable instance :
    IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable instance :
    IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeChallengeOracle StmtIn U) :=
  IsUniformSpec.ofFintypeInhabited _

/-! ### Layer A: combining the per-class totals into the total DS-query bound -/

/-- The three DS classes are exhaustive on `Sum.inr` and disjoint: per-class totals combine
into the total DS (`Sum.isRight`) bound. -/
lemma isQueryBoundP_isRight_of_classes {α : Type}
    {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α} {tₕ tₚ tₚᵢ : ℕ}
    (hh : OracleComp.IsQueryBoundP oa
      (fun t => isHashQueryPoint (StmtIn := StmtIn) (U := U) t = true) tₕ)
    (hp : OracleComp.IsQueryBoundP oa
      (fun t => isFwdPermQueryPoint (StmtIn := StmtIn) (U := U) t = true) tₚ)
    (hpi : OracleComp.IsQueryBoundP oa
      (fun t => isBwdPermQueryPoint (StmtIn := StmtIn) (U := U) t = true) tₚᵢ) :
    OracleComp.IsQueryBoundP oa (fun t => t.isRight = true) (tₕ + tₚ + tₚᵢ) := by
  have h2 := IsQueryBoundP.or_add hh hp (by
    rintro (e | (s | (c | c))) ⟨h1, h2⟩ <;>
      simp_all [isHashQueryPoint, isFwdPermQueryPoint])
  have h3 := IsQueryBoundP.or_add h2 hpi (by
    rintro (e | (s | (c | c))) ⟨h1, h2⟩ <;>
      simp_all [isHashQueryPoint, isFwdPermQueryPoint, isBwdPermQueryPoint])
  rw [isQueryBoundP_congr_pred (p' := fun t => Sum.isRight t = true)] at h3
  · exact h3
  · rintro (e | (s | (c | c))) <;>
      simp [isHashQueryPoint, isFwdPermQueryPoint, isBwdPermQueryPoint]

/-! ### Layer A: the wide forward verifier is a `(1, L, 0)`-query algorithm -/

/-- Wide-spec forward verifier, forward-permutation class: `≤ L`. -/
lemma runForwardVerifierWide_fwd_bound
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)]
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeChallengeOracle StmtIn U)]
    (hδR : δ ≤ SpongeSize.R)
    (V : Verifier ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    OracleComp.IsQueryBoundP (runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof)
      (fun t => isFwdPermQueryPoint (StmtIn := StmtIn) (U := U) t = true)
      pSpec.totalNumPermQueries := by
  rw [runForwardVerifierWide]
  refine isQueryBoundP_liftComp' _
    (p := fun t => isNarrowFwdPermPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true)
    (fun t => ?_) (dsfsForwardVerify_fwd_bound hδR V stmtIn proof)
  rcases t with e | (s | c)
  · exact e.elim
  · rfl
  · rfl

/-- Wide-spec forward verifier, hash class: `≤ 1`. -/
lemma runForwardVerifierWide_hash_bound
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)]
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeChallengeOracle StmtIn U)]
    (V : Verifier ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    OracleComp.IsQueryBoundP (runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof)
      (fun t => isHashQueryPoint (StmtIn := StmtIn) (U := U) t = true) 1 := by
  rw [runForwardVerifierWide]
  refine isQueryBoundP_liftComp' _
    (p := fun t => isNarrowHashPoint (oSpec := []ₒ) (StmtIn := StmtIn) (U := U) t = true)
    (fun t => ?_) (dsfsForwardVerify_hash_bound V stmtIn proof)
  rcases t with e | (s | c)
  · exact e.elim
  · rfl
  · rfl

/-- Wide-spec forward verifier, inverse-permutation class: `0` — the narrow spec has no `p⁻¹`
slot, so no narrow query can land in the wide inverse class. -/
lemma runForwardVerifierWide_bwd_bound
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)]
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeChallengeOracle StmtIn U)]
    (V : Verifier ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) StmtIn StmtOut pSpec) (stmtIn : StmtIn)
    (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    OracleComp.IsQueryBoundP (runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof)
      (fun t => isBwdPermQueryPoint (StmtIn := StmtIn) (U := U) t = true) 0 := by
  rw [runForwardVerifierWide]
  refine isQueryBoundP_liftComp' _
    (p := fun _ => False)
    (fun t => ?_) (isQueryBoundP_zero_of_forall_not _ (by simp))
  rcases t with e | (s | c)
  · exact e.elim
  · exact iff_of_false Bool.false_ne_true not_false
  · exact iff_of_false Bool.false_ne_true not_false

/-! ### Layer A: generic length bound for the abortable experiment -/

/-- **Layer A, generic.** Any instantiation of the abortable Lemma-5.8 experiment (real or
simulated) produces a combined base trace of length at most `T = tₕ + 1 + tₚ + L + tₚᵢ`:
the prover contributes at most its `(tₕ, tₚ, tₚᵢ)` budget, the forward verifier its
`(1, L, 0)` budget, and projection/deduplication only shorten. -/
lemma lemma5_8ProjectedTraceDistAbortable_length {σ : Type}
    [IsUniformSpec (duplexSpongeForwardOracle StmtIn U)]
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeForwardOracle StmtIn U)]
    [IsUniformSpec (([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) + duplexSpongeChallengeOracle StmtIn U)]
    (init : ProbComp σ)
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ (OptionT ProbComp)))
    (V : Verifier ([]ₒ : OracleSpec.{0, 0} PEmpty.{1}) StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) (hδR : δ ≤ SpongeSize.R)
    (hMaliciousBound : IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) maliciousProver tₕ tₚ tₚᵢ) :
    ∀ tr ∈ support (lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
        (pSpec := pSpec) (U := U) (δ := δ) init impl V maliciousProver),
      (getBaseTrace (tr.1 ++ tr.2)).length
        ≤ tₕ + 1 + tₚ + pSpec.totalNumPermQueries + tₚᵢ := by
  intro tr htr
  -- Total prover DS budget from the three per-class totals.
  have hproverBound : OracleComp.IsQueryBoundP maliciousProver
      (fun t => t.isRight = true) (tₕ + tₚ + tₚᵢ) :=
    isQueryBoundP_isRight_of_classes hMaliciousBound.1 hMaliciousBound.2.1 hMaliciousBound.2.2
  rw [lemma5_8ProjectedTraceDistAbortable] at htr
  rw [mem_support_bind_iff] at htr
  obtain ⟨s₀, _, htr⟩ := htr
  rw [mem_support_bind_iff] at htr
  obtain ⟨proverResult, hpr, htr⟩ := htr
  -- Prover log length.
  have hplen := logLength_le_of_isQueryBoundP impl hproverBound (s₀, ([] : QueryLog _)) hpr
  simp only [List.length_nil, Nat.zero_add] at hplen
  -- Case on abort.
  obtain ⟨res, s₁, trP⟩ := proverResult
  rcases res with _ | ⟨stmtIn, proof⟩
  · -- Abort: `tr_V = []`.
    rw [mem_support_pure_iff] at htr
    subst htr
    calc (getBaseTrace (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP ++ [])).length
        ≤ (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP ++ []).length :=
          (getBaseTrace_sublist _).length_le
      _ ≤ trP.length := by
          rw [List.append_nil, lemma5_8ProjectTraceLog]
          exact List.length_filterMap_le _ _
      _ ≤ tₕ + 1 + tₚ + pSpec.totalNumPermQueries + tₚᵢ := by
          have hp : trP.length ≤ tₕ + tₚ + tₚᵢ := hplen
          omega
  · -- Success: the verifier runs with a fresh log.
    rw [mem_support_bind_iff] at htr
    obtain ⟨verifierResult, hvr, htr⟩ := htr
    rw [mem_support_pure_iff] at htr
    subst htr
    -- Verifier total DS budget: `(1, L, 0)`.
    have hverifBound : OracleComp.IsQueryBoundP
        (runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof)
        (fun t => t.isRight = true) (1 + pSpec.totalNumPermQueries + 0) :=
      isQueryBoundP_isRight_of_classes
        (runForwardVerifierWide_hash_bound V stmtIn proof)
        (runForwardVerifierWide_fwd_bound hδR V stmtIn proof)
        (runForwardVerifierWide_bwd_bound V stmtIn proof)
    have hvlen := logLength_le_of_isQueryBoundP impl hverifBound (s₁, ([] : QueryLog _)) hvr
    simp only [List.length_nil, Nat.zero_add] at hvlen
    calc (getBaseTrace (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP
            ++ lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) verifierResult.2.2)).length
        ≤ (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP
            ++ lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) verifierResult.2.2).length :=
          (getBaseTrace_sublist _).length_le
      _ ≤ trP.length + verifierResult.2.2.length := by
          rw [List.length_append]
          gcongr <;> · rw [lemma5_8ProjectTraceLog]; exact List.length_filterMap_le _ _
      _ ≤ tₕ + 1 + tₚ + pSpec.totalNumPermQueries + tₚᵢ := by
          have hp : trP.length ≤ tₕ + tₚ + tₚᵢ := hplen
          omega

/-! ### Layer A — trace-length bounds

Instantiations of the generic bound for the two concrete experiments. -/

/-- **Layer A (real).** The combined base trace of the `𝒟_𝔖` experiment has length `≤ T`.
`tr_P̃` contributes `≤ tₕ + tₚ + tₚᵢ` (prover query budget); the forward verifier `tr_V`
contributes `≤ 1 + L` (`(1, L, 0)`-query).  `getBaseTrace` only shortens. -/
lemma lemma5_8_real_length
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hδR : δ ≤ SpongeSize.R)
    (hMaliciousBound : IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) maliciousProver tₕ tₚ tₚᵢ)
    (hTp : tₚ ≥ pSpec.totalNumPermQueries) :
    ∀ tr ∈ support (lemma5_8RealTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut)
        (n := n) (pSpec := pSpec) (U := U) (δ := δ)
        (D_𝔖 StmtIn U).sample ((D_𝔖 StmtIn U).eagerImpl) V maliciousProver),
      (getBaseTrace (tr.1 ++ tr.2)).length ≤ tₕ + 1 + tₚ + pSpec.totalNumPermQueries + tₚᵢ := by
  rw [lemma5_8RealTraceDist]
  exact lemma5_8ProjectedTraceDistAbortable_length _ _ V maliciousProver tₕ tₚ tₚᵢ hδR
    hMaliciousBound

/-- **Layer A (sigma).** Same length bound for the `𝒟_Σ` simulator experiment. -/
lemma lemma5_8_sigma_length
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hδR : δ ≤ SpongeSize.R)
    (hMaliciousBound : IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) maliciousProver tₕ tₚ tₚᵢ)
    (hTp : tₚ ≥ pSpec.totalNumPermQueries) :
    ∀ tr ∈ support (lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ)
        (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U)
        V maliciousProver),
      (getBaseTrace (tr.1 ++ tr.2)).length ≤ tₕ + 1 + tₚ + pSpec.totalNumPermQueries + tₚᵢ := by
  intro tr htr
  rw [lemma5_8SigmaTraceDist, mem_support_bind_iff] at htr
  obtain ⟨k_g, _, htr⟩ := htr
  exact lemma5_8ProjectedTraceDistAbortable_length _ _ V maliciousProver tₕ tₚ tₚᵢ hδR
    hMaliciousBound tr htr

/-! ### Layer C, real `E_func` — the real permutation is a genuine function

On the `𝒟_𝔖` side every trace entry is answered by the *fixed* sampled realization `(h, p, p⁻¹)`,
so the projected log is functionally consistent (`e.2 = realAnswer fam e.1`) and `E_func`
(two conflicting permutation entries) is impossible — CO25 Eq. 33, real branch. -/

/-- The deterministic answer of one sampled real `(h, p, p⁻¹)` realization on a narrow DS point. -/
def realAnswer (fam : (D_𝔖 StmtIn U).Carrier) :
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) →
      (duplexSpongeChallengeOracle StmtIn U).Range t
  | .inl q => fam.1 q
  | .inr (.inl sIn) => (show Equiv.Perm (CanonicalSpongeState U) from fam.2) sIn
  | .inr (.inr sOut) => (show Equiv.Perm (CanonicalSpongeState U) from fam.2).symm sOut

/-- A functionally-consistent trace (every entry answered by the fixed real realization) has no
`E_func` conflict at any position: `p` is a genuine bijection, so no two entries disagree. -/
lemma E_func_at_false_of_consistent
    (fam : (D_𝔖 StmtIn U).Carrier)
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hc : ∀ e ∈ getBaseTrace trace, e.2 = realAnswer fam e.1) (j : ℕ) :
    ¬ E_func_at trace j := by
  rintro ⟨hj, sIn, sOut, hdisj⟩
  have key : ∀ (k : ℕ) (hk : k < (getBaseTrace trace).length)
      (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
      (a : (duplexSpongeChallengeOracle StmtIn U).Range q),
      (getBaseTrace trace)[k] = ⟨q, a⟩ → a = realAnswer fam q := by
    intro k hk q a hka
    have hmem : (getBaseTrace trace)[k] ∈ getBaseTrace trace := List.getElem_mem _
    have := hc _ hmem
    rw [hka] at this
    exact this
  set p : Equiv.Perm (CanonicalSpongeState U) := fam.2 with hp
  have eF : ∀ s, realAnswer fam (.inr (.inl s)) = p s := fun _ => rfl
  have eB : ∀ s, realAnswer fam (.inr (.inr s)) = p.symm s := fun _ => rfl
  rcases hdisj with ⟨hbtj, j', _, hprior⟩ | ⟨hbtj, j', _, hprior⟩
  · -- forward query at `j`: `sOut = p sIn`.
    have hj0 : sOut = p sIn := by rw [← eF]; exact key j hj _ _ hbtj
    rcases hprior with ⟨sOut1, hbtj', hne⟩ | ⟨sOut2, hbtj', hne⟩
    · have hj1 : sOut1 = p sIn := by rw [← eF]; exact key j' j'.2 _ _ hbtj'
      exact hne (hj1.trans hj0.symm)
    · have hj1 : sIn = p.symm sOut2 := by rw [← eB]; exact key j' j'.2 _ _ hbtj'
      exact hne (by rw [hj0, hj1, Equiv.apply_symm_apply])
  · -- inverse query at `j`: `sIn = p⁻¹ sOut`.
    have hj0 : sIn = p.symm sOut := by rw [← eB]; exact key j hj _ _ hbtj
    rcases hprior with ⟨sIn1, hbtj', hne⟩ | ⟨sIn2, hbtj', hne⟩
    · have hj1 : sIn1 = p.symm sOut := by rw [← eB]; exact key j' j'.2 _ _ hbtj'
      exact hne (hj1.trans hj0.symm)
    · have hj1 : sOut = p sIn2 := by rw [← eF]; exact key j' j'.2 _ _ hbtj'
      exact hne (by rw [hj0, hj1, Equiv.symm_apply_apply])

/-- Consistency of a wide (`[]ₒ + DS`) trace entry with a real realization: DS entries must carry
the deterministic real answer; the (uncallable) empty branch is vacuously consistent. -/
def wideRealConsistent (fam : (D_𝔖 StmtIn U).Carrier)
    (e : (t : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain) ×
      ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range t) : Prop :=
  match e with
  | ⟨.inl _, _⟩ => True
  | ⟨.inr q, r⟩ => r = realAnswer fam q

/-- **Generic support invariant** for the combined Lemma-5.8 implementation under a *deterministic*
DS oracle `impl` (each query returns the table answer `ans s q` and preserves the carrier `s`).
Abstract `impl`/`σ` so the `OptionT`-monad membership normalizes exactly as in
`logLength_le_of_isQueryBoundP`; the eager real oracle is a special case. -/
lemma combinedImpl_support_invariant {σ α : Type}
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ (OptionT ProbComp)))
    (ans : σ → (q : (duplexSpongeChallengeOracle StmtIn U).Domain) →
      (duplexSpongeChallengeOracle StmtIn U).Range q)
    (hdet : ∀ (q : (duplexSpongeChallengeOracle StmtIn U).Domain) (s : σ),
        (impl q s).run = pure (some (ans s q, s)))
    {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α}
    (st : σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    {r : Option α × (σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))}
    (hr : r ∈ support (((simulateQ (lemma5_8CombinedImpl impl) oa).run).run st)) :
    r.2.1 = st.1 ∧ ∀ e ∈ r.2.2, e ∈ st.2 ∨ ∃ q, e = ⟨Sum.inr q, ans st.1 q⟩ := by
  induction oa using OracleComp.inductionOn generalizing st r with
  | pure x =>
    simp only [simulateQ_pure] at hr
    have : r = (some x, st) := by simpa using hr
    subst this
    exact ⟨rfl, fun e he => Or.inl he⟩
  | query_bind t mx ih =>
    match t with
    | Sum.inl q => exact PEmpty.elim q
    | Sum.inr q =>
      simp only [simulateQ_query_bind, lemma5_8CombinedImpl, OracleQuery.input_query,
        OracleQuery.cont_query, QueryImpl.add_apply_inr, lemma5_8WrappedDSImpl,
        Option.elimM, monadLift_self, OptionT.run_bind, OptionT.run_mk, StateT.run_bind,
        support_bind, Set.mem_iUnion] at hr
      obtain ⟨i, hi, hri⟩ := hr
      have hi' : i ∈ support ((impl q st.1).run >>= fun r₀ =>
          match r₀ with
          | none => (pure (none, st) :
              ProbComp (Option (([]ₒ + duplexSpongeChallengeOracle StmtIn U).Range (Sum.inr q)) ×
                (σ × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))))
          | some (a, s') => pure (some a, (s', st.2 ++ [⟨Sum.inr q, a⟩]))) := hi
      rw [hdet, mem_support_bind_iff] at hi'
      obtain ⟨r₀, hr₀, hi'⟩ := hi'
      rw [mem_support_pure_iff] at hr₀
      subst hr₀
      rw [mem_support_pure_iff] at hi'
      subst hi'
      have hri' : r ∈ support ((simulateQ (lemma5_8CombinedImpl impl)
          (mx (ans st.1 q))).run.run (st.1, st.2 ++ [⟨Sum.inr q, ans st.1 q⟩])) := hri
      have hIH := ih (ans st.1 q) (st.1, st.2 ++ [⟨Sum.inr q, ans st.1 q⟩]) hri'
      refine ⟨hIH.1, fun e he => ?_⟩
      rcases hIH.2 e he with hmem | hcons
      · rcases List.mem_append.mp hmem with h | h
        · exact Or.inl h
        · rw [List.mem_singleton] at h
          subst h
          exact Or.inr ⟨q, rfl⟩
      · exact Or.inr hcons

/-- **Real-side support invariant.** Running any computation under the real (eager-table)
implementation preserves the sampled carrier and appends only table-consistent entries. -/
lemma realConsistent_of_mem_support {α : Type}
    {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α}
    (st : (D_𝔖 StmtIn U).Carrier × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    {r : Option α × ((D_𝔖 StmtIn U).Carrier ×
      QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))}
    (hr : r ∈ support (((simulateQ (lemma5_8CombinedImpl
        (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl))) oa).run).run st)) :
    r.2.1 = st.1 ∧ ∀ e ∈ r.2.2, e ∈ st.2 ∨ wideRealConsistent st.1 e := by
  have hdet : ∀ (q : (duplexSpongeChallengeOracle StmtIn U).Domain) (s : (D_𝔖 StmtIn U).Carrier),
      (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl) q s).run
        = pure (some (realAnswer s q, s)) := by
    intro q s
    rcases q with hq | (sIn | sOut) <;> rfl
  have hinv := combinedImpl_support_invariant
    (lemma5_8TotalAbortLift ((D_𝔖 StmtIn U).eagerImpl)) realAnswer hdet st hr
  refine ⟨hinv.1, fun e he => (hinv.2 e he).imp id ?_⟩
  rintro ⟨q, rfl⟩
  rfl

/-- **Projection bridge.** A wide log that is entirely `wideRealConsistent` projects to a narrow
log that is `realAnswer`-consistent (`e.2 = realAnswer fam e.1`). -/
lemma projectTraceLog_realConsistent (fam : (D_𝔖 StmtIn U).Carrier)
    (L : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))
    (h : ∀ e ∈ L, wideRealConsistent fam e) :
    ∀ e ∈ lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) L, e.2 = realAnswer fam e.1 := by
  intro e he
  rw [lemma5_8ProjectTraceLog, List.mem_filterMap] at he
  obtain ⟨⟨wi, wr⟩, hwe, heq⟩ := he
  rcases wi with q | q
  · exact q.elim
  · rw [Option.some.injEq] at heq
    subst heq
    have := h _ hwe
    simpa [wideRealConsistent] using this

/-! ### Layer C — per-index freshness bounds

For each side, at base-trace position `j` (`0`-indexed, so `j` priors), the freshly-sampled `j`-th
answer capacity is uniform in `Σ^c` and collides with `≤ 2j` (h) / `≤ 2j+1` (p, p⁻¹) / `≤ j` (func)
prior capacities.  Real side: `h` uniform random function, `p`/`p⁻¹` random permutation
(near-uniform ⇒ the new permutation-freshness lemma), and `E_func` never fires (`p` genuine
function) so its bound is `0 ≤ j/|Σ|^c`.  Sigma side: all answers lazily uniform (`d2sQueryImpl`),
`E_func` via the `Cache_p ∩ tr` count. -/

variable [Fintype U] [Nonempty U]

/-! #### Step R — union-bound reduction of the per-index E_h/E_p/E_pinv events

Each `E_X_at · j` is covered by the ≤ 2j pairwise capacity collisions between the entry at base
position `j` and the ≤ 2 capacity segments exposed by each earlier position `j' < j`.  This
reduces the per-index probability to a sum of collision *atoms* `Pr[collision(j,j',k)] ≤ 1/|Σ|^c`
(the atoms are the genuinely probabilistic obligation; the reduction below is pure). -/

/-- The (≤ 2) capacity segments a base-trace entry exposes as collision sources, indexed by
`Fin 2`: a hash entry exposes only its output (`k = 0`); a permutation entry exposes both its
domain- and range-state capacities. -/
def entryCapAt :
    ((t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t) → Fin 2 → Option (Vector U SpongeSize.C)
  | ⟨.inl _, out⟩, k => if k = 0 then some out else none
  | ⟨.inr (.inl sIn), sOut⟩, k =>
      if k = 0 then some sIn.capacitySegment else some sOut.capacitySegment
  | ⟨.inr (.inr sOut), sIn⟩, k =>
      if k = 0 then some sOut.capacitySegment else some sIn.capacitySegment

/-- The output capacity of base position `j` if it is a hash entry, else `none`. -/
def hashOutCapAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option (Vector U SpongeSize.C) :=
  (bt[j]?).bind fun e => match e with | ⟨.inl _, out⟩ => some out | ⟨.inr _, _⟩ => none

/-- E_h collision atom: base position `j` is a hash entry whose output capacity equals the
`k`-th capacity segment of base position `j'`. -/
def hashCollisionAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (j j' : ℕ) (k : Fin 2) : Prop :=
  ∃ c, hashOutCapAt bt j = some c ∧ (bt[j']?).bind (fun e => entryCapAt e k) = some c

/-- **Step R (E_h).** The per-index hash duplication event at `j` is covered by the finite family
of `≤ 2j` pairwise collisions with earlier positions. -/
lemma E_h_at_imp_exists_collision
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) (h : E_h_at trace j) :
    ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
      hashCollisionAt (getBaseTrace trace) j p.1 p.2 := by
  classical
  obtain ⟨hj, capSeg, ⟨stmt, hbtj⟩, hdup⟩ := h
  -- base[j] is a hash entry with output capSeg ⇒ hashOutCapAt = some capSeg.
  have hhash : hashOutCapAt (getBaseTrace trace) j = some capSeg := by
    simp only [hashOutCapAt, List.getElem?_eq_getElem hj, Option.bind_some, hbtj]
  -- Package: from a Fin prior `j' < j` with a matching slot capacity, build the witness.
  have mk : ∀ (j' : Fin (getBaseTrace trace).length) (k : Fin 2), (j' : ℕ) < j →
      entryCapAt (getBaseTrace trace)[j'] k = some capSeg →
      ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
        hashCollisionAt (getBaseTrace trace) j p.1 p.2 := by
    intro j' k hlt hce
    refine ⟨((j' : ℕ), k), by simp [Finset.mem_product, Finset.mem_range, hlt], capSeg, hhash, ?_⟩
    rw [List.getElem?_eq_getElem j'.2]
    exact hce
  -- For the `≤ j` disjuncts (4,5): base[j'] is a permutation entry, base[j] is hash ⇒ `j' ≠ j`.
  have hlt_of_le : ∀ (j' : Fin (getBaseTrace trace).length),
      j' ≤ (⟨j, hj⟩ : Fin (getBaseTrace trace).length) →
      (∀ stmt', (getBaseTrace trace)[j'] ≠ (⟨.inl stmt', capSeg⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t)) → (j' : ℕ) < j := by
    intro j' hle hperm
    refine lt_of_le_of_ne (Fin.le_def.mp hle) (fun heq => ?_)
    have hjj' : j' = (⟨j, hj⟩ : Fin (getBaseTrace trace).length) := Fin.ext heq
    exact hperm stmt (by rw [hjj', Fin.getElem_fin]; exact hbtj)
  rcases hdup with ⟨j', hlt, stmt', he⟩ | ⟨j', hlt, sIn1, sOut1, he, hc⟩ |
      ⟨j', hlt, sOut2, sIn2, he, hc⟩ | ⟨j', hlt, sIn3, sOut3, he, hc⟩ |
      ⟨j', hlt, sOut4, sIn4, he, hc⟩
  · exact mk j' 0 (Fin.lt_def.mp hlt) (by rw [he]; rfl)
  · exact mk j' 1 (Fin.lt_def.mp hlt) (by rw [he]; exact congrArg some hc)
  · exact mk j' 1 (Fin.lt_def.mp hlt) (by rw [he]; exact congrArg some hc)
  · exact mk j' 0 (hlt_of_le j' hlt (fun s' hs' => by simp [he] at hs'))
      (by rw [he]; exact congrArg some hc)
  · exact mk j' 0 (hlt_of_le j' hlt (fun s' hs' => by simp [he] at hs'))
      (by rw [he]; exact congrArg some hc)

/-- **Step A (real E_h atom).** On the real experiment, for an *earlier* base position `j' < j`,
the probability that the hash answer at base position `j` equals the `k`-th capacity at `j'` is
`≤ 1/|Σ|^c`: the real hash oracle is a uniform random function, so `h(stmtⱼ)` is fresh-uniform in
`Σ^c` and independent of the prior `j' < j` capacity.  The hypothesis `j' < j` is essential — for
`j' = j` the entry collides with its own capacity with probability `1` (the atom would be false).
Freshness rests on base-trace no-redundancy (`getBaseTrace_noRedundant`) + real consistency
(`realConsistent_of_mem_support`): distinct base positions carry distinct hash statements.
(Proof: eager→lazy conversion of the hash sub-oracle, then VCVio `probEvent_log_entry_eq_le`.) -/
lemma real_hashCollision_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j j' : ℕ) (hj' : j' < j) (k : Fin 2) :
    Pr[ fun tr => hashCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j j' k |
        lemma5_8RealTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) (D_𝔖 StmtIn U).sample ((D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ 1 / capPow (U := U) := by
  sorry

/-- **Generic E_h bound-from-atom.** For any experiment producing a `(tr_P̃, tr_V)` pair, if the
per-pair hash-collision atom holds (`≤ 1/|Σ|^c` for every earlier position `j' < j` and slot `k`),
then the per-index `E_h` bound `≤ 2j/|Σ|^c` follows by the Step-R union bound.  Shared by the real
and simulator sides — only the atom differs. -/
lemma E_h_bound_of_atom
    (exp : ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (duplexSpongeChallengeOracle StmtIn U))) (j : ℕ)
    (hatom : ∀ j', j' < j → ∀ k : Fin 2,
      Pr[ fun tr => hashCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j j' k | exp]
        ≤ 1 / capPow (U := U)) :
    Pr[ fun tr => E_h_at (tr.1 ++ tr.2) j | exp] ≤ (2 * (j : ℝ≥0∞)) / capPow (U := U) := by
  calc Pr[ fun tr => E_h_at (tr.1 ++ tr.2) j | exp]
      ≤ Pr[ fun tr => ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
            hashCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j p.1 p.2 | exp] :=
        probEvent_mono fun tr _ h => E_h_at_imp_exists_collision _ j h
    _ ≤ ∑ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
          Pr[ fun tr => hashCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j p.1 p.2 | exp] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))), (1 / capPow (U := U)) :=
        Finset.sum_le_sum fun p hp =>
          hatom p.1 (Finset.mem_range.mp (Finset.mem_product.mp hp).1) p.2
    _ = (2 * (j : ℝ≥0∞)) / capPow (U := U) := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        simp only [one_div, div_eq_mul_inv]
        push_cast
        ring

/-- Layer C, real `E_h`: `Pr[E_h_at · j] ≤ 2j/|Σ|^c`. -/
lemma lemma5_8_real_E_h_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_h_at (tr.1 ++ tr.2) j |
        lemma5_8RealTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) (D_𝔖 StmtIn U).sample ((D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞)) / capPow (U := U) :=
  E_h_bound_of_atom _ j fun j' hj' k => real_hashCollision_le V maliciousProver j j' hj' k

/-! #### Step R — reduction of E_p (fwd-permutation output-capacity duplication)

`E_p_at·j` fires when the *output* capacity of the fwd-perm entry at base position `j` duplicates
a capacity. This is covered by ≤ 2j pairwise collisions with earlier positions (`j' < j`) plus one
**self** collision (the entry's own input capacity equals its output capacity — the `j' = j` case
of `isDuplicatedPriorCapacity`'s fourth disjunct), giving the `2j+1` count. -/

/-- Output capacity of base position `j` if it is a fwd-permutation entry. -/
def permOutCapAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option (Vector U SpongeSize.C) :=
  (bt[j]?).bind fun e => match e with
    | ⟨.inr (.inl _), sOut⟩ => some sOut.capacitySegment
    | _ => none

/-- Input capacity of base position `j` if it is a fwd-permutation entry. -/
def permInCapAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option (Vector U SpongeSize.C) :=
  (bt[j]?).bind fun e => match e with
    | ⟨.inr (.inl sIn), _⟩ => some sIn.capacitySegment
    | _ => none

/-- E_p prior-collision atom: fwd-perm output at `j` matches the `k`-th capacity at `j'`. -/
def permOutCollisionAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (j j' : ℕ) (k : Fin 2) : Prop :=
  ∃ c, permOutCapAt bt j = some c ∧ (bt[j']?).bind (fun e => entryCapAt e k) = some c

/-- E_p self-collision atom: the fwd-perm entry at `j` has equal input and output capacities. -/
def permSelfCollisionAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) : Prop :=
  ∃ c, permOutCapAt bt j = some c ∧ permInCapAt bt j = some c

/-- **Step R (E_p).** `E_p_at·j` is covered by the self collision or one of the `≤ 2j` prior
collisions. -/
lemma E_p_at_imp_collision
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) (h : E_p_at trace j) :
    permSelfCollisionAt (getBaseTrace trace) j ∨
      ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
        permOutCollisionAt (getBaseTrace trace) j p.1 p.2 := by
  classical
  obtain ⟨hj, capSeg, ⟨sInj, sOutj, hbtj, hcapj⟩, hdup⟩ := h
  have hout : permOutCapAt (getBaseTrace trace) j = some capSeg := by
    simp only [permOutCapAt, List.getElem?_eq_getElem hj, Option.bind_some, hbtj]
    exact congrArg some hcapj
  -- prior-collision packager
  have mkP : ∀ (j' : Fin (getBaseTrace trace).length) (k : Fin 2), (j' : ℕ) < j →
      entryCapAt (getBaseTrace trace)[j'] k = some capSeg →
      permSelfCollisionAt (getBaseTrace trace) j ∨
        ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
          permOutCollisionAt (getBaseTrace trace) j p.1 p.2 := by
    intro j' k hlt hce
    refine Or.inr ⟨((j' : ℕ), k), by simp [Finset.mem_product, Finset.mem_range, hlt],
      capSeg, hout, ?_⟩
    rw [List.getElem?_eq_getElem j'.2]; exact hce
  rcases hdup with ⟨j', hlt, stmt', he⟩ | ⟨j', hlt, s1, s2, he, hc⟩ |
      ⟨j', hlt, s1, s2, he, hc⟩ | ⟨j', hlt, s1, s2, he, hc⟩ | ⟨j', hlt, s1, s2, he, hc⟩
  · exact mkP j' 0 (Fin.lt_def.mp hlt) (by rw [he]; rfl)
  · exact mkP j' 1 (Fin.lt_def.mp hlt) (by rw [he]; exact congrArg some hc)
  · exact mkP j' 1 (Fin.lt_def.mp hlt) (by rw [he]; exact congrArg some hc)
  · -- disjunct 4 (`j' ≤ j`): split `j' < j` (prior) vs `j' = j` (self).
    rcases lt_or_eq_of_le (Fin.le_def.mp hlt) with hlt' | heq
    · exact mkP j' 0 hlt' (by rw [he]; exact congrArg some hc)
    · -- `j' = j`: base[j] = ⟨.inr (.inl s1), s2⟩ = ⟨.inr (.inl sInj), sOutj⟩ ⇒ s1 = sInj.
      have hjj' : j' = (⟨j, hj⟩ : Fin (getBaseTrace trace).length) := Fin.ext heq
      rw [hjj', Fin.getElem_fin, hbtj] at he
      obtain ⟨he1, _he2⟩ := Sigma.mk.inj_iff.mp he
      refine Or.inl ⟨capSeg, hout, ?_⟩
      simp only [permInCapAt, List.getElem?_eq_getElem hj, Option.bind_some, hbtj]
      have hs : sInj = s1 := Sum.inl.inj (Sum.inr.inj he1)
      rw [hs]
      exact congrArg some hc
  · -- disjunct 5 (`j' ≤ j`): base[j'] is a bwd entry but base[j] is fwd ⇒ `j' < j`.
    have hlt' : (j' : ℕ) < j := by
      refine lt_of_le_of_ne (Fin.le_def.mp hlt) (fun heq => ?_)
      have hjj' : j' = (⟨j, hj⟩ : Fin (getBaseTrace trace).length) := Fin.ext heq
      rw [hjj', Fin.getElem_fin, hbtj] at he
      exact absurd he (by simp)
    exact mkP j' 0 hlt' (by rw [he]; exact congrArg some hc)

/-- **Generic E_p bound-from-atoms.** The self-collision atom plus the `≤ 2j` prior-collision atoms
combine (union bound) to `≤ (2j+1)/|Σ|^c`. -/
lemma E_p_bound_of_atom
    (exp : ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (duplexSpongeChallengeOracle StmtIn U))) (j : ℕ)
    (hself : Pr[ fun tr => permSelfCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j | exp]
      ≤ 1 / capPow (U := U))
    (hprior : ∀ j', j' < j → ∀ k : Fin 2,
      Pr[ fun tr => permOutCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j j' k | exp]
        ≤ 1 / capPow (U := U)) :
    Pr[ fun tr => E_p_at (tr.1 ++ tr.2) j | exp] ≤ (2 * (j : ℝ≥0∞) + 1) / capPow (U := U) := by
  have hpriorSum :
      Pr[ fun tr => ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
          permOutCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j p.1 p.2 | exp]
        ≤ (2 * (j : ℝ≥0∞)) / capPow (U := U) := by
    calc Pr[ fun tr => ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
            permOutCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j p.1 p.2 | exp]
        ≤ ∑ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
            Pr[ fun tr => permOutCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j p.1 p.2 | exp] :=
          probEvent_exists_finset_le_sum _ _ _
      _ ≤ ∑ _p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))), (1 / capPow (U := U)) :=
          Finset.sum_le_sum fun p hp =>
            hprior p.1 (Finset.mem_range.mp (Finset.mem_product.mp hp).1) p.2
      _ = (2 * (j : ℝ≥0∞)) / capPow (U := U) := by
          rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          simp only [one_div, div_eq_mul_inv]; push_cast; ring
  calc Pr[ fun tr => E_p_at (tr.1 ++ tr.2) j | exp]
      ≤ Pr[ fun tr => permSelfCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j ∨
            ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
              permOutCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j p.1 p.2 | exp] :=
        probEvent_mono fun tr _ h => E_p_at_imp_collision _ j h
    _ ≤ Pr[ fun tr => permSelfCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j | exp]
          + Pr[ fun tr => ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
              permOutCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j p.1 p.2 | exp] :=
        probEvent_or_le _ _ _
    _ ≤ 1 / capPow (U := U) + (2 * (j : ℝ≥0∞)) / capPow (U := U) := add_le_add hself hpriorSum
    _ = (2 * (j : ℝ≥0∞) + 1) / capPow (U := U) := by
        simp only [div_eq_mul_inv]; ring

/-- **Step A (real E_p atoms).** The fwd-perm output capacity at `j` is near-uniform in `Σ^c`
(random permutation), so it collides with any fixed earlier capacity, and with its own input
capacity, with probability `≤ 1/|Σ|^c`.  (Proof: permutation-freshness of `p`; the riskiest atom —
no VCVio lemma yet, needs a fresh-image bound on `Equiv.Perm`.) -/
lemma real_permOutCollision_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j j' : ℕ) (hj' : j' < j) (k : Fin 2) :
    Pr[ fun tr => permOutCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j j' k |
        lemma5_8RealTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) (D_𝔖 StmtIn U).sample ((D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ 1 / capPow (U := U) := by
  sorry

lemma real_permSelfCollision_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => permSelfCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j |
        lemma5_8RealTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) (D_𝔖 StmtIn U).sample ((D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ 1 / capPow (U := U) := by
  sorry

/-- Layer C, real `E_p`: `Pr[E_p_at · j] ≤ (2j+1)/|Σ|^c` (permutation freshness). -/
lemma lemma5_8_real_E_p_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_p_at (tr.1 ++ tr.2) j |
        lemma5_8RealTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) (D_𝔖 StmtIn U).sample ((D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞) + 1) / capPow (U := U) :=
  E_p_bound_of_atom _ j (real_permSelfCollision_le V maliciousProver j)
    fun j' hj' k => real_permOutCollision_le V maliciousProver j j' hj' k

/-! #### Step R — reduction of E_pinv (inverse-permutation range-capacity duplication)

Symmetric to E_p: `E_pinv_at·j` fires when the *range* (pre-image) capacity of the bwd-perm entry
at `j` duplicates a capacity — covered by ≤ 2j prior collisions plus one self collision (its own
domain capacity equals its range capacity — the `j' = j` case of the fifth disjunct). -/

/-- Range (pre-image) capacity of base position `j` if it is a bwd-permutation entry. -/
def permInvRangeCapAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option (Vector U SpongeSize.C) :=
  (bt[j]?).bind fun e => match e with
    | ⟨.inr (.inr _), sIn⟩ => some sIn.capacitySegment
    | _ => none

/-- Domain (queried) capacity of base position `j` if it is a bwd-permutation entry. -/
def permInvDomainCapAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) :
    Option (Vector U SpongeSize.C) :=
  (bt[j]?).bind fun e => match e with
    | ⟨.inr (.inr sOut), _⟩ => some sOut.capacitySegment
    | _ => none

/-- E_pinv prior-collision atom: bwd-perm range capacity at `j` matches the `k`-th capacity at `j'`. -/
def permInvCollisionAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (j j' : ℕ) (k : Fin 2) : Prop :=
  ∃ c, permInvRangeCapAt bt j = some c ∧ (bt[j']?).bind (fun e => entryCapAt e k) = some c

/-- E_pinv self-collision atom: the bwd-perm entry at `j` has equal domain and range capacities. -/
def permInvSelfCollisionAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) : Prop :=
  ∃ c, permInvRangeCapAt bt j = some c ∧ permInvDomainCapAt bt j = some c

/-- **Step R (E_pinv).** `E_pinv_at·j` is covered by the self collision or one of the `≤ 2j` prior
collisions. -/
lemma E_pinv_at_imp_collision
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) (h : E_pinv_at trace j) :
    permInvSelfCollisionAt (getBaseTrace trace) j ∨
      ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
        permInvCollisionAt (getBaseTrace trace) j p.1 p.2 := by
  classical
  obtain ⟨hj, capSeg, ⟨sOutj, sInj, hbtj, hcapj⟩, hdup⟩ := h
  have hout : permInvRangeCapAt (getBaseTrace trace) j = some capSeg := by
    simp only [permInvRangeCapAt, List.getElem?_eq_getElem hj, Option.bind_some, hbtj]
    exact congrArg some hcapj
  have mkP : ∀ (j' : Fin (getBaseTrace trace).length) (k : Fin 2), (j' : ℕ) < j →
      entryCapAt (getBaseTrace trace)[j'] k = some capSeg →
      permInvSelfCollisionAt (getBaseTrace trace) j ∨
        ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
          permInvCollisionAt (getBaseTrace trace) j p.1 p.2 := by
    intro j' k hlt hce
    refine Or.inr ⟨((j' : ℕ), k), by simp [Finset.mem_product, Finset.mem_range, hlt],
      capSeg, hout, ?_⟩
    rw [List.getElem?_eq_getElem j'.2]; exact hce
  rcases hdup with ⟨j', hlt, stmt', he⟩ | ⟨j', hlt, s1, s2, he, hc⟩ |
      ⟨j', hlt, s1, s2, he, hc⟩ | ⟨j', hlt, s1, s2, he, hc⟩ | ⟨j', hlt, s1, s2, he, hc⟩
  · exact mkP j' 0 (Fin.lt_def.mp hlt) (by rw [he]; rfl)
  · exact mkP j' 1 (Fin.lt_def.mp hlt) (by rw [he]; exact congrArg some hc)
  · exact mkP j' 1 (Fin.lt_def.mp hlt) (by rw [he]; exact congrArg some hc)
  · -- disjunct 4 (`j' ≤ j`): base[j'] is a fwd entry but base[j] is bwd ⇒ `j' < j`.
    have hlt' : (j' : ℕ) < j := by
      refine lt_of_le_of_ne (Fin.le_def.mp hlt) (fun heq => ?_)
      have hjj' : j' = (⟨j, hj⟩ : Fin (getBaseTrace trace).length) := Fin.ext heq
      rw [hjj', Fin.getElem_fin, hbtj] at he
      exact absurd he (by simp)
    exact mkP j' 0 hlt' (by rw [he]; exact congrArg some hc)
  · -- disjunct 5 (`j' ≤ j`): split `j' < j` (prior) vs `j' = j` (self).
    rcases lt_or_eq_of_le (Fin.le_def.mp hlt) with hlt' | heq
    · exact mkP j' 0 hlt' (by rw [he]; exact congrArg some hc)
    · have hjj' : j' = (⟨j, hj⟩ : Fin (getBaseTrace trace).length) := Fin.ext heq
      rw [hjj', Fin.getElem_fin, hbtj] at he
      obtain ⟨he1, _he2⟩ := Sigma.mk.inj_iff.mp he
      refine Or.inl ⟨capSeg, hout, ?_⟩
      simp only [permInvDomainCapAt, List.getElem?_eq_getElem hj, Option.bind_some, hbtj]
      have hs : sOutj = s1 := Sum.inr.inj (Sum.inr.inj he1)
      rw [hs]
      exact congrArg some hc

/-- **Generic E_pinv bound-from-atoms.** -/
lemma E_pinv_bound_of_atom
    (exp : ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (duplexSpongeChallengeOracle StmtIn U))) (j : ℕ)
    (hself : Pr[ fun tr => permInvSelfCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j | exp]
      ≤ 1 / capPow (U := U))
    (hprior : ∀ j', j' < j → ∀ k : Fin 2,
      Pr[ fun tr => permInvCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j j' k | exp]
        ≤ 1 / capPow (U := U)) :
    Pr[ fun tr => E_pinv_at (tr.1 ++ tr.2) j | exp] ≤ (2 * (j : ℝ≥0∞) + 1) / capPow (U := U) := by
  have hpriorSum :
      Pr[ fun tr => ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
          permInvCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j p.1 p.2 | exp]
        ≤ (2 * (j : ℝ≥0∞)) / capPow (U := U) := by
    calc Pr[ fun tr => ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
            permInvCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j p.1 p.2 | exp]
        ≤ ∑ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
            Pr[ fun tr => permInvCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j p.1 p.2 | exp] :=
          probEvent_exists_finset_le_sum _ _ _
      _ ≤ ∑ _p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))), (1 / capPow (U := U)) :=
          Finset.sum_le_sum fun p hp =>
            hprior p.1 (Finset.mem_range.mp (Finset.mem_product.mp hp).1) p.2
      _ = (2 * (j : ℝ≥0∞)) / capPow (U := U) := by
          rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          simp only [one_div, div_eq_mul_inv]; push_cast; ring
  calc Pr[ fun tr => E_pinv_at (tr.1 ++ tr.2) j | exp]
      ≤ Pr[ fun tr => permInvSelfCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j ∨
            ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
              permInvCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j p.1 p.2 | exp] :=
        probEvent_mono fun tr _ h => E_pinv_at_imp_collision _ j h
    _ ≤ Pr[ fun tr => permInvSelfCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j | exp]
          + Pr[ fun tr => ∃ p ∈ (Finset.range j ×ˢ (Finset.univ : Finset (Fin 2))),
              permInvCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j p.1 p.2 | exp] :=
        probEvent_or_le _ _ _
    _ ≤ 1 / capPow (U := U) + (2 * (j : ℝ≥0∞)) / capPow (U := U) := add_le_add hself hpriorSum
    _ = (2 * (j : ℝ≥0∞) + 1) / capPow (U := U) := by
        simp only [div_eq_mul_inv]; ring

/-- **Step A (real E_pinv atoms).** The bwd-perm range (pre-image) capacity at `j` is near-uniform
(`p⁻¹` on a fresh output), colliding with any fixed earlier capacity, and with its own domain
capacity, with probability `≤ 1/|Σ|^c`. -/
lemma real_permInvCollision_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j j' : ℕ) (hj' : j' < j) (k : Fin 2) :
    Pr[ fun tr => permInvCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j j' k |
        lemma5_8RealTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) (D_𝔖 StmtIn U).sample ((D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ 1 / capPow (U := U) := by
  sorry

lemma real_permInvSelfCollision_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => permInvSelfCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j |
        lemma5_8RealTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) (D_𝔖 StmtIn U).sample ((D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ 1 / capPow (U := U) := by
  sorry

/-- Layer C, real `E_p⁻¹`: `Pr[E_pinv_at · j] ≤ (2j+1)/|Σ|^c` (permutation freshness). -/
lemma lemma5_8_real_E_pinv_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_pinv_at (tr.1 ++ tr.2) j |
        lemma5_8RealTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) (D_𝔖 StmtIn U).sample ((D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞) + 1) / capPow (U := U) :=
  E_pinv_bound_of_atom _ j (real_permInvSelfCollision_le V maliciousProver j)
    fun j' hj' k => real_permInvCollision_le V maliciousProver j j' hj' k

/-- Layer C, real `E_func`: `Pr[E_func_at · j] ≤ j/|Σ|^c` — in fact `= 0` (`p` genuine function). -/
lemma lemma5_8_real_E_func_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_func_at (tr.1 ++ tr.2) j |
        lemma5_8RealTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
          (U := U) (δ := δ) (D_𝔖 StmtIn U).sample ((D_𝔖 StmtIn U).eagerImpl) V maliciousProver]
      ≤ (j : ℝ≥0∞) / capPow (U := U) := by
  -- The real permutation is a genuine function ⇒ `E_func` never fires ⇒ the probability is `0`.
  refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le')
  intro tr htr
  -- Destructure the experiment support and read off the sampled realization `s₀`.
  rw [lemma5_8RealTraceDist, lemma5_8ProjectedTraceDistAbortable, mem_support_bind_iff] at htr
  obtain ⟨s₀, _, htr⟩ := htr
  rw [mem_support_bind_iff] at htr
  obtain ⟨proverResult, hpr, htr⟩ := htr
  have hProver := realConsistent_of_mem_support (s₀, []) hpr
  obtain ⟨res, s₁, trP⟩ := proverResult
  have hProverCons : ∀ e ∈ trP, wideRealConsistent s₀ e := fun e he =>
    (hProver.2 e he).resolve_left (by simp)
  have htrP := projectTraceLog_realConsistent s₀ trP hProverCons
  rcases res with _ | ⟨stmtIn, proof⟩
  · -- Abort: `tr = (project trP, [])`.
    rw [mem_support_pure_iff] at htr
    subst htr
    refine E_func_at_false_of_consistent s₀ _ (fun e he => ?_) j
    have he2 := (getBaseTrace_sublist _).subset he
    rw [List.append_nil] at he2
    exact htrP e he2
  · -- Success: the verifier runs on the same carrier `s₁ = s₀`.
    rw [mem_support_bind_iff] at htr
    obtain ⟨verifierResult, hvr, htr⟩ := htr
    rw [mem_support_pure_iff] at htr
    subst htr
    have hs : s₁ = s₀ := hProver.1
    subst s₁
    have hVerifCons : ∀ e ∈ verifierResult.2.2, wideRealConsistent s₀ e := fun e he =>
      (realConsistent_of_mem_support (s₀, []) hvr |>.2 e he).resolve_left (by simp)
    have htrV := projectTraceLog_realConsistent s₀ verifierResult.2.2 hVerifCons
    refine E_func_at_false_of_consistent s₀ _ (fun e he => ?_) j
    rcases List.mem_append.mp ((getBaseTrace_sublist _).subset he) with h | h
    · exact htrP e h
    · exact htrV e h

/-- **Step A (sigma E_h atom).** Same per-pair hash-collision bound `≤ 1/|Σ|^c` on the simulator
experiment: `d2sQueryImpl` answers each *fresh* hash query with a uniform `Σ^c` sample (lazy
random oracle), so the `j`-th base hash answer is independent of the earlier `j' < j` capacity.
(Proof: VCVio cachingOracle freshness `probEvent_cacheCollision_le_birthday_total`.) -/
lemma sigma_hashCollision_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j j' : ℕ) (hj' : j' < j) (k : Fin 2) :
    Pr[ fun tr => hashCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j j' k |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ 1 / capPow (U := U) := by
  sorry

/-- Layer C, sigma `E_h`: `Pr[E_h_at · j] ≤ 2j/|Σ|^c`. -/
lemma lemma5_8_sigma_E_h_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_h_at (tr.1 ++ tr.2) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞)) / capPow (U := U) :=
  E_h_bound_of_atom _ j fun j' hj' k => sigma_hashCollision_le V maliciousProver j j' hj' k

/-- **Step A (sigma E_p atoms).** Same per-pair and self bounds on the simulator: `d2sQueryImpl`
answers a fresh permutation query with a uniform `Σ^{r+c}` sample, whose capacity segment is
uniform in `Σ^c` (`cachingOracle` freshness). -/
lemma sigma_permOutCollision_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j j' : ℕ) (hj' : j' < j) (k : Fin 2) :
    Pr[ fun tr => permOutCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j j' k |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ 1 / capPow (U := U) := by
  sorry

lemma sigma_permSelfCollision_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => permSelfCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ 1 / capPow (U := U) := by
  sorry

/-- Layer C, sigma `E_p`: `Pr[E_p_at · j] ≤ (2j+1)/|Σ|^c`. -/
lemma lemma5_8_sigma_E_p_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_p_at (tr.1 ++ tr.2) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞) + 1) / capPow (U := U) :=
  E_p_bound_of_atom _ j (sigma_permSelfCollision_le V maliciousProver j)
    fun j' hj' k => sigma_permOutCollision_le V maliciousProver j j' hj' k

/-- **Step A (sigma E_pinv atoms).** Simulator analogue of the bwd-perm collision bounds. -/
lemma sigma_permInvCollision_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j j' : ℕ) (hj' : j' < j) (k : Fin 2) :
    Pr[ fun tr => permInvCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j j' k |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ 1 / capPow (U := U) := by
  sorry

lemma sigma_permInvSelfCollision_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => permInvSelfCollisionAt (getBaseTrace (tr.1 ++ tr.2)) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ 1 / capPow (U := U) := by
  sorry

/-- Layer C, sigma `E_p⁻¹`: `Pr[E_pinv_at · j] ≤ (2j+1)/|Σ|^c`. -/
lemma lemma5_8_sigma_E_pinv_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_pinv_at (tr.1 ++ tr.2) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ (2 * (j : ℝ≥0∞) + 1) / capPow (U := U) :=
  E_pinv_bound_of_atom _ j (sigma_permInvSelfCollision_le V maliciousProver j)
    fun j' hj' k => sigma_permInvCollision_le V maliciousProver j j' hj' k

/-! #### Step R — reduction of E_func (function-violation, simulator side)

`E_func_at·j` fires when the permutation entry at `j` conflicts with an *earlier* entry `j' < j`
sharing a domain/pre-image but disagreeing on the value.  This is covered by the `≤ j` pairwise
function conflicts, giving the `j/|Σ|^c` count.  (On the real side `E_func` is impossible —
`lemma5_8_real_E_func_at` — because `p` is a genuine bijection.) -/

/-- The function-conflict of base positions `j` and `j'`: `j` is a permutation entry, and `j'`
shares its domain/pre-image but disagrees on the mapped value. -/
def funcConflictAt (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j j' : ℕ) : Prop :=
  ∃ stateIn stateOut : CanonicalSpongeState U,
    (bt[j]? = some ⟨.inr (.inl stateIn), stateOut⟩ ∧
      ((∃ sO1, bt[j']? = some ⟨.inr (.inl stateIn), sO1⟩ ∧ sO1 ≠ stateOut) ∨
       (∃ sO2, bt[j']? = some ⟨.inr (.inr sO2), stateIn⟩ ∧ sO2 ≠ stateOut))) ∨
    (bt[j]? = some ⟨.inr (.inr stateOut), stateIn⟩ ∧
      ((∃ sI1, bt[j']? = some ⟨.inr (.inr stateOut), sI1⟩ ∧ sI1 ≠ stateIn) ∨
       (∃ sI2, bt[j']? = some ⟨.inr (.inl sI2), stateOut⟩ ∧ sI2 ≠ stateIn)))

/-- **Step R (E_func).** `E_func_at·j` is covered by one of the `≤ j` pairwise function conflicts. -/
lemma E_func_at_imp_funcConflict
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ) (h : E_func_at trace j) :
    ∃ j' ∈ Finset.range j, funcConflictAt (getBaseTrace trace) j j' := by
  classical
  obtain ⟨hj, sIn, sOut, hbody⟩ := h
  rcases hbody with ⟨hbtj, j', hlt, hconf⟩ | ⟨hbtj, j', hlt, hconf⟩
  · refine ⟨(j' : ℕ), Finset.mem_range.mpr (Fin.lt_def.mp hlt), sIn, sOut, Or.inl ⟨?_, ?_⟩⟩
    · rw [List.getElem?_eq_getElem hj]; exact congrArg some hbtj
    · rcases hconf with ⟨sO1, he, hne⟩ | ⟨sO2, he, hne⟩
      · exact Or.inl ⟨sO1, by rw [List.getElem?_eq_getElem j'.2]; exact congrArg some he, hne⟩
      · exact Or.inr ⟨sO2, by rw [List.getElem?_eq_getElem j'.2]; exact congrArg some he, hne⟩
  · refine ⟨(j' : ℕ), Finset.mem_range.mpr (Fin.lt_def.mp hlt), sIn, sOut, Or.inr ⟨?_, ?_⟩⟩
    · rw [List.getElem?_eq_getElem hj]; exact congrArg some hbtj
    · rcases hconf with ⟨sI1, he, hne⟩ | ⟨sI2, he, hne⟩
      · exact Or.inl ⟨sI1, by rw [List.getElem?_eq_getElem j'.2]; exact congrArg some he, hne⟩
      · exact Or.inr ⟨sI2, by rw [List.getElem?_eq_getElem j'.2]; exact congrArg some he, hne⟩

/-- **Step A (sigma E_func atom).** On the simulator, a fresh permutation query creates a function
conflict with a fixed earlier entry with probability `≤ 1/|Σ|^c` (CO25 Eq. 33): the two
sub-conflicts (fwd-vs-fwd, fwd-vs-bwd) each require the fresh uniform `Σ^{r+c}` value to hit one
prior state, so each is `≤ 1/|Σ|^{r+c}`; their union is `≤ 2/|Σ|^{r+c} ≤ 1/|Σ|^c` since
`|Σ^r| ≥ 2`.  (Proof: `d2sQueryImpl` cache freshness; the paper's `|Cache_p ∩ tr|` count.) -/
lemma sigma_funcConflict_le
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j j' : ℕ) (hj' : j' < j) :
    Pr[ fun tr => funcConflictAt (getBaseTrace (tr.1 ++ tr.2)) j j' |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ 1 / capPow (U := U) := by
  sorry

/-- Layer C, sigma `E_func`: `Pr[E_func_at · j] ≤ j/|Σ|^c` (`Cache_p ∩ tr` count). -/
lemma lemma5_8_sigma_E_func_at
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) (j : ℕ) :
    Pr[ fun tr => E_func_at (tr.1 ++ tr.2) j |
        lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
          (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver]
      ≤ (j : ℝ≥0∞) / capPow (U := U) := by
  set exp := lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
    (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver
  calc Pr[ fun tr => E_func_at (tr.1 ++ tr.2) j | exp]
      ≤ Pr[ fun tr => ∃ j' ∈ Finset.range j,
            funcConflictAt (getBaseTrace (tr.1 ++ tr.2)) j j' | exp] :=
        probEvent_mono fun tr _ h => E_func_at_imp_funcConflict _ j h
    _ ≤ ∑ j' ∈ Finset.range j,
          Pr[ fun tr => funcConflictAt (getBaseTrace (tr.1 ++ tr.2)) j j' | exp] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _j' ∈ Finset.range j, (1 / capPow (U := U)) :=
        Finset.sum_le_sum fun j' hj' =>
          sigma_funcConflict_le V maliciousProver j j' (Finset.mem_range.mp hj')
    _ = (j : ℝ≥0∞) / capPow (U := U) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div]

set_option linter.unusedDecidableInType false in
/-- CO25 Lemma 5.8 — Bad-event probability bound (paper-faithful eager statement), assembled from
the Layer-B/D/E spine (`probEvent_E_le_lemma5_8Bound`, fully proven) and the Layer-A/C
per-side obligations above. -/
theorem lemma_5_8
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hδR : δ ≤ SpongeSize.R)
    (hMaliciousBound : IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) maliciousProver tₕ tₚ tₚᵢ)
    (hTp : tₚ ≥ pSpec.totalNumPermQueries) :
    max
        (Pr[ fun (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
                      QueryLog (duplexSpongeChallengeOracle StmtIn U)) =>
              E (tr.1 ++ tr.2) |
          lemma5_8RealTraceDist
            (StmtIn := StmtIn) (StmtOut := StmtOut)
            (n := n) (pSpec := pSpec) (U := U) (δ := δ)
            (D_𝔖 StmtIn U).sample ((D_𝔖 StmtIn U).eagerImpl) V maliciousProver])
        (Pr[ fun (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
                      QueryLog (duplexSpongeChallengeOracle StmtIn U)) =>
              E (tr.1 ++ tr.2) |
          lemma5_8SigmaTraceDist
            (T_H := T_H) (T_P := T_P) (δ := δ)
            (StmtIn := StmtIn) (StmtOut := StmtOut)
            (n := n) (pSpec := pSpec) (U := U) V maliciousProver])
      ≤ ENNReal.ofReal (lemma5_8Bound U tₕ tₚ tₚᵢ pSpec.totalNumPermQueries) := by
  refine max_le ?_ ?_
  · exact probEvent_E_le_lemma5_8Bound
      (lemma5_8RealTraceDist (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
        (U := U) (δ := δ) (D_𝔖 StmtIn U).sample ((D_𝔖 StmtIn U).eagerImpl) V maliciousProver)
      (fun tr => tr.1 ++ tr.2) tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
      (lemma5_8_real_length V maliciousProver tₕ tₚ tₚᵢ hδR hMaliciousBound hTp)
      (lemma5_8_real_E_h_at V maliciousProver)
      (lemma5_8_real_E_p_at V maliciousProver)
      (lemma5_8_real_E_pinv_at V maliciousProver)
      (lemma5_8_real_E_func_at V maliciousProver)
  · exact probEvent_E_le_lemma5_8Bound
      (lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn)
        (StmtOut := StmtOut) (n := n) (pSpec := pSpec) (U := U) V maliciousProver)
      (fun tr => tr.1 ++ tr.2) tₕ tₚ tₚᵢ pSpec.totalNumPermQueries
      (lemma5_8_sigma_length V maliciousProver tₕ tₚ tₚᵢ hδR hMaliciousBound hTp)
      (lemma5_8_sigma_E_h_at V maliciousProver)
      (lemma5_8_sigma_E_p_at V maliciousProver)
      (lemma5_8_sigma_E_pinv_at V maliciousProver)
      (lemma5_8_sigma_E_func_at V maliciousProver)

end BadEventDS

end DuplexSpongeFS
