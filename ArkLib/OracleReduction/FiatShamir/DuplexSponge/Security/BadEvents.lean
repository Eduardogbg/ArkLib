/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform

set_option linter.style.longFile 1800

/-!
# Definition and analysis of bad events

This file contains the definition and analysis of bad events for the analysis of duplex sponge
Fiat-Shamir, following Section 5.6 in the paper.

## Predicate organization

The bad-event surface mirrors the paper definitions directly:

- **Trace-only events (Def 5.7):** `E_h` / `E_p` / `E_pinv` / `E_dup` / `E_func` / `E`.
- **Collision family (Def 5.9):** `collisionFwdFwd` / `collisionBwdBwd` / `collisionFwdBwd` /
  `collisionBwdFwd` / `collisionPerm`, with paper aliases `E_col_p` / `E_col_pinv` /
  `E_col_p_pinv` / `E_col_pinv_p` / `E_prp`.
- **BackTrack-family events (Defs 5.11, 5.13, 5.15):** `E_inv`, `E_fork` (with subcases
  `E_fork_h`, `E_fork_p`, `E_fork_h_p`), and `E_time` (with subcases `E_time_h`, `E_time_p`).
  These take `(S_BT : Backtrack.S_BT trace state)` as an explicit parameter and quantify over
  the family `S_BT.seqFamily` and the index-list family `Backtrack.J_BT S_BT` (CO25 Defs 5.3 &
  5.4).

Lemmas `lemma_5_12` / `lemma_5_14` / `lemma_5_16` are the paper-faithful "if `E(tr) = 0` then
the BackTrack-family event vanishes" statements.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

/-! ## Definition 5.5 and Definition 5.6 - Redundant entries in a trace -/
section Def_5_5_6_RedundantEntryDSHelpers

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-- **Definition 5.5**: Redundancy test for a new entry against a prefix of the trace -/
def isRedundantEntryOfPrefix
    (pref : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  match entry with
  | ⟨.inl stmt, capSeg⟩ =>
      ⟨.inl stmt, capSeg⟩ ∈ pref
  | ⟨.inr (.inl stateIn), stateOut⟩ =>
      ⟨.inr (.inl stateIn), stateOut⟩ ∈ pref
      ∨ ⟨.inr (.inr stateOut), stateIn⟩ ∈ pref
  | ⟨.inr (.inr stateOut), stateIn⟩ =>
      ⟨.inr (.inr stateOut), stateIn⟩ ∈ pref
      ∨ ⟨.inr (.inl stateIn), stateOut⟩ ∈ pref

/-- CO25 Definition 5.6 — Base trace `tr̄` side condition.
`hasNoRedundantEntries log` holds iff no entry of `log` is redundant in the sense of
Definition 5.5.  The base trace `tr̄` is the unique sub-log satisfying this predicate
(see `getBaseTrace`). -/
def hasNoRedundantEntries (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ i : ℕ, ∀ hi : i < log.length,
    ¬ isRedundantEntryOfPrefix (log.take i) log[i]

private lemma noRedundantEntryDS_nil : hasNoRedundantEntries (StmtIn := StmtIn) (U := U) [] := by
  intro i hi _
  exact (Nat.not_lt_zero i) hi

private lemma noRedundantEntryDS_append_singleton
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U))
    (hAcc : hasNoRedundantEntries acc)
    (hEntry : ¬ isRedundantEntryOfPrefix acc entry) :
    hasNoRedundantEntries (acc ++ [entry]) := by
  intro i hi
  have hi' : i < acc.length + 1 := by
    rw [List.length_append, List.length_singleton] at hi
    exact hi
  by_cases hlt : i < acc.length
  · have hOld :
      ¬ isRedundantEntryOfPrefix (acc.take i) acc[i] := hAcc i hlt
    simp only [List.take_append_of_le_length (Nat.le_of_lt hlt), List.getElem_append_left hlt]
    exact hOld
  · have hEq : i = acc.length := Nat.eq_of_lt_succ_of_not_lt hi' hlt
    subst hEq
    revert hEntry
    simp [isRedundantEntryOfPrefix]

noncomputable def getBaseTraceAux
    (remaining : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) := by
  classical
  exact match remaining with
  | [] => acc
  | entry :: rest =>
      if hRed : isRedundantEntryOfPrefix acc entry then
        getBaseTraceAux rest acc
      else
        getBaseTraceAux rest (acc ++ [entry])

private lemma getBaseTraceAux_noRedundant
    (remaining : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (acc : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hAcc : hasNoRedundantEntries acc) :
    hasNoRedundantEntries (getBaseTraceAux remaining acc) := by
  classical
  induction remaining generalizing acc with
  | nil => exact hAcc
  | cons entry rest ih =>
      by_cases hRed : isRedundantEntryOfPrefix acc entry
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih acc hAcc
      · let hAcc' := noRedundantEntryDS_append_singleton acc entry hAcc hRed
        simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih (acc ++ [entry]) hAcc'

/-- CO25 Definition 5.6 — Compute the base trace `tr̄` of a duplex-sponge query-answer trace by
removing all redundant entries (in the sense of Definition 5.5). -/
noncomputable def getBaseTrace
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  getBaseTraceAux log []

lemma getBaseTrace_noRedundant
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    hasNoRedundantEntries (getBaseTrace log) :=
  getBaseTraceAux_noRedundant log [] (noRedundantEntryDS_nil (StmtIn := StmtIn) (U := U))

/-! ### Structural lemmas about `getBaseTrace` (membership / order bridge)

These connect the *external* `trace` (where backtrack sequences live) to its base trace `tr̄`
(`getBaseTrace`, where the bad events `E_dup`/`E_func` are evaluated).  They are used by the
toolbox lemmas (B1)/(B2) and Lemmas 5.12/5.14/5.16. -/

/-- Redundancy is monotone in the prefix: enlarging the prefix can only make an entry *more*
redundant. -/
private lemma isRedundantEntryOfPrefix_mono
    {acc acc' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {entry : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hsub : acc ⊆ acc')
    (h : isRedundantEntryOfPrefix acc entry) : isRedundantEntryOfPrefix acc' entry := by
  obtain ⟨q, r⟩ := entry
  match q with
  | .inl stmt =>
      exact hsub h
  | .inr (.inl stateIn) =>
      rcases h with h | h
      · exact Or.inl (hsub h)
      · exact Or.inr (hsub h)
  | .inr (.inr stateOut) =>
      rcases h with h | h
      · exact Or.inl (hsub h)
      · exact Or.inr (hsub h)

/-- Entries already in the accumulator survive `getBaseTraceAux`. -/
private lemma mem_getBaseTraceAux_of_mem_acc
    (remaining acc : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {e : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (he : e ∈ acc) : e ∈ getBaseTraceAux remaining acc := by
  classical
  induction remaining generalizing acc with
  | nil => simpa [getBaseTraceAux] using he
  | cons entry rest ih =>
      by_cases hRed : isRedundantEntryOfPrefix acc entry
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih acc he
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih (acc ++ [entry]) (List.mem_append_left _ he)

/-- `getBaseTraceAux` is a fold: processing `l₁ ++ l₂` is processing `l₂` after `l₁`. -/
private lemma getBaseTraceAux_append
    (l₁ l₂ acc : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    getBaseTraceAux (l₁ ++ l₂) acc = getBaseTraceAux l₂ (getBaseTraceAux l₁ acc) := by
  classical
  induction l₁ generalizing acc with
  | nil => simp [getBaseTraceAux]
  | cons entry rest ih =>
      by_cases hRed : isRedundantEntryOfPrefix acc entry
      · simp only [List.cons_append, getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih acc
      · simp only [List.cons_append, getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih (acc ++ [entry])

/-- `getBaseTraceAux remaining acc` is a sublist of `acc ++ remaining`. -/
private lemma getBaseTraceAux_sublist
    (remaining acc : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    (getBaseTraceAux remaining acc).Sublist (acc ++ remaining) := by
  classical
  induction remaining generalizing acc with
  | nil => simp [getBaseTraceAux]
  | cons entry rest ih =>
      by_cases hRed : isRedundantEntryOfPrefix acc entry
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        have h1 : (getBaseTraceAux rest acc).Sublist (acc ++ rest) := ih acc
        refine h1.trans ?_
        exact List.Sublist.append_left (List.sublist_cons_self entry rest) acc
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        have h1 : (getBaseTraceAux rest (acc ++ [entry])).Sublist ((acc ++ [entry]) ++ rest) :=
          ih (acc ++ [entry])
        simpa using h1

/-- `getBaseTrace` is a sublist of the original trace. -/
lemma getBaseTrace_sublist
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    (getBaseTrace log).Sublist log := by
  have := getBaseTraceAux_sublist log ([] : QueryLog (duplexSpongeChallengeOracle StmtIn U))
  simpa [getBaseTrace] using this

/-- Bridge: if the entry at position `k` of `trace` is not redundant relative to the literal
prefix `trace.take k`, then it survives into `getBaseTrace trace`. -/
private lemma mem_getBaseTrace_of_not_redundant_take
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (k : ℕ) (hk : k < trace.length)
    (hnr : ¬ isRedundantEntryOfPrefix (trace.take k) (trace.get ⟨k, hk⟩)) :
    (trace.get ⟨k, hk⟩) ∈ getBaseTrace trace := by
  classical
  set e := trace.get ⟨k, hk⟩ with he
  -- Split the fold at position `k`.
  have key : getBaseTraceAux (trace.drop k) (getBaseTrace (trace.take k))
           = getBaseTrace trace := by
    rw [getBaseTrace, getBaseTrace, ← getBaseTraceAux_append, List.take_append_drop]
  -- `e` is not redundant relative to the (smaller) filtered prefix.
  have hsub : getBaseTrace (trace.take k) ⊆ trace.take k :=
    (getBaseTrace_sublist (trace.take k)).subset
  have hnr' : ¬ isRedundantEntryOfPrefix (getBaseTrace (trace.take k)) e := by
    intro hc
    exact hnr (isRedundantEntryOfPrefix_mono hsub hc)
  -- Unfold one step of the fold: `e` is appended and then persists.
  have hdrop : trace.drop k = e :: trace.drop (k + 1) := by
    rw [he, List.get_eq_getElem]; exact List.drop_eq_getElem_cons hk
  rw [← key, hdrop]
  simp only [getBaseTraceAux, hnr', ↓reduceDIte]
  exact mem_getBaseTraceAux_of_mem_acc _ _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

/-- `getElem?` form of `mem_getBaseTrace_of_not_redundant_take`. -/
private lemma mem_getBaseTrace_of_getElem?_not_redundant
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {k : ℕ} {e : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hget : (trace)[k]? = some e)
    (hnr : ¬ isRedundantEntryOfPrefix (trace.take k) e) :
    e ∈ getBaseTrace trace := by
  rw [List.getElem?_eq_some_iff] at hget
  obtain ⟨hk, hek⟩ := hget
  have hmem := mem_getBaseTrace_of_not_redundant_take trace k hk
    (by rw [List.get_eq_getElem, hek]; exact hnr)
  rwa [List.get_eq_getElem, hek] at hmem

/-- A forward-permutation entry indexed by a `getElem?` whose two query forms do not occur earlier
survives into `getBaseTrace`. -/
private lemma permFwd_mem_getBaseTrace
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {sIn sOut : CanonicalSpongeState U} {k : ℕ}
    (hget : (trace)[k]? = some ⟨.inr (.inl sIn), sOut⟩)
    (hnrA : (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∉ trace.take k)
    (hnrB : (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∉ trace.take k) :
    (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∈ getBaseTrace trace := by
  refine mem_getBaseTrace_of_getElem?_not_redundant trace hget ?_
  intro hred
  simp only [isRedundantEntryOfPrefix] at hred
  rcases hred with h | h
  · exact hnrA h
  · exact hnrB h

/-- An inverse-permutation entry indexed by a `getElem?` whose two query forms do not occur earlier
survives into `getBaseTrace`. -/
private lemma permInv_mem_getBaseTrace
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {sOut sIn : CanonicalSpongeState U} {k : ℕ}
    (hget : (trace)[k]? = some ⟨.inr (.inr sOut), sIn⟩)
    (hnrB : (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∉ trace.take k)
    (hnrA : (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∉ trace.take k) :
    (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        ∈ getBaseTrace trace := by
  refine mem_getBaseTrace_of_getElem?_not_redundant trace hget ?_
  intro hred
  simp only [isRedundantEntryOfPrefix] at hred
  rcases hred with h | h
  · exact hnrB h
  · exact hnrA h

/-- The accumulator is a prefix of `getBaseTraceAux` (entries are only ever appended). -/
private lemma getBaseTraceAux_prefix
    (remaining acc : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    acc <+: getBaseTraceAux remaining acc := by
  classical
  induction remaining generalizing acc with
  | nil => simp [getBaseTraceAux]
  | cons entry rest ih =>
      by_cases hRed : isRedundantEntryOfPrefix acc entry
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact ih acc
      · simp only [getBaseTraceAux, hRed, ↓reduceDIte]
        exact (List.prefix_append acc [entry]).trans (ih (acc ++ [entry]))

/-- `getBaseTrace` of a shorter prefix is a prefix of `getBaseTrace` of a longer prefix. -/
private lemma getBaseTrace_take_prefix
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) {a b : ℕ} (hab : a ≤ b) :
    getBaseTrace (trace.take a) <+: getBaseTrace (trace.take b) := by
  classical
  have hsplit : trace.take b = trace.take a ++ (trace.take b).drop a := by
    conv_lhs => rw [← List.take_append_drop a (trace.take b)]
    rw [List.take_take, Nat.min_eq_left hab]
  calc getBaseTrace (trace.take a)
      <+: getBaseTraceAux ((trace.take b).drop a) (getBaseTrace (trace.take a)) :=
        getBaseTraceAux_prefix _ _
    _ = getBaseTrace (trace.take b) := by
        unfold getBaseTrace
        rw [← getBaseTraceAux_append, ← hsplit]

/-- Length of `getBaseTrace` is monotone in the prefix length. -/
private lemma getBaseTrace_take_length_mono
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) {a b : ℕ} (hab : a ≤ b) :
    (getBaseTrace (trace.take a)).length ≤ (getBaseTrace (trace.take b)).length :=
  (getBaseTrace_take_prefix trace hab).length_le

/-- The base index of a non-redundant trace position `k` is `|getBaseTrace (trace.take k)|`, and the
base trace there carries that entry.  This is the order-preserving "first occurrence ↦ base index"
map used for Lemma 5.16. -/
private lemma baseIdx_of_getElem?_not_redundant
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {k : ℕ} {e : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hget : (trace)[k]? = some e)
    (hnr : ¬ isRedundantEntryOfPrefix (trace.take k) e) :
    ∃ hb : (getBaseTrace (trace.take k)).length < (getBaseTrace trace).length,
      (getBaseTrace trace)[(getBaseTrace (trace.take k)).length]'hb = e := by
  classical
  rw [List.getElem?_eq_some_iff] at hget
  obtain ⟨hk, hek⟩ := hget
  -- Decompose the fold and unfold one step at position `k`.
  have key : getBaseTraceAux (trace.drop k) (getBaseTrace (trace.take k)) = getBaseTrace trace := by
    rw [getBaseTrace, getBaseTrace, ← getBaseTraceAux_append, List.take_append_drop]
  have hsub : getBaseTrace (trace.take k) ⊆ trace.take k :=
    (getBaseTrace_sublist (trace.take k)).subset
  have hnr' : ¬ isRedundantEntryOfPrefix (getBaseTrace (trace.take k)) e :=
    fun hc => hnr (isRedundantEntryOfPrefix_mono hsub hc)
  have hdrop : trace.drop k = e :: trace.drop (k + 1) := by
    rw [← hek]; exact List.drop_eq_getElem_cons hk
  have hstep : getBaseTrace trace
      = getBaseTraceAux (trace.drop (k + 1)) (getBaseTrace (trace.take k) ++ [e]) := by
    rw [← key, hdrop]; simp only [getBaseTraceAux, hnr', ↓reduceDIte]
  have hpre : (getBaseTrace (trace.take k) ++ [e]) <+: getBaseTrace trace := by
    rw [hstep]; exact getBaseTraceAux_prefix _ _
  have hlen : (getBaseTrace (trace.take k)).length
      < (getBaseTrace (trace.take k) ++ [e]).length := by simp
  refine ⟨lt_of_lt_of_le hlen hpre.length_le, ?_⟩
  set b := (getBaseTrace (trace.take k)).length with hbdef
  have h2 : (getBaseTrace (trace.take k) ++ [e])[b]'hlen = e := by simp [hbdef]
  exact (hpre.getElem hlen).symm.trans h2

/-- A hash entry indexed by a `getElem?` not occurring earlier survives into `getBaseTrace`. -/
private lemma hash_mem_getBaseTrace
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {cap : Vector U SpongeSize.C} {k : ℕ}
    (hget : (trace)[k]? = some ⟨.inl stmt, cap⟩)
    (hnr : (⟨.inl stmt, cap⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∉ trace.take k) :
    (⟨.inl stmt, cap⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace := by
  refine mem_getBaseTrace_of_getElem?_not_redundant trace hget ?_
  intro hred
  simp only [isRedundantEntryOfPrefix] at hred
  exact hnr hred

end Def_5_5_6_RedundantEntryDSHelpers

/-! ## Bad-event-related predicates and lemmas (Definition 5.7 -> Lemma 5.16) -/
namespace BadEventDS
open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

variable (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (state : CanonicalSpongeState U)

/-! ## Definition 5.7 — trace-only bad events (`E_h`, `E_p`, `E_{p⁻¹}`, `E_dup`, `E_func`, `E`) -/

section Def57_TraceOnlyBadEvents

/-! The main bad event `E` (Def 5.7) is the disjunction of two conditions: a capacity-segment
duplication on the base trace (`E_dup`), or `p` behaving non-functionally (`E_func`). -/

/- NOTE: the paper write `∃ j > 0`, which can be confusing since we don't know whether the intended
indexing is from 0 or from 1. We assume they mean from 1, and since indexing here is from 0, we just
write `∃ j`. -/

/-- A unified check for whether a capacity segment `capSeg` has appeared previously as an
output capacity (strictly before `j`) or as an input capacity (up to and including `j`).
This exactly captures the redundancy conditions in `E_h`, `E_p`, and `E_{p⁻¹}`. -/
def isDuplicatedPriorCapacity (baseTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (j : Fin baseTrace.length) (capSeg : Vector U SpongeSize.C) : Prop :=
  (∃ j' < j, ∃ stmt', baseTrace[j'] = ⟨.inl stmt', capSeg⟩) ∨
  (∃ j' < j, ∃ stateIn1 stateOut1, baseTrace[j'] = ⟨.inr <|.inl stateIn1, stateOut1⟩ ∧
    stateOut1.capacitySegment = capSeg) ∨
  (∃ j' < j, ∃ stateOut2 stateIn2, baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn2⟩ ∧
    stateIn2.capacitySegment = capSeg) ∨
  (∃ j' ≤ j, ∃ stateIn3 stateOut3, baseTrace[j'] = ⟨.inr <|.inl stateIn3, stateOut3⟩ ∧
    stateIn3.capacitySegment = capSeg) ∨
  (∃ j' ≤ j, ∃ stateOut4 stateIn4, baseTrace[j'] = ⟨.inr <|.inr stateOut4, stateIn4⟩ ∧
    stateOut4.capacitySegment = capSeg)

/-- CO25 Definition 5.7 — Event `E_h(tr)` (Eq. 23).
An output capacity segment `s_C` of an `h`-entry in the base trace `tr̄` previously appears
as an output or input capacity segment of `h`, `p`, or `p⁻¹`:

```
E_h(tr) := ∃ j > 0, s_C ∈ Σ^c :  tr̄_j = (h, ·, s_C)  and  ∃ j' < j :
  tr̄_{j'} = (h, ·, s_C)  ∨  tr̄_{j'} = (p, ·, (·, s_C))  ∨  tr̄_{j'} = (p⁻¹, ·, (·, s_C))
  ∨  tr̄_{j'} = (p, (·, s_C), ·)  ∨  tr̄_{j'} = (p⁻¹, (·, s_C), ·)
```

All five prior-entry branches are unified via `isDuplicatedPriorCapacity`. -/
def capacitySegmentDupHash : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stmt : StmtIn, baseTrace[j] = ⟨.inl stmt, capSeg⟩) ∧
    isDuplicatedPriorCapacity baseTrace j capSeg

alias E_h := capacitySegmentDupHash

/-- CO25 Definition 5.7 — Event `E_p(tr)` (Eq. 24).
An output capacity segment `s_C` of a `p`-entry in the base trace `tr̄` previously (or
simultaneously for some branches) appears as an output or input capacity segment of `h`, `p`,
or `p⁻¹`:

```
E_p(tr) := ∃ j > 0, s_C ∈ Σ^c :  tr̄_j = (p, ·, (·, s_C))  and
  ∃ j' < j : tr̄_{j'} = (h, ·, s_C)  ∨  ∃ j' < j : tr̄_{j'} = (p, ·, (·, s_C))
  ∨  ∃ j' < j : tr̄_{j'} = (p⁻¹, ·, (·, s_C))
  ∨  ∃ j' ≤ j : tr̄_{j'} = (p, (·, s_C), ·)  ∨  ∃ j' < j : tr̄_{j'} = (p⁻¹, (·, s_C), ·)
```

Branches realized by `isDuplicatedPriorCapacity`'s uniform `≤ j`; extensionally equal to the
paper's asymmetric `< j`/`≤ j` (the extra `j' = j` cases are vacuous). -/
def capacitySegmentDupPerm : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateIn stateOut, baseTrace[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      stateOut.capacitySegment = capSeg) ∧
    isDuplicatedPriorCapacity baseTrace j capSeg

alias E_p := capacitySegmentDupPerm

/-- CO25 Definition 5.7 — Event `E_{p⁻¹}(tr)` (Eq. 25).
An output capacity segment `s_C` (i.e. the output of `p⁻¹`, which is the input side `s_in`) of a
`p⁻¹`-entry in the base trace `tr̄` previously (or simultaneously for some branches) appears as
an output or input capacity segment of `h`, `p`, or `p⁻¹`:

```
E_{p⁻¹}(tr) := ∃ j > 0, s_C ∈ Σ^c :  tr̄_j = (p⁻¹, ·, (·, s_C))  and
  ∃ j' < j : tr̄_{j'} = (h, ·, s_C)  ∨  ∃ j' < j : tr̄_{j'} = (p, ·, (·, s_C))
  ∨  ∃ j' < j : tr̄_{j'} = (p⁻¹, ·, (·, s_C))
  ∨  ∃ j' ≤ j : tr̄_{j'} = (p, (·, s_C), ·)  ∨  ∃ j' ≤ j : tr̄_{j'} = (p⁻¹, (·, s_C), ·)
```

Same uniform-`≤ j` caveat as `E_p` (via `isDuplicatedPriorCapacity`); extensionally equal to
Eq. 25's asymmetric quantifiers. -/
def capacitySegmentDupPermInv : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ capSeg : Vector U SpongeSize.C,
    (∃ stateOut stateIn, baseTrace[j] = ⟨.inr <|.inr stateOut, stateIn⟩ ∧
      stateIn.capacitySegment = capSeg) ∧
    isDuplicatedPriorCapacity baseTrace j capSeg

alias E_pinv := capacitySegmentDupPermInv

/-- CO25 Definition 5.7 — Combined capacity-segment duplication event `E_dup(tr)`.
Holds iff at least one of `E_h(tr)`, `E_p(tr)`, or `E_{p⁻¹}(tr)` holds: there exists an output
capacity segment in the base trace `tr̄` that previously appeared as an output or input capacity
segment. -/
def capacitySegmentDup : Prop :=
  capacitySegmentDupHash trace ∨ capacitySegmentDupPerm trace ∨ capacitySegmentDupPermInv trace

alias E_dup := capacitySegmentDup

/-- CO25 Definition 5.7 — Event `E_func(tr)` (Eq. 26).
**The same query to `p` leads to different answers**, or there are inconsistent queries across `p`
and `p⁻¹`:

```
E_func(tr) := ∃ j > 0 :
  [Case 1] tr̄_j = (p, s_in, s_out)  and  ∃ j' < j :
    (tr̄_{j'} = (p, s_in, s_out') ∧ s_out' ≠ s_out)  ∨  (tr̄_{j'} = (p⁻¹, s_out', s_in) ∧ s_out' ≠ s_out)
  or
  [Case 2] tr̄_j = (p⁻¹, s_out, s_in)  and  ∃ j' < j :
    (tr̄_{j'} = (p⁻¹, s_out, s_in') ∧ s_in' ≠ s_in)  ∨  (tr̄_{j'} = (p, s_in', s_out) ∧ s_in' ≠ s_in)
```

Note: `E_func(tr)` never holds for a true permutation `p` and its inverse `p⁻¹`, but may hold
(with small probability) for the D2SQuery simulator.

**Strengthening:** bidirectional. Case 1 (`j`-th entry `p`-forward) is Eq. 26; Case 2 (`j`-th entry
`p⁻¹`) has no paper counterpart but is *required* by `not_collisionFwdBwd_of_not_combined`
(Lemma 5.10, Item 3). The `≠`-output conditions are forced by base-trace non-redundancy.
See `DSFS-archive/BadEvents_deep_analysis.md` §7. -/
def E_func : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ j : Fin baseTrace.length, ∃ stateIn stateOut : CanonicalSpongeState U,
    (baseTrace[j] = ⟨.inr <|.inl stateIn, stateOut⟩ ∧
      ∃ j' < j,
        (∃ stateOut1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inl stateIn, stateOut1⟩ ∧ stateOut1 ≠ stateOut) ∨
        (∃ stateOut2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inr stateOut2, stateIn⟩ ∧ stateOut2 ≠ stateOut)) ∨
    (baseTrace[j] = ⟨.inr <|.inr stateOut, stateIn⟩ ∧
      ∃ j' < j,
        (∃ stateIn1 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inr stateOut, stateIn1⟩ ∧ stateIn1 ≠ stateIn) ∨
        (∃ stateIn2 : CanonicalSpongeState U,
          baseTrace[j'] = ⟨.inr <|.inl stateIn2, stateOut⟩ ∧ stateIn2 ≠ stateIn))

/-- CO25 Definition 5.7 — Combined bad event `E(tr)`.
`E(tr)` is the disjunction `E_dup(tr) ∨ E_func(tr)`, i.e., either a capacity-segment
duplication occurs or `p` behaves non-functionally.  Lemma 5.8 bounds `Pr[E(tr_P̃ ‖ tr_V)]`
in both the real `𝒟_𝔖` and simulator `𝒟_Σ` experiments. -/
def E : Prop :=
  capacitySegmentDup trace ∨ E_func trace

end Def57_TraceOnlyBadEvents

/-! ## Lemma 5.8 — closed-form bound
This section is consistency-free: `lemma_5_8` bounds `Pr[E]` directly via birthday-style
counting on freshly-sampled values. -/
section Lemma_5_8

/-- CO25 Lemma 5.8 — Closed-form upper bound on `max{Pr[E | 𝒟_𝔖], Pr[E | 𝒟_Σ]}`.
For a `(tₕ, tₚ, tₚᵢ)`-query prover and verifier making `L` permutation queries (with `tₚ ≥ L`),
the bound is:

```
(7·T² − 3·T) / (2·|Σ|^c)
```

where `T = tₕ + 1 + tₚ + L + tₚᵢ`. -/
noncomputable def lemma5_8Bound (U : Type) [SpongeUnit U] [SpongeSize] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  let tShift : ℝ := (tₕ + 1 + tₚ + L + tₚᵢ : ℕ)
  (7 * tShift ^ 2 - 3 * tShift) / (2 * ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C)

/-- CO25 §5.6 — Run a concrete duplex-sponge experiment under an oracle implementation and return
the full DS query-answer trace.  Used as the building block for both the real (`𝒟_𝔖`) and
simulator (`𝒟_Σ`) trace distributions in Lemma 5.8. -/
def traceDistOfConcreteExperiment
    {σ α : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (exp : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let outWithLog :
      OracleComp (duplexSpongeChallengeOracle StmtIn U)
        (α × QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
    (simulateQ loggingOracle exp).run
  let ⟨_, trace⟩ ← (simulateQ impl outWithLog).run' (← init)
  pure trace

variable {StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [codec : Codec pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [VCVCompatible U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]
  {T_H : Type}
  {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- Class predicate on the `[]ₒ + DS` query domain: is this a hash (`h`) query point? -/
def isHashQueryPoint : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → Bool
  | .inr (.inl _) => true
  | _ => false

/-- Class predicate on the `[]ₒ + DS` query domain: is this a forward-permutation (`p`) point? -/
def isFwdPermQueryPoint : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → Bool
  | .inr (.inr (.inl _)) => true
  | _ => false

/-- Class predicate on the `[]ₒ + DS` query domain: is this an inverse-permutation (`p⁻¹`)
point? -/
def isBwdPermQueryPoint : ([]ₒ + duplexSpongeChallengeOracle StmtIn U).Domain → Bool
  | .inr (.inr (.inr _)) => true
  | _ => false

/-- CO25 Lemma 5.8 — Semantic `(tₕ, tₚ, tₚᵢ)` query bound for the salted §5.6 prover.
`IsLemma5_8QueryBound maliciousProver tₕ tₚ tₚᵢ` asserts that the prover makes **in total** at
most `tₕ` hash queries, `tₚ` forward permutation queries, and `tₚᵢ` inverse permutation queries
on the combined `[]ₒ + DS` surface that matches the §5.8 hybrid games (LHS=Hyb_0, RHS=Hyb_1).

Formalized as three per-class `IsQueryBoundP` totals.  (A per-point
`IsPerIndexQueryBound` with a constant budget would be strictly weaker — it caps each *specific*
query point separately and admits unboundedly long traces — and cannot support the paper's
`|tr̄| ≤ tₕ + 1 + tₚ + L + tₚᵢ` accounting.) -/
abbrev IsLemma5_8QueryBound
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ) : Prop :=
  OracleComp.IsQueryBoundP maliciousProver
    (fun t => isHashQueryPoint (StmtIn := StmtIn) (U := U) t = true) tₕ ∧
  OracleComp.IsQueryBoundP maliciousProver
    (fun t => isFwdPermQueryPoint (StmtIn := StmtIn) (U := U) t = true) tₚ ∧
  OracleComp.IsQueryBoundP maliciousProver
    (fun t => isBwdPermQueryPoint (StmtIn := StmtIn) (U := U) t = true) tₚᵢ

/-- CO25 §5.6 — Project a `[]ₒ + DS` combined trace log down to just the DS component.
The empty-oracle branch is unreachable, so we discard it via `PEmpty.elim`. -/
def lemma5_8ProjectTraceLog
    (log : QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  log.filterMap fun entry =>
    match entry with
    | ⟨.inl q, _⟩ => PEmpty.elim q
    | ⟨.inr q, r⟩ => some ⟨q, r⟩

/-- The empty-oracle branch of the Section 5.6 experiment is uncallable. -/
private def lemma5_8EmptyQueryImpl {σ : Type} :
    QueryImpl []ₒ (StateT σ ProbComp) :=
  fun q => PEmpty.elim q

/-- Generic-`m` sibling of `lemma5_8EmptyQueryImpl`: the empty-oracle branch is uncallable in any
target monad. Used to build `QueryImpl ([]ₒ + DS) (OptionT (StateT _ ProbComp))` via `QueryImpl.+`
where the right summand is the abortable DS impl. -/
private def lemma5_8EmptyQueryImplGeneric {m : Type → Type} : QueryImpl []ₒ m :=
  fun q => PEmpty.elim q

/-- CO25 §5.6 (Option G) — Monad-reorder + logging wrapper. Reorders `StateT σ (OptionT ProbComp)`
into `OptionT (StateT (σ × QueryLog) ProbComp)` so the log survives an abort (paper line 1417:
"abort halts execution; trace is partial"), and appends `⟨q, a⟩` on each successful query. -/
private def lemma5_8LoggingWrapper {σ : Type}
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT σ (OptionT ProbComp))) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (OptionT
        (StateT (σ × QueryLog (duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
  fun q => OptionT.mk fun st => do
    let r ← (impl q st.1).run
    match r with
    | none => pure (none, st)
    | some (a, s') => pure (some a, (s', st.2 ++ [⟨q, a⟩]))

/-- CO25 §5.6 (Option G) — the log-appending wrapper of the Lemma-5.8 experiments, standalone so
support/counting lemmas can reason about it: each *successful* DS query appends the wide-tagged
entry `⟨Sum.inr q, a⟩` to the `[]ₒ + DS` log; an abort leaves the log unchanged (paper line 1417:
"abort halts execution; trace is partial"). -/
def lemma5_8WrappedDSImpl {σ : Type}
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT σ (OptionT ProbComp))) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (OptionT
        (StateT (σ ×
          QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
  fun q => OptionT.mk fun st => do
    let r ← (impl q st.1).run
    match r with
    | none => pure (none, st)
    | some (a, s') => pure (some a, (s', st.2 ++ [⟨Sum.inr q, a⟩]))

/-- The `[]ₒ + DS` combined implementation of the Lemma-5.8 experiments: the (uncallable) empty
branch paired with the log-appending DS wrapper `lemma5_8WrappedDSImpl`. -/
def lemma5_8CombinedImpl {σ : Type}
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT σ (OptionT ProbComp))) :
    QueryImpl ([]ₒ + duplexSpongeChallengeOracle StmtIn U)
      (OptionT
        (StateT (σ ×
          QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ProbComp)) :=
  (lemma5_8EmptyQueryImplGeneric
    (m := OptionT
      (StateT (σ ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) ProbComp)))
  + lemma5_8WrappedDSImpl (StmtIn := StmtIn) (U := U) impl

/-- CO25 §5.6 (Option G) — Abortable Lemma-5.8 trace experiment, mirroring the §5.8 hybrid skeleton
(`KeyLemma.dsfsGame` / `hybridGame`): the salted `maliciousProver` runs under `impl`, then the
forward-only verifier `𝒱^{h,p} := V.toDSFS δ` (paper Figure 4 line 3) runs on its output, with the
carrier `σ` (e.g. `D_𝔖.Carrier` / `D2SQueryState`) threaded throughout.

Returns `(tr_P̃, tr_V)`; the bad event `E` (Def 5.7) is evaluated on `tr_P̃ ++ tr_V`. -/
noncomputable def lemma5_8ProjectedTraceDistAbortable
    {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT σ (OptionT ProbComp)))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let s₀ ← init
  -- Log each DS query into the wide `[]ₒ + DS` log (tagged `Sum.inr`); the log is kept on abort.
  -- The `[]ₒ` summand is unreachable (`lemma5_8CombinedImpl` pairs it with the generic empty
  -- impl).
  let combinedImpl := lemma5_8CombinedImpl (StmtIn := StmtIn) (U := U) impl
  -- Prover phase on a fresh log `[]`; the log accumulates the prover trace `tr_P̃`.
  let proverResult ← ((simulateQ combinedImpl maliciousProver).run) (s₀, [])
  match proverResult with
  | (none, (_, trP)) =>
      -- Abort (paper line 1417): execution halts, `V` never runs, so `tr_V = []`.
      pure (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP, [])
  | (some ⟨stmtIn, proof⟩, (s₁, trP)) =>
      -- Success: verifier reuses carrier `s₁` but a fresh log, so `tr_V` is verifier-only.
      -- `runForwardVerifierWide` lifts the forward verifier to the wide spec (shared log surface).
      let verifyCompWide :
          OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) :=
        runForwardVerifierWide (oSpec := []ₒ) δ V stmtIn proof
      let verifierResult ← ((simulateQ combinedImpl verifyCompWide).run) (s₁, [])
      let trV := verifierResult.2.2
      -- Project both `[]ₒ + DS` logs down to bare DS.
      pure (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trP,
            lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trV)

/-- CO25 §5.6 — Run a concrete Lemma 5.8 experiment over `[]ₒ + DS` and keep only the DS trace.
Combines the logging oracle with the given DS implementation, runs the experiment, and projects
the combined trace down to the DS component. -/
def lemma5_8ProjectedTraceDistOfConcreteExperiment
    {σ α : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp))
    (exp : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let combinedImpl :
      QueryImpl ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp) :=
    (lemma5_8EmptyQueryImpl (σ := σ)) + impl
  let outWithLog :
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U)
        (α × QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U)) :=
    (simulateQ loggingOracle exp).run
  let ⟨_, trace⟩ ←
    (simulateQ combinedImpl outWithLog).run' (← init)
  pure (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trace)

/-- CO25 §5.6 Lemma 5.8 — Shared experiment shape for both sides of Lemma 5.8.
Runs the malicious prover under the DS oracle, then runs the DSFS verifier on the resulting
`(statement, proof)` pair.  Returns the optional verifier output.

Type-level CO25 Figure 4 line 3: the honest verifier is invoked at the narrow forward-only spec
`[]ₒ + duplexSpongeForwardOracle StmtIn U` (`𝒱^{h,p}` — no `p⁻¹`); its computation is then
`liftComp`-ed into the wide spec used by the (adversarial) prover for trace concatenation. -/
def lemma5_8TraceExperiment
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver :
      OracleComp (duplexSpongeChallengeOracle StmtIn U) (StmtIn × pSpec.Messages)) :
    OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) := do
  let _ : Codec pSpec U := codec
  let ⟨stmtIn, messages⟩ ← maliciousProver
  let verifyCompNarrow :
      OracleComp ([]ₒ + duplexSpongeForwardOracle StmtIn U) (Option StmtOut) :=
    ((Verifier.duplexSpongeFiatShamirForward
        (oSpec := []ₒ) (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
        (U := U) V).run
      stmtIn (fun i => match i with | ⟨0, _⟩ => messages)).run
  liftComp verifyCompNarrow ([]ₒ + duplexSpongeChallengeOracle StmtIn U)

/-- CO25 §5.6 (Option G) — Trivially lift a total `StateT σ ProbComp` DS implementation to the
abortable shape `StateT σ (OptionT ProbComp)` required by `lemma5_8ProjectedTraceDistAbortable`.
The lifted impl never produces `none`. -/
def lemma5_8TotalAbortLift {σ : Type}
    (impl : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ ProbComp)) :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σ (OptionT ProbComp)) :=
  fun q s => OptionT.lift (impl q s)

/-- CO25 Lemma 5.8 — Left-hand-side trace distribution (Option G — paper-faithful abort).
Real DS execution under the explicit `(h, p, p⁻¹) ← 𝒟_𝔖(λ, n)` implementation. The eager impl is
total (never aborts), so the `OptionT`-layer is a dummy. Returns the pair `(tr_P̃, tr_V)`. -/
noncomputable def lemma5_8RealTraceDist
    {σReal : Type}
    (initReal : ProbComp σReal)
    (implReal : QueryImpl (duplexSpongeChallengeOracle StmtIn U) (StateT σReal ProbComp))
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) :=
  lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ)
    initReal
    (lemma5_8TotalAbortLift (StmtIn := StmtIn) (U := U) implReal)
    V maliciousProver

/-- CO25 Lemma 5.8 — Right-hand-side trace distribution (Option G — paper-faithful abort).
Simulator execution under eager `g ← 𝒟_Σ(λ, n)` with `D2SQuery` as the oracle implementation.
The `d2sQueryImpl` runs in `StateT D2SQueryState (OptionT ProbComp)`: an `OptionT`-abort halts the
experiment (paper line 1417). Returns the pair `(tr_P̃, tr_V)`.

The `g` carrier is sampled **once** at experiment start from `𝒟_Σ`, captured by closure,
and consulted deterministically by every `gᵢ` query. This mirrors `lemma5_8RealTraceDist`'s
eager `(h, p, p⁻¹) ← 𝒟_𝔖` sampling — CO25 Def. 4.2 + Lemma 5.8 statement. -/
noncomputable def lemma5_8SigmaTraceDist
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    ProbComp (QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
              QueryLog (duplexSpongeChallengeOracle StmtIn U)) := do
  let k_g ←
    (D_Sigma (U := U) StmtIn pSpec δ).sample
  lemma5_8ProjectedTraceDistAbortable (StmtIn := StmtIn) (StmtOut := StmtOut)
    (pSpec := pSpec) (U := U) (δ := δ)
    (init := pure default)
    (impl := ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (gImpl := fun q => OptionT.lift
        ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q))
      (auxImpl := fun aux => OptionT.lift
        ((ProverTransform.d2sUnitSampleImpl (U := U) +
          QueryImpl.id' unifSpec) aux)))
    V maliciousProver

/- CO25 Lemma 5.8 — the bad-event probability bound `max{Pr[E|𝒟_𝔖], Pr[E|𝒟_Σ]} ≤ (7T²−3T)/(2|Σ|^c)`
— is stated and assembled in `BadEventsProb.lean` as `BadEventDS.lemma_5_8`.  It could not live here
because its proof factors through the per-index refactor + union bound (`BadEventsProb`), which
imports this file.  The Layer-B/D/E numeric spine there is fully proven; the remaining obligations
are the per-side Layer-A length bound and Layer-C per-index freshness bounds. -/

end Lemma_5_8

/-! ## Definition 5.9 — permutation collisions; paper `E_prp`; well-formed trace predicate -/
section Def5_9_CollisionsAndConsistency

/-! Then we define other bad events that don't hold (`= 0`)
if the combined event doesn't hold (`= 0`)
-/

/-- CO25 Definition 5.9 Item 1 — Event `E_{col,p}(tr)`.
There exist `(p, s_in, s_out)` and `(p, s_in', s_out)` in `tr̄` with `s_in ≠ s_in'`:
two distinct forward-permutation inputs map to the same output. -/
def collisionFwdFwd : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ stateIn stateIn' stateOut,
    ⟨.inr <|.inl stateIn, stateOut⟩ ∈ baseTrace ∧
    ⟨.inr <|.inl stateIn', stateOut⟩ ∈ baseTrace ∧
    stateIn ≠ stateIn'

alias E_col_p := collisionFwdFwd

/-- CO25 Definition 5.9 Item 2 — Event `E_{col,p⁻¹}(tr)`.
There exist `(p⁻¹, s_out, s_in)` and `(p⁻¹, s_out', s_in)` in `tr̄` with `s_out ≠ s_out'`:
two distinct inverse-permutation inputs map to the same output. -/
def collisionBwdBwd : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ stateOut stateOut' stateIn,
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut', stateIn⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv := collisionBwdBwd

/-- CO25 Definition 5.9 Item 3 — Event `E_{col,p,p⁻¹}(tr)` in exact paper shape.
There exist `(p, s_in, s_out)` and `(p⁻¹, s_out, s_in')` in `tr̄` with `s_out = s_out'` and
`s_in ≠ s_in'`: `p` is onto but its inverse is not a function. -/
def collisionFwdBwd : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ stateIn stateOut stateIn',
    ⟨.inr <| .inl stateIn, stateOut⟩ ∈ baseTrace ∧
    ⟨.inr <| .inr stateOut, stateIn'⟩ ∈ baseTrace ∧
    stateIn ≠ stateIn'

alias E_col_p_pinv := collisionFwdBwd

/-- CO25 Definition 5.9 Item 4 — Event `E_{col,p⁻¹,p}(tr)` in exact paper shape.
There exist `(p⁻¹, s_out, s_in)` and `(p, s_in, s_out')` in `tr̄` with `s_out ≠ s_out'`:
`p⁻¹` is onto but `p` is not a function. -/
def collisionBwdFwd : Prop :=
  let baseTrace := getBaseTrace trace
  ∃ stateOut stateIn stateOut',
    ⟨.inr <| .inr stateOut, stateIn⟩ ∈ baseTrace ∧
    ⟨.inr <| .inl stateIn, stateOut'⟩ ∈ baseTrace ∧
    stateOut ≠ stateOut'

alias E_col_pinv_p := collisionBwdFwd

/-- CO25 Definition 5.9 — Event `E_prp(tr)`: the disjunction of the four collision events above
(`E_col_p`, `E_col_pinv`, `E_col_p_pinv`, `E_col_pinv_p`). Informally, Items 1/3 make `p`
non-injective; Items 2/4 make `p⁻¹` non-injective. -/
def collisionPerm : Prop :=
  collisionFwdFwd trace ∨ collisionBwdBwd trace
    ∨ collisionFwdBwd trace ∨ collisionBwdFwd trace

alias E_prp := collisionPerm

end Def5_9_CollisionsAndConsistency

/-! ## Lemma 5.10 — trace-level bad-event implication -/
section Lemma5_10

/-- CO25 Lemma 5.10 helper: `¬E(tr)` rules out Item 1 of Definition 5.9. -/
lemma not_collisionFwdFwd_of_not_combined (h : ¬ E trace) : ¬ collisionFwdFwd trace := by
  intro hff
  apply h; clear h
  obtain ⟨sI, sI', sO, hm1, hm2, hne⟩ := hff
  rw [List.mem_iff_get] at hm1 hm2
  obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
  obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
  simp only [List.get_eq_getElem] at hgi hgj
  have hij : i ≠ j := by
    intro heq; subst heq; rw [hgi] at hgj
    exact hne (congrArg (fun x => match x with | ⟨.inr (.inl s), _⟩ => s | _ => sI) hgj)
  left; right; left
  rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
  · exact ⟨⟨j, hj⟩, sO.capacitySegment, ⟨sI', sO, hgj, rfl⟩,
      Or.inr (Or.inl ⟨⟨i, hi⟩, h_lt, sI, sO, hgi, rfl⟩)⟩
  · exact ⟨⟨i, hi⟩, sO.capacitySegment, ⟨sI, sO, hgi, rfl⟩,
      Or.inr (Or.inl ⟨⟨j, hj⟩, h_lt, sI', sO, hgj, rfl⟩)⟩

/-- CO25 Lemma 5.10 helper: `¬E(tr)` rules out Item 2 of Definition 5.9. -/
lemma not_collisionBwdBwd_of_not_combined (h : ¬ E trace) : ¬ collisionBwdBwd trace := by
  intro hbb
  apply h; clear h
  obtain ⟨sO, sO', sI, hm1, hm2, hne⟩ := hbb
  rw [List.mem_iff_get] at hm1 hm2
  obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
  obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
  simp only [List.get_eq_getElem] at hgi hgj
  have hij : i ≠ j := by
    intro heq; subst heq; rw [hgi] at hgj
    exact hne (congrArg (fun x => match x with | ⟨.inr (.inr s), _⟩ => s | _ => sO) hgj)
  left; right; right
  unfold capacitySegmentDupPermInv
  rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
  · refine ⟨⟨j, hj⟩, sI.capacitySegment, ⟨sO', sI, hgj, rfl⟩, ?_⟩
    right; right; left
    exact ⟨⟨i, hi⟩, h_lt, sO, sI, hgi, rfl⟩
  · refine ⟨⟨i, hi⟩, sI.capacitySegment, ⟨sO, sI, hgi, rfl⟩, ?_⟩
    right; right; left
    exact ⟨⟨j, hj⟩, h_lt, sO', sI, hgj, rfl⟩

/-- CO25 Lemma 5.10 helper: `¬E(tr)` rules out Item 3 of Definition 5.9. -/
lemma not_collisionFwdBwd_of_not_combined (h : ¬ E trace) : ¬ collisionFwdBwd trace := by
  intro hfb
  apply h; clear h
  obtain ⟨sI, sO, sI', hm1, hm2, hne⟩ := hfb
  rw [List.mem_iff_get] at hm1 hm2
  obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
  obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
  simp only [List.get_eq_getElem] at hgi hgj
  have hij : i ≠ j := by
    intro heq; subst heq; rw [hgi] at hgj
    have hq : true = false :=
      congrArg (fun x => match x with | ⟨.inr (.inl _), _⟩ => true | _ => false) hgj
    contradiction
  rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
  · right
    refine ⟨⟨j, hj⟩, sI', sO, Or.inr ⟨hgj, ⟨⟨i, hi⟩, h_lt, Or.inr ⟨sI, hgi, hne⟩⟩⟩⟩
  · left; right; left
    unfold capacitySegmentDupPerm
    refine ⟨⟨i, hi⟩, sO.capacitySegment, ⟨sI, sO, hgi, rfl⟩,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨j, hj⟩, h_lt.le, sO, sI', hgj, rfl⟩)))⟩

/-- CO25 Lemma 5.10 helper: `¬E(tr)` rules out Item 4 of Definition 5.9. -/
lemma not_collisionBwdFwd_of_not_combined (h : ¬ E trace) : ¬ collisionBwdFwd trace := by
  intro hbf
  apply h; clear h
  obtain ⟨sO, sI, sO', hm1, hm2, hne⟩ := hbf
  rw [List.mem_iff_get] at hm1 hm2
  obtain ⟨⟨i, hi⟩, hgi⟩ := hm1
  obtain ⟨⟨j, hj⟩, hgj⟩ := hm2
  simp only [List.get_eq_getElem] at hgi hgj
  have hij : i ≠ j := by
    intro heq; subst heq; rw [hgi] at hgj
    have hq : true = false :=
      congrArg (fun x => match x with | ⟨.inr (.inr _), _⟩ => true | _ => false) hgj
    contradiction
  rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
  · right
    refine ⟨⟨j, hj⟩, sI, sO', Or.inl ⟨hgj, ⟨⟨i, hi⟩, h_lt, Or.inr ⟨sO, hgi, hne⟩⟩⟩⟩
  · left; right; right
    unfold capacitySegmentDupPermInv
    refine ⟨⟨i, hi⟩, sI.capacitySegment, ⟨sO, sI, hgi, rfl⟩,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨j, hj⟩, h_lt.le, sI, sO', hgj, rfl⟩)))⟩

/-- CO25 Lemma 5.10 — helper.
For a well-formed `(h, p, p⁻¹)` trace, if `E(tr) = 0`, then the exact paper-form
`E_prp(tr)` does not hold. -/
lemma not_collisionPerm_of_not_combined
    (h : ¬ E trace) : ¬ E_prp trace := by
  intro hprp
  rcases hprp with hff | hbb | hfb | hbf
  · exact not_collisionFwdFwd_of_not_combined (trace := trace) h hff
  · exact not_collisionBwdBwd_of_not_combined (trace := trace) h hbb
  · exact not_collisionFwdBwd_of_not_combined (trace := trace) h hfb
  · exact not_collisionBwdFwd_of_not_combined (trace := trace) h hbf

/-- CO25 Lemma 5.10.
For a well-formed `(h, p, p⁻¹)` trace, if `E(tr) = 0` then `E_prp(tr) = 0`. -/
theorem lemma_5_10 (h : ¬ E trace) : ¬ E_prp trace :=
  not_collisionPerm_of_not_combined (trace := trace) h

end Lemma5_10

/-! ## Toolbox for Lemmas 5.12 / 5.14 / 5.16

Following the patch `DSFS-archive/(Analysis #1) …`, §4 (Lemma B) and §5.  The proofs of the three
BackTrack-family lemmas reduce to two freshness corollaries of `¬E_dup`:

- **(B1)** distinct base entries have distinct *answer capacities* (`answerCap_inj`);
- **(B2)** a base entry's answer capacity never equals the *query capacity* of an earlier-or-equal
  base entry (`answerCap_ne_queryCap_le`).

`answerCap`/`queryCap` name the paper's `acap`/`qcap`. -/
section BadEventToolbox

/-- The *answer capacity* `acap(e)` of a base trace entry (patch §1, terminology table):
the capacity segment of the value the entry returns. -/
def answerCap (e : Sigma (duplexSpongeChallengeOracle StmtIn U)) : Vector U SpongeSize.C :=
  match e with
  | ⟨.inl _, cap⟩ => cap
  | ⟨.inr (.inl _), sOut⟩ => sOut.capacitySegment
  | ⟨.inr (.inr _), sIn⟩ => sIn.capacitySegment

/-- The *query capacity* `qcap(e)` of a base trace entry: the capacity segment of the value the
entry was queried on.  Defined only for permutation entries (`none` for `h`). -/
def queryCap (e : Sigma (duplexSpongeChallengeOracle StmtIn U)) : Option (Vector U SpongeSize.C) :=
  match e with
  | ⟨.inl _, _⟩ => none
  | ⟨.inr (.inl sIn), _⟩ => some sIn.capacitySegment
  | ⟨.inr (.inr sOut), _⟩ => some sOut.capacitySegment

/-- `¬E` splits into `¬E_dup`. -/
lemma not_E_dup_of_not_E (h : ¬ E trace) : ¬ capacitySegmentDup trace :=
  fun hd => h (Or.inl hd)

/-- `¬E` splits into `¬E_func`. -/
lemma not_E_func_of_not_E (h : ¬ E trace) : ¬ E_func trace :=
  fun hf => h (Or.inr hf)

/-- If an earlier base entry has answer capacity `c`, then index `j` sees a duplicated prior
capacity `c` (the `< j` clauses of `isDuplicatedPriorCapacity`). -/
private lemma isDup_of_earlier_answerCap
    {baseTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {i j : Fin baseTrace.length} (hij : i < j)
    {e₁ : Sigma (duplexSpongeChallengeOracle StmtIn U)} (h1 : baseTrace[i] = e₁)
    {c : Vector U SpongeSize.C} (hc : answerCap e₁ = c) :
    isDuplicatedPriorCapacity baseTrace j c := by
  obtain ⟨q, r⟩ := e₁
  match q with
  | .inl stmt =>
      simp only [answerCap] at hc
      exact Or.inl ⟨i, hij, stmt, by rw [h1, hc]⟩
  | .inr (.inl sIn) =>
      simp only [answerCap] at hc
      exact Or.inr <| Or.inl ⟨i, hij, sIn, r, by rw [h1], hc⟩
  | .inr (.inr sOut) =>
      simp only [answerCap] at hc
      exact Or.inr <| Or.inr <| Or.inl ⟨i, hij, sOut, r, by rw [h1], hc⟩

/-- If an earlier-or-equal base entry is a permutation entry with query capacity `c`, then index
`j` sees a duplicated prior capacity `c` (the `≤ j` clauses of `isDuplicatedPriorCapacity`). -/
private lemma isDup_of_le_queryCap
    {baseTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {i j : Fin baseTrace.length} (hij : i ≤ j)
    {e₁ : Sigma (duplexSpongeChallengeOracle StmtIn U)} (h1 : baseTrace[i] = e₁)
    {c : Vector U SpongeSize.C} (hc : queryCap e₁ = some c) :
    isDuplicatedPriorCapacity baseTrace j c := by
  obtain ⟨q, r⟩ := e₁
  match q with
  | .inl stmt =>
      simp only [queryCap, reduceCtorEq] at hc
  | .inr (.inl sIn) =>
      simp only [queryCap, Option.some.injEq] at hc
      exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨i, hij, sIn, r, by rw [h1], hc⟩
  | .inr (.inr sOut) =>
      simp only [queryCap, Option.some.injEq] at hc
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨i, hij, sOut, r, by rw [h1], hc⟩

/-- If the entry at index `j` has a duplicated prior capacity equal to its own answer capacity,
then `E_dup` holds. -/
private lemma capacitySegmentDup_of_isDup_at
    {j : Fin (getBaseTrace trace).length}
    {e₂ : Sigma (duplexSpongeChallengeOracle StmtIn U)} (h2 : (getBaseTrace trace)[j] = e₂)
    (hdupCap : isDuplicatedPriorCapacity (getBaseTrace trace) j (answerCap e₂)) :
    capacitySegmentDup trace := by
  obtain ⟨q, r⟩ := e₂
  match q with
  | .inl stmt =>
      refine Or.inl ⟨j, answerCap ⟨.inl stmt, r⟩, ⟨stmt, ?_⟩, hdupCap⟩
      simp only [answerCap]; exact h2
  | .inr (.inl sIn) =>
      refine Or.inr <| Or.inl ⟨j, answerCap ⟨.inr (.inl sIn), r⟩, ⟨sIn, r, h2, ?_⟩, hdupCap⟩
      simp only [answerCap]
  | .inr (.inr sOut) =>
      refine Or.inr <| Or.inr ⟨j, answerCap ⟨.inr (.inr sOut), r⟩, ⟨sOut, r, h2, ?_⟩, hdupCap⟩
      simp only [answerCap]

/-- **(B1)** If `¬E_dup`, then distinct base entries have distinct answer capacities. -/
lemma answerCap_inj (hdup : ¬ capacitySegmentDup trace)
    {e₁ e₂ : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (h1 : e₁ ∈ getBaseTrace trace) (h2 : e₂ ∈ getBaseTrace trace)
    (hne : e₁ ≠ e₂) : answerCap e₁ ≠ answerCap e₂ := by
  intro hAcap
  apply hdup
  rw [List.mem_iff_getElem] at h1 h2
  obtain ⟨i, hi, hgi⟩ := h1
  obtain ⟨j, hj, hgj⟩ := h2
  have hij : i ≠ j := by
    intro h; subst h; rw [hgi] at hgj; exact hne hgj
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · -- `e₁` (index i) earlier; collide at `j` with `e₂`.
    refine capacitySegmentDup_of_isDup_at trace (j := ⟨j, hj⟩) hgj ?_
    exact isDup_of_earlier_answerCap (i := ⟨i, hi⟩) hlt hgi (by rw [hAcap])
  · -- `e₂` (index j) earlier; collide at `i` with `e₁`.
    refine capacitySegmentDup_of_isDup_at trace (j := ⟨i, hi⟩) hgi ?_
    exact isDup_of_earlier_answerCap (i := ⟨j, hj⟩) hlt hgj (by rw [hAcap])

/-- Capacity segments at definitionally-equal indices agree (used to discharge index arithmetic
without rewriting inside `getElem`). -/
lemma inputCap_congr {l : List (CanonicalSpongeState U)} {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i = j) :
    l[i].capacitySegment = l[j].capacitySegment := by
  subst hij; rfl

omit [SpongeSize] in
/-- `getElem` at equal indices agree. -/
lemma getElem_idx_congr {α : Type*} {l : List α} {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i = j) : l[i] = l[j] := by
  subst hij; rfl

omit [SpongeSize] in
/-- `getElem` of equal lists at the same index agree. -/
lemma getElem_listEq {α : Type*} {l l' : List α} (hll : l = l') {i : ℕ}
    (hi : i < l.length) (hi' : i < l'.length) : l[i] = l'[i] := by
  subst hll; rfl

/-- Injectivity of the forward-permutation entry shape. -/
lemma fwdEntry_inj {a a' b b' : CanonicalSpongeState U}
    (heq : (⟨.inr (.inl a), b⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
         = ⟨.inr (.inl a'), b'⟩) : a = a' ∧ b = b' := by
  rw [Sigma.mk.injEq] at heq
  obtain ⟨h1, h2⟩ := heq
  rw [Sum.inr.injEq, Sum.inl.injEq] at h1
  subst h1
  exact ⟨rfl, eq_of_heq h2⟩

/-- Contrapositive of (B1): base entries with equal answer capacities are equal. -/
lemma eq_of_answerCap_eq (hdup : ¬ capacitySegmentDup trace)
    {e₁ e₂ : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (h1 : e₁ ∈ getBaseTrace trace) (h2 : e₂ ∈ getBaseTrace trace)
    (heq : answerCap e₁ = answerCap e₂) : e₁ = e₂ := by
  by_contra hne
  exact answerCap_inj trace hdup h1 h2 hne heq

/-- **(B2)** If `¬E_dup`, then a base entry's answer capacity never equals the query capacity of
an earlier-or-equal base entry. -/
lemma answerCap_ne_queryCap_le (hdup : ¬ capacitySegmentDup trace)
    {i j : Fin (getBaseTrace trace).length} (hij : i ≤ j)
    {c : Vector U SpongeSize.C} (hq : queryCap (getBaseTrace trace)[i] = some c) :
    answerCap (getBaseTrace trace)[j] ≠ c := by
  intro hAcap
  apply hdup
  refine capacitySegmentDup_of_isDup_at trace (j := j) rfl ?_
  rw [hAcap]
  exact isDup_of_le_queryCap (i := i) (j := j) hij rfl hq

end BadEventToolbox

/-! ## Definition 5.11 and Lemma 5.12 — inverse-step event -/
section Def511_Lemma512

/-- CO25 Definition 5.11 — event `E_inv(tr, s)`.

Paper-faithful (CO25 Eq. 35): `E_inv(tr, s) = 1` iff there exists an index list
`J^(k) = (j_h^(k), j_0^(k), …, j_{m_k}^(k)) ∈ 𝒥_BT(tr, s)` and an index `ι ∈ [0, m_k - 1]` such
that `tr_{j_ι^(k)} = ('p⁻¹', ·, ·)`, i.e., the `ι`-th step of the corresponding BackTrack
sequence is constructed using `p⁻¹` rather than `p`.

`𝒥_BT(tr, s)` is computed deterministically from `S_BT(tr, s)` via
`Backtrack.BacktrackSequence.Index` (cf. CO25 Def 5.4), so this definition takes `S_BT` as input
but quantifies directly over `Backtrack.J_BT S_BT` in the body. -/
def E_inv (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ p ∈ Backtrack.J_BT S_BT,
  ∃ ι : Fin p.1.outputState.length,
  ∃ s_out s_in : CanonicalSpongeState U,
    (trace)[(p.2.2 ⟨ι.val, by
      have := p.1.inputState_length_eq_outputState_length_succ
      omega⟩).val]? = some ⟨.inr (.inr s_out), s_in⟩
    -- (Eq. 36): ι = 0
    -- (Eq. 37): 0 < ι ≤ m_k - 1

/-- CO25 Lemma 5.12 — If `E(tr) = 0` then `E_inv(tr, s) = 0`.

Patch §5.2: by **minimal inversion**.  Suppose some step's representative is a `p⁻¹` entry; take the
minimal such step `ι*` (strong induction).  If `ι* = 0`, the hash anchor and the inverted step are
two distinct base entries with equal answer capacity (`acap = s_{C,in,0}`), contradicting (B1).  If
`ι* ≥ 1`, minimality makes step `ι*-1` forward, and the chain condition forces its answer capacity
to equal the inverted step's — again two distinct base entries colliding, contradicting (B1). -/
lemma lemma_5_12 (h : ¬ E trace)
    (seq_BT : Backtrack.S_BT trace state) :
    ¬ E_inv trace state seq_BT := by
  classical
  have hdup : ¬ capacitySegmentDup trace := not_E_dup_of_not_E trace h
  intro he_inv
  obtain ⟨p, hp, ι, s_out, s_in, hentry⟩ := he_inv
  obtain ⟨seq, hseq, rfl⟩ := Finset.mem_image.mp hp
  have hlen : seq.inputState.length = seq.outputState.length + 1 :=
    seq.inputState_length_eq_outputState_length_succ
  -- No step's representative is a `p⁻¹` entry (proved by strong induction = minimal inversion).
  have key : ∀ k, ∀ (hk : k < seq.outputState.length) (hki : k < seq.inputState.length),
      (trace)[((Backtrack.BacktrackSequence.Index trace state seq).2 ⟨k, hki⟩).val]?
        ≠ some ⟨.inr (.inr seq.outputState[k]), seq.inputState[k]⟩ := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      rcases k with _ | j
      · -- ι* = 0: collide with the hash anchor.
        intro hk hki hQ
        have hpos : 0 < seq.inputState.length := by omega
        -- The inverted step-0 entry is in the base trace.
        have hnotmem := Backtrack.BacktrackSequence.Index_snd_not_mem_take seq ⟨0, hk⟩ hki
        have hmemB : (⟨.inr (.inr seq.outputState[0]), seq.inputState[0]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace :=
          permInv_mem_getBaseTrace trace hQ hnotmem.2 hnotmem.1
        -- The hash anchor is in the base trace.
        have hgetH : (trace)[((Backtrack.BacktrackSequence.Index trace state seq).1).val]?
            = some ⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ := by
          rw [List.getElem?_eq_getElem (Backtrack.BacktrackSequence.Index trace state seq).1.isLt,
            ← List.get_eq_getElem]
          exact congrArg some (Backtrack.BacktrackSequence.Index_fst_get seq hpos)
        have hmemH : (⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace :=
          hash_mem_getBaseTrace trace hgetH
            (Backtrack.BacktrackSequence.Index_fst_not_mem_take seq hpos)
        -- Equal answer capacities, distinct entries: contradicts (B1).
        refine answerCap_inj trace hdup hmemH hmemB (by simp) ?_
        simp only [answerCap, CanonicalSpongeState.capacitySegment]
      · -- ι* = j+1: minimality makes step j forward; collide via the chain condition.
        intro hk hki hQ
        have hkj : j < seq.outputState.length := by omega
        have hkij : j < seq.inputState.length := by omega
        -- Step j is not inverted (induction hypothesis), hence forward.
        have hjnot := ih j (Nat.lt_succ_self j) hkj hkij
        have hjspec := Backtrack.BacktrackSequence.Index_snd_getElem? seq ⟨j, hkj⟩ hkij
        have hjfwd : (trace)[((Backtrack.BacktrackSequence.Index trace state seq).2
            ⟨j, hkij⟩).val]? = some ⟨.inr (.inl seq.inputState[j]), seq.outputState[j]⟩ := by
          rcases hjspec with hA | hB
          · exact hA
          · exact absurd hB hjnot
        -- The forward step-j entry and the inverted step-(j+1) entry are in the base trace.
        have hnotmemJ := Backtrack.BacktrackSequence.Index_snd_not_mem_take seq ⟨j, hkj⟩ hkij
        have hmemA : (⟨.inr (.inl seq.inputState[j]), seq.outputState[j]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace :=
          permFwd_mem_getBaseTrace trace hjfwd hnotmemJ.1 hnotmemJ.2
        have hnotmemB := Backtrack.BacktrackSequence.Index_snd_not_mem_take seq ⟨j + 1, hk⟩ hki
        have hmemB : (⟨.inr (.inr seq.outputState[j + 1]), seq.inputState[j + 1]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace :=
          permInv_mem_getBaseTrace trace hQ hnotmemB.2 hnotmemB.1
        -- Chain condition `(d)`: `s_{C,out,j} = s_{C,in,j+1}`, so equal answer capacities.
        refine answerCap_inj trace hdup hmemA hmemB (by simp) ?_
        simp only [answerCap]
        exact seq.capacitySegment_output_eq_input ⟨j, hkj⟩
  -- Apply `key` to the witnessing inverted step `ι`.
  have hιlt : ι.val < seq.outputState.length := ι.isLt
  have hki : ι.val < seq.inputState.length := by omega
  have hentry' : (trace)[((Backtrack.BacktrackSequence.Index trace state seq).2 ⟨ι.val, hki⟩).val]?
      = some ⟨.inr (.inr s_out), s_in⟩ := hentry
  have hspec := Backtrack.BacktrackSequence.Index_snd_getElem? seq ι hki
  rw [hentry'] at hspec
  rcases hspec with hA | hB
  · simp at hA
  · rw [Option.some_inj] at hB
    exact key ι.val hιlt hki (hB ▸ hentry')

/-- Corollary of Lemma 5.12: under `¬E`, every backtrack step's representative is the *forward*
(`p`) query form. -/
lemma step_forward (h : ¬ E trace) (S_BT : Backtrack.S_BT trace state)
    {seq : Backtrack.BacktrackSequence trace state} (hseq : seq ∈ S_BT.seqFamily)
    (k : ℕ) (hk : k < seq.outputState.length) (hki : k < seq.inputState.length) :
    (trace)[((Backtrack.BacktrackSequence.Index trace state seq).2 ⟨k, hki⟩).val]?
      = some ⟨.inr (.inl seq.inputState[k]), seq.outputState[k]⟩ := by
  classical
  rcases Backtrack.BacktrackSequence.Index_snd_getElem? seq ⟨k, hk⟩ hki with hA | hB
  · exact hA
  · exfalso
    apply lemma_5_12 (trace := trace) (state := state) h S_BT
    exact ⟨⟨seq, Backtrack.BacktrackSequence.Index trace state seq⟩,
      Finset.mem_image_of_mem _ hseq, ⟨k, hk⟩, seq.outputState[k], seq.inputState[k], hB⟩

/-- Base-trace index of a forward step's representative (`|getBaseTrace (trace.take j_k)|`). -/
lemma fwdStep_base (h : ¬ E trace) (S_BT : Backtrack.S_BT trace state)
    {seq : Backtrack.BacktrackSequence trace state} (hseq : seq ∈ S_BT.seqFamily)
    (k : ℕ) (hk : k < seq.outputState.length) (hki : k < seq.inputState.length) :
    ∃ idx : Fin (getBaseTrace trace).length,
      idx.val = (getBaseTrace (trace.take
        ((Backtrack.BacktrackSequence.Index trace state seq).2 ⟨k, hki⟩).val)).length ∧
      (getBaseTrace trace)[idx] = ⟨.inr (.inl seq.inputState[k]), seq.outputState[k]⟩ := by
  have hget := step_forward (trace := trace) (state := state) h S_BT hseq k hk hki
  have hnotmem := Backtrack.BacktrackSequence.Index_snd_not_mem_take seq ⟨k, hk⟩ hki
  have hnr : ¬ isRedundantEntryOfPrefix
      (trace.take ((Backtrack.BacktrackSequence.Index trace state seq).2 ⟨k, hki⟩).val)
      ⟨.inr (.inl seq.inputState[k]), seq.outputState[k]⟩ := by
    intro hred; simp only [isRedundantEntryOfPrefix] at hred
    rcases hred with hh | hh
    · exact hnotmem.1 hh
    · exact hnotmem.2 hh
  obtain ⟨hb, heq⟩ := baseIdx_of_getElem?_not_redundant trace hget hnr
  exact ⟨⟨_, hb⟩, rfl, heq⟩

/-- A forward step's representative entry is a member of the base trace. -/
lemma fwdStep_mem (h : ¬ E trace) (S_BT : Backtrack.S_BT trace state)
    {seq : Backtrack.BacktrackSequence trace state} (hseq : seq ∈ S_BT.seqFamily)
    (k : ℕ) (hk : k < seq.outputState.length) (hki : k < seq.inputState.length) :
    (⟨.inr (.inl seq.inputState[k]), seq.outputState[k]⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace := by
  obtain ⟨idx, _, heq⟩ := fwdStep_base (trace := trace) (state := state) h S_BT hseq k hk hki
  exact heq ▸ List.getElem_mem idx.isLt

/-- Base-trace index of the hash anchor (`|getBaseTrace (trace.take j_h)|`). -/
lemma hashAnchor_base (seq : Backtrack.BacktrackSequence trace state)
    (hpos : 0 < seq.inputState.length) :
    ∃ idx : Fin (getBaseTrace trace).length,
      idx.val = (getBaseTrace (trace.take
        ((Backtrack.BacktrackSequence.Index trace state seq).1).val)).length ∧
      (getBaseTrace trace)[idx]
        = ⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ := by
  have hget : (trace)[((Backtrack.BacktrackSequence.Index trace state seq).1).val]?
      = some ⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ := by
    rw [List.getElem?_eq_getElem (Backtrack.BacktrackSequence.Index trace state seq).1.isLt,
      ← List.get_eq_getElem]
    exact congrArg some (Backtrack.BacktrackSequence.Index_fst_get seq hpos)
  have hnr : ¬ isRedundantEntryOfPrefix
      (trace.take ((Backtrack.BacktrackSequence.Index trace state seq).1).val)
      ⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ := by
    intro hred; simp only [isRedundantEntryOfPrefix] at hred
    exact (Backtrack.BacktrackSequence.Index_fst_not_mem_take seq hpos) hred
  obtain ⟨hb, heq⟩ := baseIdx_of_getElem?_not_redundant trace hget hnr
  exact ⟨⟨_, hb⟩, rfl, heq⟩

/-- The hash anchor entry is a member of the base trace. -/
lemma hashAnchor_mem (seq : Backtrack.BacktrackSequence trace state)
    (hpos : 0 < seq.inputState.length) :
    (⟨.inl seq.stmt, Vector.drop (seq.inputState[0]'hpos) SpongeSize.R⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace := by
  obtain ⟨idx, _, heq⟩ := hashAnchor_base (trace := trace) (state := state) seq hpos
  exact heq ▸ List.getElem_mem idx.isLt

end Def511_Lemma512

/-! ## Lemma 5.14 -/
section Def513_Lemma514

/-- CO25 Definition 5.13 / Eq. 38 — `E_{fork,h}(tr, s)`: collision of two outputs of `h`.
Two backtrack sequences in `𝒮_BT(tr, s)` have distinct input statements `𝕩^{(1)} ≠ 𝕩^{(2)}` but
their first input states share the same capacity segment `s_{C,in,0}^{(1)} = s_{C,in,0}^{(2)}`. -/
def E_fork_h (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ S₁ ∈ S_BT.seqFamily, ∃ S₂ ∈ S_BT.seqFamily,
    S₁.stmt ≠ S₂.stmt ∧
    (S₁.inputState[0]'(by
      have := S₁.inputState_length_eq_outputState_length_succ; omega)).capacitySegment =
    (S₂.inputState[0]'(by
      have := S₂.inputState_length_eq_outputState_length_succ; omega)).capacitySegment

/-- CO25 Definition 5.13 / Eq. 39 — `E_{fork,p}(tr, s)`: capacity-segment collision of two
outputs of `p`.  There exist `S^{(1)}, S^{(2)} ∈ 𝒮_BT(tr, s)` and indices
`ι_1 ∈ [0, m_1 - 1]`, `ι_2 ∈ [0, m_2 - 1]` with `s_{in,ι_1}^{(1)} ≠ s_{in,ι_2}^{(2)}` (full input
states differ) and `s_{C,out,ι_1}^{(1)} = s_{C,out,ι_2}^{(2)}` (output capacity segments
coincide). -/
def E_fork_p (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ S₁ ∈ S_BT.seqFamily, ∃ S₂ ∈ S_BT.seqFamily,
  ∃ ι₁ : Fin S₁.outputState.length, ∃ ι₂ : Fin S₂.outputState.length,
    S₁.inputState[ι₁.val]'(by have := S₁.inputState_length_eq_outputState_length_succ; omega) ≠
    S₂.inputState[ι₂.val]'(by have := S₂.inputState_length_eq_outputState_length_succ; omega) ∧
    S₁.outputState[ι₁].capacitySegment = S₂.outputState[ι₂].capacitySegment

/-- CO25 Definition 5.13 / Eq. 40 — `E_{fork,h,p}(tr, s)`: collision of `h` with the output
capacity segment of a query to `p`.  There exist `S^{(1)}, S^{(2)} ∈ 𝒮_BT(tr, s)` and
`ι ∈ [m_2 - 1]` (paper notation: `{1, …, m₂ - 1}`) with
`s_{C,in,0}^{(1)} = s_{C,out,ι}^{(2)}`.

Note: `ι ≥ 1` is required by the paper — the `ι = 0` case cannot arise in the
exhaustiveness proof (Claim 5.19) because it would be handled by `E_fork_h` instead. -/
def E_fork_h_p (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ S₁ ∈ S_BT.seqFamily, ∃ S₂ ∈ S_BT.seqFamily,
  ∃ ι : Fin S₂.outputState.length,
    0 < ι.val ∧ (S₁.inputState[0]'(by
      have := S₁.inputState_length_eq_outputState_length_succ; omega)).capacitySegment =
    S₂.outputState[ι].capacitySegment

def E_fork (S_BT : Backtrack.S_BT trace state) : Prop :=
  S_BT.seqFamily.card > 1

/-- Backward determinism (Lemma 5.14, Step 1): two backtrack sequences ending at the same state
agree on their input states counting from the end, as long as `E_dup = 0`.  All steps are forward
(Lemma 5.12), so equal next-input forces equal output capacities (chain), hence equal base
representatives (B1), hence equal full predecessor states. -/
private lemma bt_seq_eq_of_le (h : ¬ E trace) (S_BT : Backtrack.S_BT trace state)
    {A B : Backtrack.BacktrackSequence trace state}
    (hA : A ∈ S_BT.seqFamily) (hB : B ∈ S_BT.seqFamily)
    (hmle : A.outputState.length ≤ B.outputState.length) : A = B := by
  classical
  have hdup : ¬ capacitySegmentDup trace := not_E_dup_of_not_E trace h
  have hAlen : A.inputState.length = A.outputState.length + 1 :=
    A.inputState_length_eq_outputState_length_succ
  have hBlen : B.inputState.length = B.outputState.length + 1 :=
    B.inputState_length_eq_outputState_length_succ
  -- Step 1: backward determinism on input states.
  have bdet : ∀ d, d ≤ A.outputState.length →
      A.inputState.get ⟨A.outputState.length - d, by omega⟩
        = B.inputState.get ⟨B.outputState.length - d, by omega⟩ := by
    intro d
    induction d with
    | zero =>
      intro _
      have hA0 : A.inputState.get ⟨A.outputState.length - 0, by omega⟩ = state := by
        have e1 : (⟨A.outputState.length - 0, by omega⟩ : Fin A.inputState.length)
                = ⟨A.inputState.length - 1, by omega⟩ := by rw [Fin.mk.injEq]; omega
        rw [e1, List.get_eq_getElem]
        exact A.last_inputState_eq_state
      have hB0 : B.inputState.get ⟨B.outputState.length - 0, by omega⟩ = state := by
        have e1 : (⟨B.outputState.length - 0, by omega⟩ : Fin B.inputState.length)
                = ⟨B.inputState.length - 1, by omega⟩ := by rw [Fin.mk.injEq]; omega
        rw [e1, List.get_eq_getElem]
        exact B.last_inputState_eq_state
      rw [hA0, hB0]
    | succ d ih =>
      intro hd
      have hIH := ih (by omega)
      rw [List.get_eq_getElem, List.get_eq_getElem] at hIH
      have hkA : A.outputState.length - (d + 1) < A.outputState.length := by omega
      have hkAi : A.outputState.length - (d + 1) < A.inputState.length := by omega
      have hkB : B.outputState.length - (d + 1) < B.outputState.length := by omega
      have hkBi : B.outputState.length - (d + 1) < B.inputState.length := by omega
      have hmemA := fwdStep_mem (trace := trace) (state := state) h S_BT hA
        (A.outputState.length - (d + 1)) hkA hkAi
      have hmemB := fwdStep_mem (trace := trace) (state := state) h S_BT hB
        (B.outputState.length - (d + 1)) hkB hkBi
      have chA : A.outputState[A.outputState.length - (d + 1)].capacitySegment
          = A.inputState[A.outputState.length - (d + 1) + 1].capacitySegment :=
        A.capacitySegment_output_eq_input ⟨A.outputState.length - (d + 1), hkA⟩
      have chB : B.outputState[B.outputState.length - (d + 1)].capacitySegment
          = B.inputState[B.outputState.length - (d + 1) + 1].capacitySegment :=
        B.capacitySegment_output_eq_input ⟨B.outputState.length - (d + 1), hkB⟩
      have hidxA : A.inputState[A.outputState.length - (d + 1) + 1].capacitySegment
          = A.inputState[A.outputState.length - d].capacitySegment :=
        inputCap_congr (by omega) (by omega) (by omega)
      have hidxB : B.inputState[B.outputState.length - (d + 1) + 1].capacitySegment
          = B.inputState[B.outputState.length - d].capacitySegment :=
        inputCap_congr (by omega) (by omega) (by omega)
      have hcapeq : answerCap (⟨.inr (.inl A.inputState[A.outputState.length - (d + 1)]),
            A.outputState[A.outputState.length - (d + 1)]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U))
          = answerCap (⟨.inr (.inl B.inputState[B.outputState.length - (d + 1)]),
            B.outputState[B.outputState.length - (d + 1)]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
        change A.outputState[A.outputState.length - (d + 1)].capacitySegment
          = B.outputState[B.outputState.length - (d + 1)].capacitySegment
        rw [chA, chB, hidxA, hidxB]
        exact congrArg _ hIH
      have he := eq_of_answerCap_eq trace hdup hmemA hmemB hcapeq
      rw [List.get_eq_getElem, List.get_eq_getElem]
      exact (fwdEntry_inj he).1
  -- Step 2: equal lengths.
  have hmeq : A.outputState.length = B.outputState.length := by
    rcases eq_or_lt_of_le hmle with heq | hlt
    · exact heq
    · exfalso
      have hb := bdet A.outputState.length (le_refl _)
      rw [List.get_eq_getElem, List.get_eq_getElem] at hb
      have hposA : 0 < A.inputState.length := by omega
      have hmemH := hashAnchor_mem (trace := trace) (state := state) A hposA
      have hkB' : B.outputState.length - A.outputState.length - 1 < B.outputState.length := by omega
      have hkB'i : B.outputState.length - A.outputState.length - 1 < B.inputState.length := by omega
      have hmemS := fwdStep_mem (trace := trace) (state := state) h S_BT hB
        (B.outputState.length - A.outputState.length - 1) hkB' hkB'i
      have chB : B.outputState[B.outputState.length - A.outputState.length - 1].capacitySegment
          = B.inputState[B.outputState.length - A.outputState.length - 1 + 1].capacitySegment :=
        B.capacitySegment_output_eq_input ⟨_, hkB'⟩
      have hidxB : B.inputState[B.outputState.length - A.outputState.length - 1 + 1].capacitySegment
          = B.inputState[B.outputState.length - A.outputState.length].capacitySegment :=
        inputCap_congr (by omega) (by omega) (by omega)
      have hidxA : A.inputState[0].capacitySegment
          = A.inputState[A.outputState.length - A.outputState.length].capacitySegment :=
        inputCap_congr (by omega) (by omega) (by omega)
      have hcapeq : answerCap (⟨.inl A.stmt, Vector.drop (A.inputState[0]'hposA) SpongeSize.R⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U))
          = answerCap (⟨.inr (.inl B.inputState[B.outputState.length - A.outputState.length - 1]),
            B.outputState[B.outputState.length - A.outputState.length - 1]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
        change Vector.drop (A.inputState[0]'hposA) SpongeSize.R
          = B.outputState[B.outputState.length - A.outputState.length - 1].capacitySegment
        calc Vector.drop (A.inputState[0]'hposA) SpongeSize.R
            = A.inputState[0].capacitySegment := rfl
          _ = A.inputState[A.outputState.length - A.outputState.length].capacitySegment := hidxA
          _ = B.inputState[B.outputState.length - A.outputState.length].capacitySegment :=
              congrArg _ hb
          _ = B.inputState[B.outputState.length - A.outputState.length - 1 + 1].capacitySegment :=
              hidxB.symm
          _ = B.outputState[B.outputState.length - A.outputState.length - 1].capacitySegment :=
              chB.symm
      have he := eq_of_answerCap_eq trace hdup hmemH hmemS hcapeq
      simp at he
  -- Step 3: input states coincide.
  have hin : A.inputState = B.inputState := by
    apply List.ext_getElem
    · rw [hAlen, hBlen, hmeq]
    · intro i h1 h2
      have hbd := bdet (A.outputState.length - i) (by omega)
      rw [List.get_eq_getElem, List.get_eq_getElem] at hbd
      calc A.inputState[i]
          = A.inputState[A.outputState.length - (A.outputState.length - i)] :=
            getElem_idx_congr h1 (by omega) (by omega)
        _ = B.inputState[B.outputState.length - (A.outputState.length - i)] := hbd
        _ = B.inputState[i] := getElem_idx_congr (by omega) h2 (by omega)
  -- Step 4: statements coincide.
  have hstmt : A.stmt = B.stmt := by
    by_contra hne
    have hposA : 0 < A.inputState.length := by omega
    have hposB : 0 < B.inputState.length := by omega
    have hmemA := hashAnchor_mem (trace := trace) (state := state) A hposA
    have hmemB := hashAnchor_mem (trace := trace) (state := state) B hposB
    have hin0 : A.inputState[0]'hposA = B.inputState[0]'hposB :=
      getElem_listEq hin hposA hposB
    have hcapeq : answerCap (⟨.inl A.stmt, Vector.drop (A.inputState[0]'hposA) SpongeSize.R⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U))
        = answerCap ⟨.inl B.stmt, Vector.drop (B.inputState[0]'hposB) SpongeSize.R⟩ := by
      change Vector.drop (A.inputState[0]'hposA) SpongeSize.R
        = Vector.drop (B.inputState[0]'hposB) SpongeSize.R
      exact congrArg (fun x => Vector.drop x SpongeSize.R) hin0
    have he := eq_of_answerCap_eq trace hdup hmemA hmemB hcapeq
    simp only [Sigma.mk.injEq, Sum.inl.injEq] at he
    exact hne he.1
  -- Step 5: output states coincide.
  have hout : A.outputState = B.outputState := by
    apply List.ext_getElem
    · rw [hmeq]
    · intro i h1 h2
      have hiAi : i < A.inputState.length := by omega
      have hiB : i < B.outputState.length := by omega
      have hiBi : i < B.inputState.length := by omega
      have hmemA := fwdStep_mem (trace := trace) (state := state) h S_BT hA i h1 hiAi
      have hmemB := fwdStep_mem (trace := trace) (state := state) h S_BT hB i hiB hiBi
      have chA : A.outputState[i].capacitySegment = A.inputState[i + 1].capacitySegment :=
        A.capacitySegment_output_eq_input ⟨i, h1⟩
      have chB : B.outputState[i].capacitySegment = B.inputState[i + 1].capacitySegment :=
        B.capacitySegment_output_eq_input ⟨i, hiB⟩
      have hcapeq : answerCap (⟨.inr (.inl A.inputState[i]), A.outputState[i]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U))
          = answerCap (⟨.inr (.inl B.inputState[i]), B.outputState[i]⟩ :
            Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
        change A.outputState[i].capacitySegment = B.outputState[i].capacitySegment
        rw [chA, chB]
        exact congrArg (fun x => x.capacitySegment)
          (getElem_listEq hin (i := i + 1) (by omega) (by omega))
      have he := eq_of_answerCap_eq trace hdup hmemA hmemB hcapeq
      exact (fwdEntry_inj he).2
  exact Backtrack.BacktrackSequence.ext hstmt hin hout

/-- CO25 Lemma 5.14 — If `E(tr) = 0` then `E_fork(tr, s) = 0`. -/
lemma lemma_5_14 (h : ¬ E trace)
    (S_BT : Backtrack.S_BT trace state) :
    ¬ E_fork trace state S_BT := by
  rw [E_fork, not_lt, Finset.card_le_one]
  intro A hA B hB
  rcases le_total A.outputState.length B.outputState.length with hle | hle
  · exact bt_seq_eq_of_le (trace := trace) (state := state) h S_BT hA hB hle
  · exact (bt_seq_eq_of_le (trace := trace) (state := state) h S_BT hB hA hle).symm

end Def513_Lemma514

/-! ## Lemma 5.16 -/
section Def515_Lemma516

/-- CO25 Definition 5.15 / Eq. 41 — `E_{time,h}(tr, s)`: the query to `h` is out of order.
There exists `J^{(k)} = (j_h^{(k)}, j_0^{(k)}, …, j_{m_k}^{(k)}) ∈ 𝒥_BT(tr, s)` with
`j_h^{(k)} > j_0^{(k)}`. -/
def E_time_h (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ p ∈ Backtrack.J_BT S_BT,
    p.2.1.val > (p.2.2 ⟨0, by
      have := p.1.inputState_length_eq_outputState_length_succ; omega⟩).val

/-- CO25 Definition 5.15 / Eq. 42 — `E_{time,p}(tr, s)`: a query to `p` is out of order.
There exists `J^{(k)} ∈ 𝒥_BT(tr, s)` and `ι ∈ [m_k - 1]` (paper notation: `{1, …, m_k - 1}`)
with `j_{ι-1}^{(k)} > j_ι^{(k)}`, i.e. some consecutive pair of permutation-step `j`-indices is
out of order.  In 0-based indexing this checks `j_ι > j_{ι+1}` for `ι ∈ {0, …, m_k - 2}`. -/
def E_time_p (S_BT : Backtrack.S_BT trace state) : Prop :=
  ∃ p ∈ Backtrack.J_BT S_BT,
  ∃ ι : Fin p.1.outputState.length,
    ι.val + 1 < p.1.outputState.length ∧
    (p.2.2 ⟨ι.val, by
      have := p.1.inputState_length_eq_outputState_length_succ
      have := ι.isLt; omega⟩).val >
    (p.2.2 ⟨ι.val + 1, by
      have := p.1.inputState_length_eq_outputState_length_succ
      have := ι.isLt; omega⟩).val

/-- CO25 Definition 5.15 — `E_time(tr, s)` -/
def E_time (S_BT : Backtrack.S_BT trace state) : Prop :=
  E_time_h trace state S_BT ∨ E_time_p trace state S_BT

/-- CO25 Lemma 5.16 — If `E(tr) = 0` then `E_time(tr, s) = 0`.

Patch §5.4: by Lemma 5.12 every step is forward (`p`), so each index points at a base `p` entry and
the hash index at a base `h` entry, in trace order = base order.  An out-of-order pair would make a
*later* base entry's answer capacity equal an *earlier* base entry's query capacity (via the chain
condition / hash anchor), contradicting (B2). -/
lemma lemma_5_16 (h : ¬ E trace)
    (S_BT : Backtrack.S_BT trace state) :
    ¬ E_time trace state S_BT := by
  classical
  have hdup : ¬ capacitySegmentDup trace := not_E_dup_of_not_E trace h
  rintro (htime | htime)
  · -- `E_time_h`: the hash query `j_h` is later than the step-0 query `j_0`.
    obtain ⟨p, hp, hgt⟩ := htime
    obtain ⟨seq, hseq, rfl⟩ := Finset.mem_image.mp hp
    have hpos : 0 < seq.inputState.length := by
      have := seq.inputState_length_eq_outputState_length_succ; omega
    by_cases h0 : 0 < seq.outputState.length
    · -- Step 0 exists; collide its query capacity with the hash anchor's answer capacity.
      obtain ⟨i0, hi0val, hi0eq⟩ := fwdStep_base (trace := trace) (state := state) h S_BT hseq 0 h0 hpos
      obtain ⟨iH, hiHval, hiHeq⟩ := hashAnchor_base (trace := trace) (state := state) seq hpos
      have hij : i0 ≤ iH := by
        have h1 : i0.val ≤ iH.val := by
          rw [hi0val, hiHval]; exact getBaseTrace_take_length_mono trace (le_of_lt hgt)
        exact h1
      refine answerCap_ne_queryCap_le trace hdup hij
        (c := seq.inputState[0].capacitySegment) ?_ ?_
      · rw [hi0eq]; rfl
      · rw [hiHeq]; simp only [answerCap, CanonicalSpongeState.capacitySegment]
    · -- No steps: `j_0 = |trace|`, but `j_h < |trace|`, so `j_h > j_0` is impossible.
      exfalso
      rw [Backtrack.BacktrackSequence.Index_snd_eq_length seq (by omega) hpos] at hgt
      exact absurd hgt (by have := (Backtrack.BacktrackSequence.Index trace state seq).1.isLt; omega)
  · -- `E_time_p`: step `ι` query is later than step `ι+1` query.
    obtain ⟨p, hp, ι, hι1, hgt⟩ := htime
    obtain ⟨seq, hseq, rfl⟩ := Finset.mem_image.mp hp
    have hlen : seq.inputState.length = seq.outputState.length + 1 :=
      seq.inputState_length_eq_outputState_length_succ
    have hιlt : ι.val < seq.outputState.length := ι.isLt
    have hι1' : ι.val + 1 < seq.outputState.length := hι1
    have hkiι : ι.val < seq.inputState.length := by omega
    have hkiι1 : ι.val + 1 < seq.inputState.length := by omega
    obtain ⟨iIdx, hival, hieq⟩ :=
      fwdStep_base (trace := trace) (state := state) h S_BT hseq (ι.val + 1) hι1' hkiι1
    obtain ⟨jIdx, hjval, hjeq⟩ :=
      fwdStep_base (trace := trace) (state := state) h S_BT hseq ι.val hιlt hkiι
    have hij : iIdx ≤ jIdx := by
      have h1 : iIdx.val ≤ jIdx.val := by
        rw [hival, hjval]; exact getBaseTrace_take_length_mono trace (le_of_lt hgt)
      exact h1
    refine answerCap_ne_queryCap_le trace hdup hij
      (c := seq.inputState[ι.val + 1].capacitySegment) ?_ ?_
    · rw [hieq]; rfl
    · rw [hjeq]; simp only [answerCap]
      exact seq.capacitySegment_output_eq_input ⟨ι.val, hιlt⟩

end Def515_Lemma516

end BadEventDS

end DuplexSpongeFS
