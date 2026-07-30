# WIP plan: IPA PCS opening and tree-SS⇒KS adapter

Nothing in this draft is proved or build-verified. The Lean file contains signatures with `sorry`,
and its #530 names require rebasing that coordinate-wise transcript-tree work onto the PR #3 base.

## Opening/extraction boundary

`OpeningStatement` exposes the commitment, evaluation point, and claimed value;
`OpeningWitness` exposes the polynomial representation and commitment blinding. The abstract
`openingRelation` is the sole algebraic boundary: the witness must recompute the commitment and the
claimed evaluation. `openingVerifier` will later fix the IPA round messages, challenges, folding
equations, and final check without embedding extraction into verification.

The protocol-specific proof ends at `opening_treeSpecialSound`: from an accepting challenge tree it
must recover an opening witness satisfying `openingRelation`. The generic probabilistic adapter
starts from that theorem and must not recompute a witness at the verifier boundary.

## Arity-five #530 instantiation

The intended shape is `distinctShape arityFive`, where `arityFive` maps every challenge coordinate
to `5`. Thus each verifier challenge node has five children and #530's `nodeOk` obligation is
pairwise distinctness of those five sibling challenges. The proof must establish the IPA folding
system has enough independent equations at every coordinate and then solve for the pre-fold witness.

## PR #3 reuse

The adapter will translate #530's accepting `ChallengeTree` into PR #3's descending/flat
`TranscriptForest`, preserving sibling distinctness and the verifier acceptance invariant. It will
reuse `Rewinding` for the extractor program, `TwoFactorRun` for ownership-separated randomness,
`TreeExtraction` for the arity/depth error and draw-cost accounting, and the forest definitions for
the extracted transcript carrier. No second rewinding game should be introduced.

## Remaining proof steps

1. Rebase/merge #530 into `feat/rewinding-knowledge-soundness`, then adjust the skeleton to the
   resulting `ChallengeTreeShape`, `distinctShape`, and `treeSpecialSound` APIs.
2. Choose the concrete group, scalar-field, polynomial, commitment, transcript, and round-index
   representations and implement the honest IPA prover/verifier.
3. Prove completeness and the per-round folding identities.
4. Build the deterministic algebraic extractor for an accepting arity-five distinct tree and prove
   that its output satisfies `openingRelation`.
5. Prove the `ChallengeTree`/`TranscriptForest` preservation lemmas for structure, acceptance, and
   extracted witness.
6. Instantiate PR #3's rewinding theorem, discharge challenge-cardinality hypotheses, and derive
   the advertised knowledge error and expected-query bound.
7. Remove every `sorry`, run the targeted validation/build, and only then claim compilation or
   knowledge soundness.
