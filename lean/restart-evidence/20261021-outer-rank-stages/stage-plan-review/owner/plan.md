# Numeric coverage at every finite envelope stage

This plan proposes one theorem in a separate `SourceCurrentOuterRankEnvelopeStages` module.
Its public `stage_bounds` header is the unchanged last 34 lines of the original 42-line proposal.
It imports the checked 157-line `SourceCurrentOuterRankEnvelope` at SHA `b8401732ae63be4d2036ccd4af7997b787ced8787789a1fb9d2e354047fde5ba`.
Root reports strict and Audit success and proof commit `ccaa8719d37d46dcf9073679c0fab56efdbb98f8`.
The existing definition and all frozen packages stay unchanged.

A private one-rank equality must expand the PUBLIC `envelope`, apply `WellFounded.fix_eq`, and identify its recursive values with the same public envelope.
It must not name the imported module's private declarations or define a second well-founded envelope.
The precise attached-list and pair-equality route is in `one-rank-unfold.md`.
Private finite abbreviations may denote only the header's literal images, slot step, and row step.

Use one private four-component comparison on `Out`: work, lower fuel, profile `Le`, and alphabet inclusion.
A short list induction transports that comparison and adds the list length to work when each step adds at least one.
`range_add`, `foldl_append`, and `foldl_map` split the SAME row or slot fold at a literal prefix; the callbacks ignore their numeric indices.
The Parent output fixes the entire row's slot limit B. Every slot recomputes candidate images at its CURRENT seed.
The proof does not compare envelopes evaluated at different seeds.

For row j<mass, the prior work is at least j. One row retains its Parent need, Parent seed, and every slot prefix; later rows retain those quantities.
For k<=B, current work is at least k, and the total work is at least prior work plus current work plus two.
For k<B, every allowed smaller rank occurs in the current images by range and filter membership.
`maximum_member`, `cover_member`, and literal append/flatMap membership bound that candidate's work, lower fuel, profile, and alphabet in the next slot.
Splitting at k+1 then transports those bounds through the SAME remaining slots and rows.
The selected child's work plus 3+j+k fits total work. This matches the literal worker offsets; no child activation is asserted.

The detailed source budget is 225-250 rendered lines, with a HARD STOP at 250 before any compiler or further implementation.
The budget is a design estimate. An actual partial source must stop and return for scope review if it does not fit.
This task authorizes only this source plan. It authorizes no implementation, compiler, runtime evaluation, official edit, or board action.

All results are pure numeric facts about the defined finite folds.
Same-global-root resource coverage, actual intermediate Parent peaks, actual nested lower fuels, capacity, and adequate outer fuel remain unproved.
Authored foundations: the checked envelope and earlier native/prefix/closure components. This is not an independent review of those proofs.
