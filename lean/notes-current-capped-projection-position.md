# Positive paths through actual capped projection and reads

This checkpoint proves a local observation inverse.
It does not prove complete class transport or outer completion.
It complements the existing actual native-request support theorem.

## Public statements

`SourceCurrentCappedProjectionPositivePosition.root` consumes
Project(path.map Int.ofNat) value before result after and the SAME later
complete Read result reader rows readAfter. A nonplain selected row at the
given row index implies PositiveAt value path.

`child` uses the SAME project, read, selected row and row index.
For row.children[childIndex] = child and PositiveAt child residual, it derives
PositiveAt value (path ++ childIndex :: residual).
The selected row can have a plain root guard. This covers the descendant
case that a root-only observation theorem misses.

Both statements require entry SemanticReady, CostHeap, Available and
GuardHeap Plain; reader SemanticReady and GuardHeap Plain; Keeps from the
projection finish to the reader; and a finite Plain cap on value.
There is no closedness premise or reader-cost premise.
The statements consume actual successful calls. They do not assert future
projection or read completion.

## Proof

The proof follows the actual read collector, selected full row, ordered
children and actual indexed projection spine. Ordinary reconstruction uses
its original row, selected child and exact smaller projection/read interval.
The proof derives semantic, cost, availability, guard and Keeps facts at
each actual intermediate cut.

Unions consume no natural child index.
A union Head can expose nonplain members. The proof retains their actual
collector membership and maps the positive occurrence back to that member.

A finite Plain cap forces a Mu value to have hereditary Plain annotations.
Actual unfolding preserves those annotations using its real stored
substitution. The full actual read annotation excludes both nonplain roots
and positive descendants. The proof does not equate an actual Mu read with
nodeEdges of a Mu, which is empty.

Root rows, including nullary rows, add no natural child index.
Ordinary child steps retain the same ordered index.
Natural path mapping is converted exactly through Int.ofNat and Int.toNat.
A private RowPositive predicate combines the two proof cases.
It does not appear in either public type.

## Scope and next step

The next local producer must derive a projected endpoint cap from the
ORIGINAL false gate and actual Required Origin. Its empty-path base can
reuse PrimaryEndpointCap.endpoint_cap. The new proof must retain the same
ordinary child and required row origins without capping unrelated siblings.

The native request theorem already derives a same-path OR-input law and a
finite cap for its returned value. A continuation consumer must apply that law
to the SAME actual projected return and selected read, using the native
Return as the cap producer. It must retain the query, writer and reader cuts.
No assumed future result law can replace this composition.

The existing PrimaryEndpointCap.endpoint_cap derives a finite cap from an
actual false endpoint gate at its original heap. A nonempty path gate does
not cap unrelated siblings. The missing class proof must retain the required
endpoint relationship through changed phaseValues and actual class edits.
Safe True at an endpoint drops relevant descendant restrictions.
Original false gates remain facts about their original captures.

Selected-observation class composition, endpoint barriers, the retained pair
or owner exclusion, general renewal, final retention, outer completion,
convergence and Haskell correspondence remain open.
The unrestricted opaque-Mu counterexample is retained.

## Validation and preservation

The final source has 264 lines and SHA-256
`7876487f3271323b0140187bf14ef84cfd23e22d88ff52175c04018ccd8ca436`.
Root strict checking has an empty log.
Full root and child readback uses all eight settings with no omitted proof.
Both heads report only propext, Classical.choice and Quot.sound.
Independent review reads the full source and the final changes.

The owner performs six Lean jobs, with four retained failed attempts.
Root strict and the default Audit add two jobs.
The total is eight actual Lean/Lake jobs and four nonzero exits.
Copies, reviews and plans add no proof jobs.

All earlier proofs, evidence, frozen registries, Haskell and package files,
stashes, other worktrees and main are preserved.
FINDINGS retains the external Haskell repair registry first.
There is no Haskell defect, source change or repair in this checkpoint.


Selected proof: `a6a233865cbce79a192945051d9df448e7d0c364`. Updated: 2026-10-21 04:13 CEST.
Default Audit: 3567 jobs and 74724 theorem dependencies.
Actual Lean/Lake jobs: 8. Nonzero jobs: 4.
