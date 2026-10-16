# Current plain parent and edge-call completion

Source main is `c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e`.
It was merged at `896b0a1cb36c58531ee24c5b4edfff0e935111c6`.
This checkpoint starts at `8906d5e687b7a62ddf42bb8c25a489a23ffec398`.
The evidence directory is `lean/restart-evidence/20261016-parent-plain/`.
Proof commits are `db438c0b` (full ranges), `b7fd0ee5` (returned domain),
`3f817e89` (parent completion), `96a1afee` (owner inputs), and
`6bbf2ee0` (outer edge-call completion).

## Objective and current boundary

The full objective is implementation correspondence for the whole library.
It includes accepted languages, transformation contracts, exact size classes,
finite execution, counts, enumeration order, both rank/unrank inverses,
and probability laws. Frontends, runtime behavior, and full-pipeline
composition remain part of that objective.

The constructed-root theorem already supplies initial Context from covered
construction. Its exact-language conclusion still requires literal worker
success and reached machine checks. The new theorem constructs finite
execution for the current outer edge-call family in the plain domain.
It does not yet construct the complete recursive root execution.

## Five additive modules

`SourceCurrentAllocatedLocalPlainRanges` derives the complete finite range
plan from the actual field load and empty effective own equalities.
The proof inverts the nil Scan and retained records at the actual state.
It does not replace the full range predicate with a weaker projection.

`SourceCurrentAllocatedPartialReturnedDomain` defines a three-way child
Shape: original children, erased slots, or the singleton Empty sentinel.
Shape retains child Regions and bounds edge height. It does not assert
equal arity. A rejected nullary edge can return one Empty child.
Stored requires Shape for each returned edge cell relative to its stored
owner. Empty outer tables derive Stored. Actual begin, advance, and finish
preserve it, with Shape required only for the edge that is finished.

`SourceCurrentAllocatedParentPlain` constructs stable literal parent
execution, its own EdgeBody, strict Reads, full Post, and Shape.
The live guard needs empty effective own equalities. Raw contradiction
needs no field premise. Constructor rejection returns the Empty sentinel.
The actual resident load supplies the full range plan. A supplied literal
success has the same Shape by whole-return uniqueness.

`SourceCurrentAllocatedPartialPlainInputs` converts the physical own
accessor to effective source equalities. Positive guard extraction is
included. Empty stored payload alone is insufficient. Actual stored-owner
identity transfers input Regions and empty-own facts. A ready edge hit
derives Shape from the captured returned owner and coherent resident input.

`SourceCurrentAllocatedPartialPlainEdgeCall.finite` takes initial Context,
ready inherited constraints, resident input, the plain guard condition,
Stored, and ActiveAbove the request rank. It constructs stable literal
execution, its own EdgeCall, strict Reads, reached Checks, full Post,
result residency, Stored after, Shape, and EdgeLaw.
The evaluate branch runs the actual stored owner and finishes the exact
selected handle. The ready branch returns the unchanged full caller.
Neither branch takes future execution, a range plan, or a result law.

The edge memo stores the parent result before descendant processing.
Stored describes that result. A later descendant rebuild need not have
the same Shape relative to the original edge.

## Next proof

Construct finite node and descendant execution in the current plain Region.
Return the actual graph, strict Reads, Checks, Post, and Stored at every
prefix. Then compose the result with the constructed-root theorem.
Read `region-next-review.md` in the evidence directory first.

EdgeCall completion now needs no recursive outer call. One possible proof
uses strong induction on nodeRank and finite recursion over rows and
children. In an ordinary node of rank R, every original edge has rank
below R. A running node can retain ActiveAbove (R - 1) across all rows.
Each edge call uses the corresponding weaker bound. Its completed active
frame restores the original bound for the next prefix. Shape supplies
Region and a strictly smaller node rank for each returned child. The node
induction hypothesis can then process that child. This outline remains
unimplemented. Public endpoints must discharge the induction hypothesis.

Mu and union are opaque Region terminals. Mu cleanup can remove an unused
binder. Do not require Region of every returned node without a separate
proof. The current pass does not traverse that returned terminal again.

General constrained completion outside Region remains open. Unequal-length
path classes and repeated-pass convergence remain open. The current worker
performs one pass. Logical Reads do not prove GHC demand, host publication,
shared warm initialization, or the noConstraint CAF. Current frontend
adapters, exact query composition, generators, probability, solver and
random-source assumptions, callbacks, and codecs still need full coverage.
Preserve the optimized interned core and all older constructor/equality work.

## Validation and source repair handoff

The pinned full Audit passes 2485 jobs and 58868 dependency checks.
The existing unused-input warning is unchanged. Public axiom and signature
probes and integration kernels are retained with their terminal logs.
All 5648 starting tracked files remain. All 2479 older non-Audit proof
sources retain their bytes. Thirty-one frozen manifests check 242 module
entries. Historical repairs, stashes, and three other worktrees remain.

This checkpoint changes no Haskell file. Reuse the strict Nix build,
798 examples plus golden, six-file Fourmolu, and four-package Cabal-gild
and metadata checks for source `c0cc8a05`. Root `FINDINGS.md` keeps the
external Haskell repair handoff first. It records failure, executable
reproducer, affected paths, commit, checks, and upstream status for each
repair. No outstanding local Haskell behavior patch is introduced.
