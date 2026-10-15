# Global memo tables through current class scans

The source is main `2ca1644c`, merged at `a7134ecb`.
Full library scope remains active. The optimized interned core remains.
Earlier proof definitions, counterexamples, and marked drafts remain.

## Actual operation receipts

`SourceClassQueryGlobalMemos` passes the same three global gate tables
through actual Fold and rotated Seeded operations. Projection can extend
the unfolding table. Native scoped requests derive their primitive event
traces and the absence of global unfolding calls. Both query tables retain
their exact contents through the fold. The empty seeded case retains all
three tables.

The fold has two domains. Closed captured forests use `fold_closed_memos`.
Current anchored path support uses `fold_memos`. The second domain permits
unrelated original children to remain open. Neither theorem assumes a
final table invariant or the absence of actual native memo calls.

`SourceTaskQueryGlobalMemos` records delayed Force, Expose, and Run calls.
A first force executes its captured fold. A completed hit retains the
tables. Exposure records actual nodeEdges read calls before pure task
capture. Every reached worklist branch passes its returned tables to the
next operation. Initial task readiness derives captured forest closure.

`SourceDecisionGlobalMemos` records the closed body, current initial free
guard, and separate fourth-memo lookup. A hit skips the body. A miss
executes the current body before saving its Boolean. The three gate tables,
fourth Boolean memo, and native node/edge request tables remain distinct.

## Current query and scan composition

`SourceCurrentClassQueryGlobalMemos.QueryReads` records the current
secondary gate, actual Seeded fold, and actual fourth-memo call in order.
Each operation receives the exact tables returned by the previous operation.
`query_memos` derives their final coherence from the initial invariants.

`SourceCurrentClassScanGlobalMemos.ScanReads` follows all five actual Scan
branches. A selected class retains its primary calls. A skipped class
retains primary and secondary calls. A continued class also retains its
query calls before the suffix. A stopped class has no suffix receipt.
The nested heap advances retain the original native request tables.

`scan_memos` assumes an actual current Scan, initial readiness, available
original values, costs, normalized fields, coherent initial memo tables,
and nonempty paths in every original class. It returns actual ordered
ScanReads, final three-table coherence, final readiness, costs, fields,
original heap retention, original value availability, fourth-memo coherence,
and retention of earlier fourth-memo entries.

No accepted term, ClassSat, Satisfies, future readiness, or future table
validity is supplied to this theorem. Proper paths derive anchored support
from the actual current secondary gate. This is a completed-execution
effect theorem. It does not prove that every source caller completes.
The full scan theorem does not claim an entry-extension law for all three
global tables. Reached gate calls can change their query tables.

`SourceCurrentClassEntryGlobalMemos.live_proper` derives proper paths from
the actual cached equality accessor and live precheck. Cached classes are
active and contradiction-free. The original record sort preserves their
membership. This proof needs no accepted candidate or record-coherence
premise. `live_memos` applies the complete memo scan theorem at that entry
without a separate proper-path premise.

## Remaining scope

Extract the physical class/trie records and derive initial caller invariants.
Then compose selected requireAll, class reduction, and empty propagation.
General constrained completion and checked native transfer remain open.

Completed operation receipts do not establish GHC producer demand, row
sharing, original child forcing, pending memo publication, or concurrent
ownership. Native containers, machine bounds, and identity representation
remain separate bridges. Whole enumeration and shared reaches-helper
effects remain open.

Keep the representative waiting-count, template exclusion, typed derived
refinement, and broader API obligations. Keep the separate exact Sized
class, execution, order, enumeration, and inverse contracts. Exact graph
query proofs do not establish their concrete lazy runtime correspondence.

## Validation

The pinned focused entry build passes 1,154 jobs. The aggregate build passes
2,105 jobs and 52,700 theorem dependency checks. Public theorem axiom probes
and the full audit use only propext, Classical.choice, and Quot.sound.
No new warning occurs. Eight new modules and four additive Audit imports
contain the proof change. HANDOFF.md records the preservation result.
Evidence uses `/tmp/mcfta-query-global-*`.

The required strict Nix build and all six suites pass after the source
merge. They cover 720 examples plus golden checks. Changed-file Fourmolu
and all four active package Cabal-gild checks pass. No Haskell file changes
after that validation.
