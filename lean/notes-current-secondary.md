# Current secondary gate and caller composition

Source main is `7fdebd07`, merged at `a3e68610`.
The secondary rule was introduced in main `88998669`.
Proof commits are `0992b336`, `3e797a74`, and `3be3967c`.
Read [the typed API source boundary](notes-main-7fdebd07.md).
Full library scope and the optimized interned core remain active.

## Exact execution and completion

`SourceCurrentSecondaryTrace` follows the complete current secondary worker.
Its Node, Child, Edges, Path, and Class graphs retain the actual unfoldings,
ordered short circuits, and complete intermediate constructor heaps.
A constrained Mu endpoint returns false exactly when its free list is empty.
A constrained Mu inside a path still returns true.

All five graph endpoints have finite execution and completed-run extraction.
The node and class endpoints have uniqueness proofs. Exact full-outcome
adapters omit the disabled descendant argument at every fuel.
`SourceCurrentSecondaryCompletion` derives finite stable node, path, and
class checks from certified inputs. Its open-Mu calls use the actual strict
unfolding rank. Original closed construction derives the input certificates.
This is gate completion. It does not prove whole-caller completion.

## Heap and memo effects

`SourceCurrentSecondaryReplay` derives semantic readiness, both heap
histories, and exact replay above the completed final heap.
`SourceCurrentSecondaryEffects` also retains costs and edge annotations.
Ordered false siblings use each preceding returned heap.

`SourceCurrentSecondaryMemos` derives actual predicate and unfolding calls
for each demanded node, child, edge, path, and class. The descendant table
is unchanged. The other two tables retain every earlier completed entry.
Current coherence derives later hit or miss receipts. No future-validity
premise is supplied. Certified inputs derive stable finite class checks with
these receipts. Original closed construction derives initial node receipts
from empty tables.

## Selected projection

The seven `SourceCurrentSecondaryProjection*` modules retain current false
certificates at one final anchor. Closed constrained Mu endpoints use their
actual free-list test. Open plain Mu calls retain actual unfoldings.
The head worklist proofs are independent of the old secondary policy.

Selected children retain shorter support through actual epsilon origins,
complete row reads, and canonical head reconstruction. Root-path support
derives original closedness. Proper forest paths require support only for
the selected original child. They do not require unrelated siblings closed.
Actual later projection has derived finite execution, closed output,
accepted-subterm inclusion, and retained annotations and native invariants.

## Current query, fourth memo, and reached scan

`SourceCurrentSecondaryClassFold` derives effects, accepted-subterm inclusion,
and retained annotations through the actual Fold and rotated Seeded schedules.
`SourceCurrentSecondaryQueryCosts` retains costs through projection, native
requests, the current initial free-list guard, and fourth-memo hits or misses.
`SourceCurrentSecondaryRefusedClassQuery` derives a strictly smaller common
accepted subtree from a satisfied active original class. A true actual body
or memo answer excludes that subtree.

`SourceCurrentSecondaryQueryReady` derives each query invariant from the
actual current false class anchor and initial caller invariants. It retains
fourth-memo coherence through the gates and seeded query. No whole-original-
forest closedness, reached-ready oracle, or supplied final invariant is used.
Actual native and completed exploration receipts remain explicit.

`SourceCurrentEqualityClassScan` records only reached original classes.
A clear primary selects; a blocked primary runs the current secondary.
A clear secondary runs Seeded and the actual fourth-memo lookup.
A false answer passes the returned memo to the next class. A true answer
stops without receipts for later classes. Original order and multiplicity
are retained.

`SourceCurrentEqualityClassScanSoundness.verified` derives all intermediate
readiness, costs, fields, value retention, fourth-memo coherence, and saved
entries under independent acceptance and satisfaction of active original
classes. Such a candidate cannot reach early rejection. `stopped_refutes`
proves the corresponding exclusion. `SourceCurrentEqualityClassEntry`
connects the unchanged live precheck to the original equality accessor.
Coherent records and actual accessor readback remain explicit. The proof
does not extract native physical records or construct the initial caller.
False memo answers do not prove nonemptiness or completeness.

## Remaining scope

The same three global gate tables must still compose through actual
Fold/Seeded, delayed Force/Expose/Run/Decision, the fourth memo, and Scan.
The new individual gate receipts and older projection/native receipts are
proved. Their whole-query composition remains open. Do not replace actual
calls with an assumed final table invariant or a table-silence predicate.
Native physical class/trie extraction, initial caller construction, and the
selected requireAll/class reduction/empty propagation fallback remain.
Full enumeration wiring and shared reaches-helper memo effects remain.

GHC producer demand, row sharing, original child forcing, publication,
checked native state, word bounds, and general completion remain separate.
Keep all waiting-count, template exclusion, typed refinement, broader API,
and exact Sized obligations. Exact Sized algorithm proofs do not remove
host-container, lazy-runtime, machine-conversion, or external IO boundaries.

## Validation

The pinned aggregate audit passes 2,097 jobs and 52,633 theorem dependency
checks. Only propext, Classical.choice, and Quot.sound occur. No new warning
occurs. Nineteen new modules and two additive Audit imports contain the
proof change. All 2,077 earlier non-Audit proof files remain byte-identical.

Required Nix validation after the source merge passes the strict build and
all six suites, 714 examples plus golden. Five changed Haskell files pass
Fourmolu. All four active package files pass Cabal-gild.
Logs, source copies, and source reviews use `/tmp/mcfta-current-secondary-*`.

Start: `/tmp/mcfta-main-889-checkpoint-20261015-2122/` (2,751 files).
Closing: `/tmp/mcfta-current-secondary-checkpoint-20261015-2148/` (2,774 files).
Script: `/tmp/mcfta-preserve-current-secondary-20261015.py`.
All prior artifacts, external drafts, stashes, and other worktrees remain.
Weekly allowance is 83%. Stop owned work at 1% or less. Do not post to the
board or deploy. Push verified formalize checkpoints.
