# Checked edge allocation and recursive memo preservation

The [accepted child checkpoint](notes-native-accepted-child-demand.md),
`970ef848`, derives actual child traces and accepted edge receipts. General
node/Mu correctness and reached-child checks remain open. Its audit passes
1,965 jobs and 50,512 dependency checks. All Sized contracts and Haskell
sources remain unchanged. Older next targets below are historical.

The [checked provenance checkpoint](notes-native-checked-provenance.md),
`20982f98`, derives stopped native completion and outer memo Sound. Actual
finite heap Keeps follows from reached current-input checks. Accepted
recursive provenance and derivation of the input/field plans remain open.
Its audit passes 1,955 jobs and 50,413 dependency checks. All Sized contracts
and Haskell definitions remain unchanged. Older next targets are historical.

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Constructor proofs: `1fa17554`. Recursive integration and audit: `261627c4`.
This extends [equality payload allocation](notes-payload-allocation-receipts.md).
Production Haskell and all older proof definitions are unchanged.

## Resumable execution extension

The [native demand checkpoint](notes-native-checked-demand.md), `f4687ad9`,
connects these prefixes to typed native publication, delayed child code,
retained operation caches, stopped language, and surrounding recursive cells.
Its aggregate audit passes 1,945 jobs and 50,309 dependency checks. Completed
native semantic provenance and actual heap preservation are the next target.
Earlier next-target and validation statements below describe this note's
original checkpoint. The eager Produced relation remains separate.

## Raw conjunction

`SourceEqualityConjoinAllocation.Constraint` retains an allocated stored
physical value and the original guard. `readback` reads those raw fields.
It does not demand the full equality accessor. This matches
`Constraint.hs:216-222`.

`conjoin` combines the first stored value before the second through the
completed combination cache. It merges the original guards with the source
`GuardConjunction.merge`. `conjoin_correct` derives successful execution,
Ready output, valid growing operation state, and literal equality to
`SourceEqualityConstraintConstructors.conjoin`. Actual normalization derives
Cached output and a literal physical constructor receipt. Completed hits
retain the entire operation state.

Ready alone does not imply globally normalized arbitrary original class
lists. `construct_complete` and `original_of_receipt` use actual original
normalized field receipts. The conjunction language theorem uses Cached
original fields to derive the required active-class conditions.

## Checked constructor and sentinel

`SourceEqualityMkEdgeAllocation.check` first reads the stored contradiction
tag and outer Bottom guard. This branch retains the entire operation state.
Otherwise it demands the full accessor and checks arity at its returned state.
The source uses these distinct reads in `Type.hs:563-568` and
`Constraint.hs:121-136`.

`fits` uses the existing signed source arity test after natural-index casts.
`SourceEqualityMkEdgeArity.fits_exact` proves that each root path is permitted
and each nonempty path starts below the edge arity. All represented indexes
are nonnegative. Active satisfied classes pass the check. Complete public
constraint acceptance excludes stored contradiction and Bottom. It derives
actual check success. `build_of_source` derives the original complete edge
interner request at the represented term arity. Ready supplies the required
active-class premise. Heap child-language correspondence remains separate.

`build` retains accessor allocations even when it rejects an edge. It then
interns either the original complete fields or the empty-edge sentinel. The
sentinel is the source direct Edge constructor with Top, empty equalities,
and one EmptyNode child (`Type.hs:530-544`). Its strict noConstraint field can
first demand the canonical empty equality key. `emptyField_correct` derives
that actual interner receipt and Ready output. Both completed operation tables
remain intact. A previously stored empty key gives a read-only hit.

This empty-field receipt is required after constructor rejection. The
contradiction check itself still performs no allocation. The full rejected
constructor must not be described as an unchanged operation state.

## Native edge prefix and recursive state

`SourceEqualityIntersectionEdgeAllocation.run` checks input arity mismatch
before conjunction. Mismatch retains the entire operation state. Equal arity
runs actual raw conjunction and the full checked-constructor guard at its
returned state. It returns mismatch, rejected, or a ready combined constraint.
Every ready output retains Ready, Cached, and literal constructor receipts.
The branch readback equals the complete existing source checks. Rejected
branches retain every reached allocation. This prefix has no child values or
child callback.

The open edge worker uses the supplied operand order. The closed
`intersectEdgeSameSymbol` first swaps operands when the second edge sorts
before the first (`Operations.hs:358-373,529-550`). The prefix takes the
already selected actual order. It does not prove that outer ordering step.

`SourceEqualityPartialConjoinAllocation` fixes the actual structural guard
comparison and preserves current recursive result-memo Sound and Frame.
`SourceEqualityPartialMkEdgeAllocation` threads the returned equality state
and actual selected edge heap. Actual heap preservation retains each original
running request and completed result proof. `advanceHeap` retains the native
domain and both native memo tables.

`SourceEqualityPartialIntersectionAllocation` preserves current Sound and
Frame before child demand. Its separate empty-edge continuation demands the
empty stored field and interns the sentinel. It needs no child-demand premise.
These results do not assume future Sound. Full native Scope remains separate.

## Demand boundary and next target

Connect the ready prefix to delayed actual native child requests. The source
checked constructor can return its sentinel before demanding child results.
The older `SourceRecursiveIntersectionKernel.edge` instead walks child
callbacks before its direct makeEdge. No equality of those effects is proved.
Its earlier semantic and kernel results remain retained component evidence.
Do not use them as a complete GHC demand or physical allocation refinement.

Next add the concrete completed-operation state and checked constructor phase
to native edge execution. Retain node and edge memo publication, running and
returned phases, the actual operand order, errors, and incomplete observations.
Rejected branches must reach the sentinel without child callbacks. Ready
branches must carry operation state through actual child continuations.
Then connect this execution through selected class folds, reconstruction,
both gate memo families, the full guarded pass, complete recursive reduction,
and original graph construction. Do not assume equal nonmemoized replay effects.

Global unrelated result-memo history, pending operation thunks, source cache
and hash-library adequacy, IntMap representation, signed machine indexes,
the complete lifetime reservation bound, unsafe IO, and GHC execution remain
open. General caller completion, open contexts, repeated fixed points,
getAllAtPath, decision-model, named measures, parser/decoder bridges, and
extraction remain open. All distinct Sized contracts remain preserved.
Whole-library formalization is not complete.

## Validation

The pinned focused endpoint build passes 1,077 jobs:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceEqualityPartialIntersectionAllocation MicroCFTA.SourceEqualityPartialConjoinAllocation MicroCFTA.SourceEqualityMkEdgeArity
```

Log: `/tmp/mcfta-edge-allocation-focused-20261015.log`.
The aggregate build passes 1,936 jobs and checks 50,146 theorem dependencies.
Only propext, Classical.choice, and Quot.sound occur.
Log: `/tmp/mcfta-edge-allocation-audit-20261015.log`.
The old unused-input warning remains. The seven new modules have no warnings.
No Haskell file changed. Prior Nix, six-suite, format, metadata, and 205-rank
checks retain their prior source evidence and were not repeated.
