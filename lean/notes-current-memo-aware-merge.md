# Recursive memo-aware merge execution

The source is main `a4dd678f`. `Interned/Operations.hs` defines
`mergeAlternatives` through the symbol-scoped `genericMergeAlternativesCache`.
Both small-row children and retained ordinary-union operands call that
memoized function. The result cache is separate from the three global
unfolding and query tables.

## Actual recursive requests

`SourceCurrentMemoMergeGraph` defines typed source instructions and mutual
`Run` and `Call` relations. Each small child uses a literal request. A large
group selects each column before retained-column normalization. A retained
singleton returns directly. A recursive boundary uses the union constructor.
Other retained columns construct an ordinary union and request its merge.
The source threshold remains four rows. Group and child order remain explicit.
The body uses the existing canonical grouping model. Literal HashMap outer
group order and the resulting allocation order need a separate adapter.

A hit returns the complete stored result and skips the body. A miss executes
the memo-aware body. It then retains the first completed entry and rereads
the winner. The graph does not require that the key stays absent during the
body. The proof does not assume that the new candidate wins. Old entries
remain in the final result table.

## Physical effects and completion

`SourceCurrentMemoMergeEffects.Stored` requires each original and result to
be available at the physical heap. Its key is the original tagged reference.
A closed original requires a closed result. Open originals are permitted.
Physical reference coherence identifies a hit's stored original with the
actual argument. Empty tables derive this invariant directly.

The actual paired instruction and request induction derives heap retention,
semantic readiness, stored cost validity, resident results, and conditional
closedness. The instruction certificates check actual constructor effects
and returned continuations. They do not supply future cache validity.

`SourceCurrentMemoMergeCompletion.call_complete` constructs a finite call.
Every recursive small child and ordinary-union request has smaller ordinary
height than the parent closed ordinary call input. The measure applies
before cache lookup.
A cached result needs no height bound. That result enters reconstruction;
it does not introduce another recursive request at that level. Each selection
has its own finite comparison bound at its actual reached heap.

## Independent language and producer history

`SourceCurrentMemoMergeLanguageCertified` derives source body certificates
for the independent guarded language. Ordered maps retain paired input and
result records. Selection, union, edge, and node laws supply the local facts.
Recursive requests use the stronger physical and coverage contract.

`SourceCurrentMemoMergeLanguage.run_language` discharges that contract by
actual mutual `Run` and `Call` induction. Every new candidate retains all
accepted input terms. Every stored winner retains its original's terms.
The final physical lookup identifies that original with the current argument.
Empty result tables require no supplied semantic cache answers.

`SourceCurrentMemoMergeOrigins` retains an actual completed memo-aware body
for each stored entry. Provenance alone is not used as a language theorem.
The language proof separately checks actual recursive execution and cache
coverage. No uncached producer is replayed in a later heap.

## Global receipts and finite composition

`SourceCurrentMemoMergeQueryMemos` follows actual instruction order. Hits
produce no body read. Misses retain their actual recursive receipts.
All three returned tables are valid. Earlier unfolding entries remain.
Both query tables are unchanged.

`SourceCurrentMemoMergeComplete.finite` combines finite execution, physical
effects, retained entries, and independent coverage for a valid warm result
table. `cold` derives entry validity, coverage, and producer histories from
an empty result table. The initial physical heap can still be warm.
`source_cold` fixes the current plain predicate and source Top guard. The
same finite call supplies its actual global receipts and returned tables.

## Remaining boundaries

This is a completed sequential projection. The Haskell lazy map publishes a
thunk before the body is forced. Publication, pending ancestor forcing,
concurrent races, and GHC evaluation need a separate correspondence proof.
The earlier publication graph does not supply that proof.

Existing shared-target and class-pass graphs still use the earlier body
boundary. Their receipts must be connected to these memo-aware requests.
No theorem here identifies the effects of the two body graphs.

Actual allocation history, checked native-state transfer, physical machine
bounds, general Scan completion, and the outer constrained caller remain
open. The full-library objective, exact Sized contracts, optimized interned
core, and all earlier constructor and equality proofs remain in scope.
