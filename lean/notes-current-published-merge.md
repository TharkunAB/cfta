# Serial publication, recursive forcing, and memo-aware targets

The source remains main `a4dd678f`. `Interned/Memo.hs` calls
`Cache.insertKeepingFirst`. That function looks up the key, installs a
candidate thunk if necessary, and rereads the stored winner. The lazy map
does not force the body inside its atomic update.

## Publication before forcing

`SourceCurrentMemoMergePublishedGraph` separates the published producer
table from completed evaluation status. The latter is proof state for the
published thunks. It is not another production cache. A force starts its
body at the published table, with the selected producer on the running stack.
The serial publication prefix is an instance of the earlier literal
`Publication` graph with no intervening inserts.

`Known` requires each published captured original to be available at its
actual tagged physical key. `CompletedPublished` requires a published
producer at each completed key. Neither invariant supplies a result-language
claim. `selected_original` derives literal captured-input equality from
these physical facts and coherent resident identity.

`SourceCurrentMemoMergeRequestBounds` derives each direct request's input
height, actual reached heap, availability, and retained-prefix facts from
the actual source body. Its `Direct` receipts retain instruction order.
They do not replace a recursive call with a transitive event list.

`SourceCurrentMemoMergePublishedLift` constructs early publication from
completed memo-aware calls. Every recursive request input has smaller
ordinary height than the current parent input. Resident identity therefore
excludes running ancestor keys. The finite endpoints derive this exclusion;
they do not take it as a premise. Completed outputs need no height bound.

The published graph preserves each running ancestor's completed lookup.
The actual body cannot complete its own running key through a child request.
`SourceCurrentMemoMergeNoReentry` derives the corresponding unchanged-key
law for the earlier completed body graph. An absent parent key stays absent.
The actual miss therefore returns its computed body candidate.

`SourceCurrentMemoMergePublishedProjection` proves the other direction.
Every valid completed published trace has exactly the earlier memo-aware
output, constructor heap, and completed result table. Its physical effects
and publication invariants are derived by actual instruction induction.
No uncached body is replayed in a later heap.

`SourceCurrentMemoMergePublishedComplete.verified` derives independent
language coverage from that exact projection. `finite` constructs a finite
published call from initial warm-state invariants. `native_cold` derives an
early-publication history, native effects, producer history, independent
coverage, and the three global memo receipts for the same finite native call.
Empty publication and completed tables derive their entry obligations.
The initial physical heap and native tables can be warm.

## Native state and demanded targets

`SourceCurrentMemoMergeNative` wraps the actual new completed call with
`advanceHeap`. It retains native node and edge tables and domains. It derives
IdleReady, stored costs, result availability, conditional closedness, and
result-table retention. Its reads retain the same lower call and final heap.

`SourceCurrentMemoTargetOperand` projects the original captured forest and
then uses that new native merge. It requires only the selected path domain.
Unrelated siblings can be open. Physical records and completed entries grow
through the actual projection and merge heaps. Proper selected original
subterms survive. The same operand has its ordered projection and merge reads.

`SourceCurrentMemoDemandTarget` threads the returned merge table through the
source's first-seeded right fold. It demands the left operand, then the tail,
then the native intersection. Intersections leave result-table contents
unchanged and derive their physical invariant at the returned heap.
The empty target returns EmptyNode with unchanged state and memo. A singleton
retains native tables and domains. Multiple operands can populate those tables.

The target proof retains a common accepted original subterm selected at every
proper operand path. This is coverage. It does not assert that narrowing
alone enforces every original class. The exact caller still checks the
original constraints. Finite target execution uses explicit reached native
word-range plans. General machine-range adequacy is not a consequence.

## Grouping and remaining source correspondence

`SourceCurrentMergeGrouping` follows the literal singleton-map insertion
fold. It distinguishes an absent key from an empty bucket. It proves exact
bucket contents and their original within-bucket order. A finite iteration
contract requires unique emitted keys and exact lookup membership. These
facts derive a permutation of canonical groups. No outer-permutation premise
is supplied to that theorem.

The actual HashMap implementation still needs that iteration contract.
The memo-aware body still uses canonical outer groups. It has not been
changed to follow a literal HashMap allocation schedule. A group permutation
does not prove equal constructor heaps, identities, or result producers.

Producer tickets are abstract labels. The serial construction can use zero
without a runtime pointer-freshness claim. Concurrent evaluation, waiting on
another thread's producer, literal GHC forcing, and host cache operations
remain open. The new serial graph closes the modeled publication-order gap;
it does not establish whole-runtime adequacy.

The older shared-target and class-pass graphs remain intact. Their stored
closures, edits, and final pass must now thread the new merge table and use
the new demanded target. General Scan and constrained outer completion,
actual allocation history, checked native transfer, and machine bounds
remain open. The full import, enumeration, template, refinement, generator,
decision-model, curried/GHC, synthesis, normal-form, and distinct Sized scope
also remains active.

Verification and preservation evidence uses `/tmp/mcfta-published-merge-*`,
`/tmp/mcfta-memo-merge-*`, `/tmp/mcfta-memo-target-*`, and
`/tmp/mcfta-current-merge-grouping-*`. Haskell and CI are unchanged.
