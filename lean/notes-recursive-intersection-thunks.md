# Native recursive memo thunk observations

Proof checkpoint: `6b8ceed8`. Upstream: `f59c198d`, 2026-10-14.
Source: `Interned/Operations.hs:intersectOpen`, `intersectOpenEdge`, and
`Interned/FlatMemo.hs:lookupOrInsert`, `insert`, and `write`.

## Completed edge provenance

`SourceRecursiveIntersectionEdgeMemo` extends concrete completed provenance
to guarded physical edge executions. The native key contains shifted domain
identity and ordered raw edge identities. It does not add node tags.
Checked word bounds derive nonnegative first keys and exact complete request
identity. Reversed unequal rows have different keys. Completed provenance
derives current row residency and exact replay at a finite child bound and
every larger bound. Initialization, growth, hits, and first-writer insertion
preserve that provenance.

## Publication before evaluation

`FlatMemoThunk` separates the published key table from typed thunk cells.
A cell captures its original request. Its phase is suspended, evaluating,
or returned. A miss publishes a fresh suspended cell. A hit retains the
first thunk identity and original request. `recursive_pending` proves that
a recursive lookup can find the same running thunk before completion.
Demand on a running cell records `busy`. It does not return Empty, a cutoff
reference, or a fabricated completed result. Demand on a returned cell gives
its original value without state changes. A second completion cannot replace
that value.

The source writes the unevaluated value and the second and third keys before
it publishes the first key. `FlatMemoPublication` supplies the logical
publication and stale-reader recheck layer. The new thunk model uses that
layer. It does not prove raw GHC primitives, memory barriers, black-hole
scheduling, exception caching, or completion of a busy demand.

## Actual source request families

`SourceRecursiveIntersectionThunks` keeps separate node and edge tables.
Node cells capture the canonical domain and ordered physical operands.
Edge cells capture the domain and complete ordered row records. Node lookup
uses the actual tagged source key. Unresolved placeholders retain the direct
source path without memo effects. Edge lookup uses the actual raw row key.
`node_publication` and `edge_publication` derive the publication first-key
contract from the checked source machine bounds.

`SourceRecursiveIntersectionThunkEffects` proves that publication, demand,
and completion preserve both table invariants. Physical constructor and
domain growth retain suspended and running input records and actual completed
provenance. `finishNode_execution` and `finishEdge_execution` complete the
original running cell from an actual guarded kernel execution. The exact
returned source machine is retained. The other memo family and all published
keys remain unchanged. The body execution in these two theorems is still
the uncached kernel.

`SourceRecursiveIntersectionThunkReadback` derives exact captured request
identity from a checked source key in every thunk phase. The source node and
edge wrappers can find the same running thunk before completion.
`node_ready_replay` and `edge_ready_replay` prove that a completed native
lookup and demand return the same concrete source result without effects.
The uncached kernel returns that same result at a finite bound and all larger
bounds. `completed_nodes` and `completed_edges` recover the existing completed
memo invariants from the pending table state.

## Next obligations

Thread both memo families through the actual recursive body requests.
The current `execute` and the completion body premises still use uncached
recursion. The new lifecycle operations alone do not establish whole-caller
memo correspondence or first-run termination. Do not treat a busy observation
as a successful result. Preserve the original continuation and current source
effects when a bounded execution yields. Do not publish only completed values
as a replacement algorithm.

Compile or interpret the source branch operations with explicit recursive
node and edge requests. Derive agreement with the existing guarded kernel.
Keep publication before body forcing, placeholder bypass, ordered and reversed
requests, domain allocation, actual Mu lookup, and optional-binder effects.
Derive sufficient bounds and completed provenance from the native execution.
Do not assume callback purity or equivalent output language.

Then derive physical input views, finite reachable payload inventories,
`ProductReadback.members`, and `.rejected`. `product_exact` gives product
language after these obligations. General open nested constructor completion,
new-body preparation, runtime primitives, and verified Haskell extraction
remain open. The exact Sized and cold-table proofs remain unchanged.

## Validation

All five new modules are imported by `MicroCFTA.Audit`. The pinned Lean 4.34.1
aggregate build passes 1,228 jobs and 40,726 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are used.
Log: `/tmp/mcfta-recursive-thunks-20261014-audit.log`.
No Haskell source changed. Prior Nix and formatter checks remain the source
validation checkpoint. Prior proof, draft, and fixture bytes remain preserved
against the saved manifest.
