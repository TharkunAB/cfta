# The mixed finite automaton cache driver

`MicroCFTA/FiniteAutomatonDriver.lean` models the full control flow of
`compileFiniteAutomaton`, `buildNode`, `buildAlternatives`, `buildEdge`, and
`buildGroup` in `Gen/Internal/Automaton.hs`. `CompactIndexChoice.lean` supplies
the concrete ordered alternative decoder and inverse.

## Concrete operational model

`Flags` and `useSymbolic` model the source fallback condition:
shared symbols with ambiguity or tied canonical keys, a residual guard, or a
path below a direct child. `EdgeSpec` retains the ordered source children and
the optional parsed equality groups. `groupRequest` scans the children by
position and executes the actual left fold of intersections.

`runGroup`, `runEdge`, and `runCompact` perform the source state traversals.
A `Nothing` group result is ordinary traversal data. It does not stop the
state traversal. Every later group still runs before `finishGroups` checks
whether all intersections succeeded. Every later edge also runs before
`finishAlternatives` drops empty edges. No such traversal enumerates terms.

`buildNode` checks empty rows before reading its cache. A cache hit returns
its stored result. The cache stores both successful indexes and `Nothing`,
so a stored empty result differs from a missing entry. On a cache miss, the
worker chooses its source backend and inserts the completed result afterward.
The operational port returns an outer `none` only when its proof budget ends.
The theorems show that this case is unreachable with a sufficient budget.

`compile` preserves the source public check order. An empty root returns
`EmptyGenerator` before the reachable guard-indicator check. An unsupported
indicator returns `CannotCountConstrainedEdges`. The indicator result is an
explicit input to this adapter; its actual traversal and guard compilation
are separate source modules. Successful driver results retain both the
decoder and inverse made in the same pass.

## Derived termination and cache invariant

`fold_meet_bound` and `group_request_bound` bound each requested intersection
by an actual selected child. `structural_requests_decrease` instantiates those
bounds with `SymbolicGraphView.structural_intersection` and
`GraphBudget.child_smaller`. It uses the actual copied product-row adapter and
acyclic row ranks. It does not assume that the driver terminates or that
intersection preserves a desired semantic height.

The structural budget is computed from constructor rows. It remains valid
when guards reject every term. Fresh intersection identities may exceed
parent identities; their computed structural budgets still decrease.
`buildNode_from_rows` proves complete source execution from those local row
adapters. A finite global list of all generated intersection identities is
not required.

`pureBuild` gives a bounded pure reference for the same local operations.
`pure_stable` proves that all adequate bounds agree. `reference_equation`
derives the recursive source equation for the selected reference bound.
This equation is proved, not supplied as a fixed-point premise.

`buildNode_exact` proves that every source cache execution returns that exact
reference result and retains a valid cache. It covers cache misses, cached
success, cached emptiness, symbolic fallback, and the full compact traversal.
The recursive proof uses only smaller computed requests. It assumes neither
a desired root index nor a whole-driver totality contract.

## Exact compact and symbolic composition

`CompactIndexChoice` models the source cardinality sum, count subtraction,
and first-success inverse with prefix offsets. It derives both inverse
directions under the local alternative disjointness supplied by the source
overlap gate. It also proves totality, bounds, and exact union coverage.

`ResultExact` is the induction statement. A missing compiled result means
an empty language. A present result has positive cardinality, a total direct
selector, both inverse directions, and precisely the independent language.

`groupRequest_language` derives each requested intersection's child-position
domain from the actual intersection fold. `localEdge_exact` uses those
smaller indexes, the parsed group layout, and `CompactEdgeRanks`. It derives
the complete edge index. If a group is empty, it proves that the removed edge
language is empty. `finishAlternatives_exact` proves that dropping such edges
and combining the retained indexes preserves the exact disjoint union.

`localNode_exact`, `reference_exact`, and `driver_exact` then derive complete
node correctness. `driver_from_rows_exact` combines semantic correctness with
the structural termination proof. Every stored cache result is exact too.
`compile_correct` proves the public successful index contract.
`compile_empty_iff` proves that the public empty error denotes precisely an
empty language when the local supported-backend adapters hold.
`exact_index_api` exposes contiguous ranks `0 .. count - 1`, distinct decoded
terms, and rejection of exactly the nonmembers.

## Precise source adapters

`Semantics` retains local contracts for source data that this module does
not redefine:

- Empty exposed rows have no accepted term.
- The chosen symbolic backend gives its proved exact optional index.
- A copied intersection denotes the intersection of its operand languages.
- The successful direct-child parser gives the existing valid group layout.
- Each compact node's accepted language is the union of its original guarded
  row languages under that local parser adapter.
- The compact branch's overlap gate makes those row languages disjoint.

The symbolic contract is local to the selected backend. It corresponds to
`SymbolicPublicAdapter` and the allocated symbolic index theorems. The row and
guard adapters correspond to the existing graph-row, full equality guard,
parser, and `AutomatonAmbiguity` proofs. `localEdge_exact` and
`finishAlternatives_exact` derive their index consequences here. No cache or
root compiler correctness statement is a field of `Semantics`.

The graph-budget adapter also requires the source copied intersection rows
and an acyclic rank for every observed constructor row. Existing allocation
history theorems supply the rank when their runtime row readback contract
holds. The Lean worker does not prove Haskell hash-table implementation,
concurrent identity stability, garbage collection, or machine integer limits.

## Errors and checked traces

The actual `symbolic` helper uses `either (const Nothing) Just`.
`symbolic_failure_cached` preserves that behavior. It does not reinterpret an
arbitrary backend failure as a proved empty language. The semantic theorem
requires the supported local symbolic adapter. The source
`fromIndexedOnDemand` construction error is its nonpositive-cardinality case;
the symbolic adapter proves exact counts and eventual nonempty construction.
Proof execution-bound errors stay distinct and `compile_no_execution_error`
excludes them at the derived bound.

The kernel-checked traversal fixture has an empty first group and a successful
second group. It proves that both child results are cached and that the final
empty root result is cached. Thus it checks the source traversal order that
would be lost by short-circuiting the stateful group traversal.

Validation on 2026-10-12 used Lean 4.34.1:
`lake -d lean build MicroCFTA.FiniteAutomatonDriver` passed, including
`CompactIndexChoice`. No Haskell file changed. No Cabal build ran.
