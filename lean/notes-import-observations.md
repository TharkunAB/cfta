# Observation partitions for imported automata

`ImportObservations.lean` connects the requested-path interface of
`Gen.Refinement.Internal.Compile` to the existing `ObservationGraph` worker.
The existing worker proves the child Cartesian product, copied edge guards,
graph-language coverage, and exact observations. This module derives the
source request-map and key properties from that worker. It does not replace
graph specialization with enumeration of an explicit term list.

`child_requests_exact` proves that each child receives precisely the tails
of requests under its index. `request_plan_exact` proves that every request
reads the complete symbol and leafness, and creates no extra prefix read.
`child_request_plan` connects that child map to trie descent. The finite
budget is the greatest requested path length plus one. Graph cycles do not
increase that observation budget.

`prefix_disjoint` proves that indexed child maps cannot overwrite one another.
`merge_prefixed_child` proves the actual left-biased map-union readback.
`merged_observations_exact` connects the root map and child-map union to
`completeObservations`. `parent_root` records the additional root retained by
`parentObservations`. A missing position has no map entry. Kernel checks
include a request below a leaf; the leaf remains in an empty-key part.

`split_empty` retains the original graph reference for an empty request set.
`split_cover` proves both language inclusions for every finite accepted term.
`split_view` proves that every member of a part has its exact requested map.
The finite vector key includes optional entries for every requested position.
It is an injective encoding of a supported sparse map; absent entries remain
absent. This is the extensional meaning of the source `Map` key.

`merged_keys` proves that the alternative merge emits each first-occurrence
key once. `split_keys_nodup` and `reordered_keys_nodup` show that sorting the
source import parts cannot duplicate a key. `group_language_exact` proves
that a part contains all and only accepted terms with its key. Distinct keys
have disjoint languages. `decoder_cover` and `decoder_injective` compose
exact local part decoders without term loss or collisions across groups.
Their local decoder contracts are supplied separately by the symbolic index
proofs. These theorems do not independently reprove those workers or the
integer offsets used by the grouped rank interface.

The adapter uses natural-index paths and the graph-state view of the existing
specialization proof. Stored binders require the existing row-exposure
contract. The source `Map` and `Set` storage, interned identity allocation,
and invalid signed-path representation are not reimplemented here. The map
readback and disjoint-prefix claims state the required representation laws.

## Repaired source loss

The audit found that `splitByObservations` handled `Node` and `Mu`, but omitted
`InternedUnion`. The fallback returned no parts. The valid imported grammar
`mu r. (r union a)` has the finite language `{a}`. A direct size-one import
returned `a`. A parent guard that required `True` at the imported root caused
compilation to report `EmptyGenerator`. The union of that grammar with `b`
lost both terms in the same way.

The repair exposes `InternedUnion` with `nodeEdges`, then passes the resulting
ordinary node to the existing split. `nodeEdges` computes finite epsilon
closure. The repair adds no constructor to terms and does not alter the
requested paths or binder-unfolding branch. The existing refinement suite
checks both finite grammars, root and descendant requests, cardinality,
decoded terms, and inverse ranks. `repro/ImportUnion.hs` retains the public
counterexample and checks the repaired result with Z3.

The graph adapter requires the same correct row-exposure boundary for ordinary
nodes, binders, and epsilon unions. Returning an empty list for an inhabited
union violates `split_cover`; it cannot be hidden in an observation-key law.

Validation: `lake build MicroCFTA.ImportObservations` passes with the pinned
toolchain. The source repair passes 611 examples across the three Haskell
suites, and the retained public repro returns the original terms. The
separately discovered productive-recursion grouping issue is outside this
one-case repair.
