# Source cyclic gates and distinct size-class indexes

`RecursiveUnambiguous` removes the global uniqueness premise from the cyclic
rank argument. `SourceCyclicAutomaton` connects this result to the source
`automatonRows` checks and to the actual bottom-up inverse.

## Forest and size-class uniqueness

`snoc_unique` proves that the source forest constructor has one prefix and
one final child. `product_nodup` applies this result to the prefix-major
Cartesian product at one size split.

`extendForests_nodup` proves uniqueness of the complete source convolution.
Each prefix has its declared node count. If two different size splits
produced one forest, unique prefix decomposition would give equal prefixes,
and their node counts would give equal split sizes. This is a contradiction.

`forests_unique` proves exact forest sizes and uniqueness through the actual
left-to-right child fold. `enumerate_nodup` then uses strong induction on
term size. Every child request uses a smaller size. The proof permits
arbitrary cycles in the state graph.

The induction requires local disjoint row languages, not global term
uniqueness. It works on any child-closed state scope.
`reachable_enumerate_nodup` instantiates that scope with the actual structural
reachable relation. Checks on unrelated states are unnecessary for this
root-local result.

`minimum_gate_unambiguous` supplies the local disjointness from
`AutomatonAmbiguity`. It uses the exact source pair scan and the computed
`productiveRows` test on explicit intersection rows. The minimum-size proof
ensures a shared finite term cannot be missed. The result is the previously
required `SizedRank.Unambiguous` theorem.

## Counts, decoder, and bottom-up inverse

`classIndex` stores a proof witness in the existing exact-size decoder order.
`classIndex_count` proves its distinct cardinality equals the source
convolution count. No term deduplication changes the source order.

`positionsOf_inverse` proves that the bottom-up `TablePosition.positionsOf`
worker and the counted class decoder are mutual inverses. It needs class
uniqueness only at the queried state. `positionsOf_reject` proves exact
nonmembership rejection. `replay_total` gives the full class interval
`0 .. countAt size - 1`.

`bounded_nodup` proves different exact sizes are disjoint. `rankAtMost` uses
the bottom-up position and the source sum of preceding class counts.
`rankAtMost_inverse` proves the actual bounded decoder is its inverse.
`selectAtMost_total`, `rankAtMost_reject`, and `selectAtMost_injective` prove
contiguous ranks, exact bounded-language rejection, and distinct output
terms. `boundedIndex_count` identifies the total with the sum of source class
counts.

The operational inverse follows the submitted tree and uses arithmetic
offsets. It does not search an enumeration of previous terms. Enumeration
lists in these theorems are finite proof witnesses. No asymptotic runtime
bound is claimed.

## Source cyclic import

`SourceCyclicAutomaton.compile` follows the actual precheck order:

1. `EmptyNode` returns the empty row table.
2. A nonempty root with free variables returns `OpenAutomaton`.
3. Any constrained reachable edge returns `CannotCountConstrainedEdges`.
4. Any ambiguous row returns `AmbiguousAutomaton`.
5. Successful compilation returns the ordered row table.

The source `unconstrainedEdge` test checks both normalized equalities and
the residual syntax flag. `unconstrained_plain` derives an always-accepting
guard from that exact test and `SourceCompactGuards.sourceEqualities_exact`.
The proof does not assume plainness for a successful import.

The finite snapshot lists every represented nonempty row. `checked_gate`
therefore derives a passing gate at every state. States absent from the
snapshot have no rows. Row sorting is supplied as a permutation. The proof
derives preservation of acceptance and disjointness under that permutation.
No row-distinctness premise is supplied.

`compile_exact` derives plain guards, distinct exact-size classes, and the
original root language for every successful source import. The public
theorems `exact_index_api`, `inverse_reject`, `distinct_ranks`, and
`class_count` expose the resulting rank guarantees. There is no assumed
global `Unambiguous` input or assumed root compiler equivalence.

## Checked examples

Kernel reduction checks a recursive binary grammar. Its size-7 count is 5.
Its total through size 5 is 4. The two size-5 binary shapes receive bounded
ranks 2 and 3 in source convolution order. Oversized and wrong-arity terms
are rejected.

A second example has two identical recursive unary alternatives and no
leaf. Its finite counts are zero. The actual minimum-size intersection test
reports no overlap. Thus duplicate unproductive rows pass the gate without
creating duplicate finite terms.

## Remaining runtime correspondence

The source input adapter retains these representation requirements:

- The row snapshot and free-variable list must be the ones read by the
  source. Every nonempty represented row must occur in the snapshot.
- Cached equality classes must satisfy their established canonical-class
  invariant. Source equality normalization and residual extraction are
  proved in `SourceCompactGuards` and `EqualitySource`.
- The sorted rows must be a permutation of the snapshot rows. Their supplied
  order determines ranks. Canonical class ordering is proved separately.
- The explicit intersection and minimum-size model uses a finite state
  domain with a complete pair list. Reading source interned intersections as
  this product graph remains the existing graph-operation boundary.
- Complete guards are retained in the independent graph view. The successful
  precheck proves they are all true. The source ordinary table stores unit
  annotations instead. The term and count algorithms ignore these proved
  true guards.

The proof establishes a total finite computation for each requested size
and each finite input term. It does not establish Haskell heap behavior,
lazy infinite count-list productivity, mutable map implementation, or a
single finite index for an infinite language. Every finite size class and
every finite size bound has the proved distinct contiguous index.

## Validation

```text
lake -d lean build MicroCFTA.SourceCyclicAutomaton
```

The focused build includes both new modules. All proofs are kernel checked.
No Haskell files or Cabal configuration change.
