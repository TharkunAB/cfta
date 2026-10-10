# Persistent state and cache proofs

Source baseline: `adb1f012b336ba0d1673f8fd7f310ad75bdfaf04`.
These modules close state-operation obligations used by enumeration and
interned graph algorithms. Their callers still require the invariants listed
in [COVERAGE.md](COVERAGE.md).

## Union-find

[UnionFind.lean](MicroCFTA/UnionFind.lean) follows
`microcfta/src/Data/CFTA/Internal/UnionFind.hs`.

- `Forest` models the effective `IntMap` lookup. `put` models a single insert.
  Missing entries mean singleton roots of size one, as in `findRoot`.
- `Reaches` independently specifies a finite parent path to a root. It also
  records the stored size. Its uniqueness theorem requires no executable
  lookup or assumed representative function.
- `findRoot` performs the recursive lookup, then compresses against the state
  returned by that call. `findRoot_correct` proves it follows an original path
  and preserves every original path. A forest in which every variable has a
  finite root path is `Total`. `findRoot_terminates` derives a sufficient
  execution bound from such a path; additional fuel leaves the result unchanged.
- `findRoot_reaches_iff` proves exact path preservation for total forests.
  `findRoot_classes` proves exact equivalence-class preservation.
- `union` performs both lookups and follows the Haskell size comparison and
  tie direction. `union_correct` proves that precisely the two requested
  classes merge. It also preserves termination of subsequent lookups.
- `initial_sizes`, `findRoot_sizes`, and `union_sizes` establish and preserve
  exact class cardinality metadata over a finite allocation domain. Both
  queried variables must be in the domain for `union_sizes`.
- `union_satisfies` proves that the resulting assignment constraints are
  exactly the original constraints conjoined with the requested value
  equality. This is the interface needed by suspended enumeration obligations.
- Fresh allocation and size-bound theorems state the natural-number bounds
  needed before a machine-`Int` correspondence can apply.
- `ClosedDomain` keeps representatives inside the allocation domain.
  Initialization, compression and union preserve it. `sizes_allocate` and
  `closed_allocate` preserve the invariants when a fresh singleton is added.

The finite execution bound makes successful Haskell recursion explicit. It
does not reject any lookup with a finite parent path. Parent cycles do not
satisfy `Total`; initial forests and successful unions preserve that invariant.

Remaining correspondence: concrete `IntMap` laws, signed machine arithmetic,
the caller's fresh-singleton condition, and invariants for enumeration value
slots. The module does not assert that arbitrary exported internal values or
overflowing allocations are valid.

## Interning and memoization

[Cache.lean](MicroCFTA/Cache.lean) follows `Interned/Cache.hs` and
`Interned/Memo.hs` at their effective typed-map interface.

- `keepFirst` models the atomic insert that retains the stored value.
  `updates_extend`, `delayed_read`, and `readback_fallback_unused` prove that
  later insertions retain its winner and that the final lookup finds it.
- `MemoValid` requires each cached value to equal its designated pure
  function's result. Inserting that computed result preserves the invariant;
  `memo_correct` derives equality of memoized and ordinary evaluation.
- `reserve` models the atomic identity increment. Its ghost reservation map
  records which key obtained each identity. It includes candidates that lose
  an insertion race. `install_valid` permits an issued candidate to arrive
  after intervening reservations and installations.
- `Steps` describes finite interleavings of atomic operations. Its invariant
  proves unique identities for different keys and stable canonical values for
  equal keys. `concurrent_readback` derives agreement of completed reads.
- `shardedInsert_correct` proves equality with unsharded lookup for any
  deterministic shard function. It does not require distinct hashes or
  distinct shards for different keys.

The reservation map is proof metadata, not proposed production storage.
Linearization of the runtime atomic primitives, bit-level shard bounds,
`HashMap` implementation laws, typed cache-family selection and casts, and
evaluation of recursive thunks remain correspondence obligations. Pure-result
memoization does not by itself prove termination or the binder-shape key
correctness needed by recursive interning.

## Enumeration value slots

[Fragments.lean](MicroCFTA/Fragments.lean) follows `TermFragment`,
`intersectUVarValue`, `assimilateUvarVal`, and `mergeNodeIntoUVarVal` in
`Enumeration.hs`.

`fill_representatives` proves that resolving fragment holes preserves their
completed terms for every assignment that satisfies the forest equalities.
`intersectSlots_correct` proves conjunction of graph restrictions and suspended
obligations. `assimilate_correct` moves those restrictions to the surviving
slot without changing permitted assignments. `union_assimilate_correct`
connects this operation to the executable union-find merge: together they add
exactly the requested term equality. `mergeInto_correct` verifies the addition
of a graph restriction and inherited obligations. An empty graph restriction
is proved to make the entire heap unsatisfiable.

Graph restrictions use their term-language interpretation. The synchronous
intersection theorem connects a concrete graph intersection to that
interpretation. Suspended obligations are still predicates on the assignment
and the current term. Their concrete path construction, the live-slot
invariant, array bounds, recursive fragment expansion and the scheduler remain
caller obligations. Failed intersections of expanded or eliminated slots are
explicit errors in this reference; caller proofs must show they are avoided.
