# Intersection domain and flat memo keys

Upstream PR #102 changes `intersectOpen` and `intersectOpenEdge` in
`microcfta/src/Data/CFTA/Interned/Operations.hs`. `mkIntersectionDom` interns
the pair `(IntMap.toList free, Set.toList recInt)`. Domain equality then
compares the returned identity. Node memoization uses the triple of domain
identity and two `nodeMemoKey` integers. Edge memoization uses domain
identity and two raw edge identities. The wrapper retains operand order;
the intersection worker can subsequently request a canonical-order swap.

`nodeMemoKey` in `Interned/Type.hs` uses `4 * i + t`. The tags are 0 for an
ordinary node, 1 for Mu, 2 for Union, and 3 for RecInt. EmptyNode uses -1.
RecUnint, RecDepth, RecIntersect, and RecState return no memo key. If either
operand has no key, `intersectOpen` calls its worker without memo lookup
or insertion.

## Proved key correspondence

`IntersectionFlatMemoKey` models the exact modular bit patterns with
`BitVec width`. `tagged_arithmetic` connects multiplication and addition
to the encoded natural code. `empty_signed` proves that the empty bit
pattern reads as signed -1. `machine_eq_iff` and `signed_eq_iff` prove exact
source tagged-input equality under `Safe`. `key_eq_iff` includes the
optional source `NodeRef` keys. The placeholder bypass is explicit.

`IntersectionFlatMemoKeyDomain.canonical_eq_iff` proves that sorted unique
free-map and recursive-set lists are equal exactly when they have the same
entries. `domain_identity_exact` applies the existing interning invariant
to relate a stored domain identity to that structural equality.
`flatKey_eq_iff` proves that equality of the new node triple is exactly
equality of the old structural-domain and tagged-operand request.
`edgeKey_eq_iff` proves the corresponding edge statement. `memo_hit_correct`
then equates the old pure computations of requests that share a valid new
key. The cache's TypeRep partition and low-level flat-table operations are
separate source correspondence obligations.

`IntersectionFlatMemoKeyPhysical.available_safe` derives each operand's
safe range from the actual physical issued-node counter and availability.
`physical_key_eq_iff` combines this with coherent resident records. Equal
memo keys then imply equality of the complete physical source payloads.
It requires `state.nodes.next < 2^(width-2)`. This bound is an explicit
premise; the unbounded natural cache model does not establish it globally.

## Exact machine limits

For a word width `w = bits + 2`, let `q = 2^bits`. The first-period safe
range excludes the all-ones bit pattern reserved for EmptyNode:

- Ordinary, Mu, and Union identities satisfy `0 <= i < q`.
- RecInt identities satisfy `0 <= i` and `i + 1 < q`.
- A uniform bound for all tags is `i + 1 < q`.

These conditions are equivalent to `4*i+t < 2^w-1` for each nonempty tag.
Negative signed node keys are permitted: crossing the sign bit does not
by itself cause an equality collision. The first flat-key component has
the separate source requirement that the domain identity is nonnegative.
`domain_word_nonnegative` derives that requirement from a positive word
width and `domain.identity < 2^(w-1)`. The raw domain and edge identity
casts must also avoid supply wraparound.

`sentinel_collision` proves that RecInt identity `q-1` has the EmptyNode
key. `node_wrap_collision` proves that ordinary identities `q` and 0 have
the same key. `collisions64` retains the exact checked witnesses:

- RecInt `4611686018427387903` has the EmptyNode key -1.
- Ordinary node `4611686018427387904` has the ordinary-node-0 key.

The node counter uses atomic machine-Int increments from zero. Source
interning does not check the smaller memo-key limit. These collisions
therefore mark a machine-boundary limitation in the unconditional comment
that different nodes have different memo integers. They are not a
demonstrated feasible source-constructor failure. A source run approaching
these 64-bit bounds would require about `2^62` identity reservations. The
cache never evicts, but losing concurrent reservations can leave unused
identities, so this count is not a proved count of retained entries. No
resource-feasible source trace reaching the limit was established.
Exported constructors permit
forged large identities, but those values need not satisfy source cache
coherence. No such forged value is used as evidence of a production
failure. Negative domain IDs also lie outside the flat-cache first-key
contract and do not independently establish a valid-source defect.

## Validation and limits

The three modules build under pinned Lean 4.34.1. The imported-theorem
axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
The focused log is `/tmp/mcfta-intersection-flat-key-audit.log`.
No Haskell source change or runtime collision reproduction is included.
The proofs retain the machine bounds, canonical container encoding,
per-type cache partition, and valid interning history as explicit
correspondence boundaries.
