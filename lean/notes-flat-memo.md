# PR 102 flat memo table audit and model

Source baseline: `origin/microcfta` at `9508eb3`. The source implementation
is `microcfta/src/Data/CFTA/Interned/FlatMemo.hs`. All changes here remain
local. No Haskell source repair was needed within the documented key and
machine-size preconditions.

## Proved slot and memo invariants

`FlatMemoProbe.lean` models published slots as complete key/value records
or empty slots. Its probe order visits the suffix from the hash index and
then the prefix. `half_full_probe` proves that a positive half-full array
has a vacancy, cannot exhaust one wrap, and reads at most its capacity.
Successful and empty results refer to the exact inspected slots. An empty
result supplies a prefix containing only occupied slots.

`FlatMemoTable.lean` states the occupied-prefix placement invariant and
exact representation of the abstract `Cache.Table`. Every represented
key is found with its original value. Actual physical insertion into the
first empty slot preserves placement and refines `Cache.keepFirst`.
An existing key retains its first stored value. The slot model uses an
arbitrary hash index, so collisions do not require a hash-quality premise.

`FlatMemoGrowth.lean` proves that an empty-slot write increases occupancy
by one and each insertion increases occupancy by at most one. Copying a
finite record inventory into enough empty space completes. The actual
copy loop refines `Cache.updates`. Copying all source slots into doubled
capacity preserves the complete abstract memo table. Both the growing
insertion branch and the nongrowing load test preserve half-full occupancy.

`FlatMemoPublication.lean` separates staged payloads from published first
keys. Before publication a reader sees an empty slot. A valid published
first key reveals the complete record. A stale successful lookup retains
the current winner. A miss rechecks the current arrays under the abstract
writer serialization and preserves the first winner.

The publication model also permits per-slot observations from different
times. Those observations need not form one whole-array snapshot.
`observed_probe_complete` proves termination when their complete records
extend to one half-full retained array. `observed_lookupOrInsert_correct`
needs only that observed complete records retain their winners in the
locked current table. Rebuild preservation supplies this property across
array generations.

The four storage modules compile with Lean 4.34.1, six dependency jobs. The audited
theorems use only `propext`, `Classical.choice`, and `Quot.sound`, or a subset.
The audit is `/tmp/mcfta-flat-memo-axioms-20261013.log`.

## Explicit implementation boundaries

The source advances with `(i + 1) .&. mask`. `FlatMemoProbeLayout.lean`
proves that word masking equals modular wrapping. It proves that the
source starts with a power-of-two capacity and retains it under doubling.
Its `order_source` theorem connects each suffix/prefix traversal entry to
the repeated source increment-and-mask operation. `FlatMemoLayout.lean`
proves allocation, slot-offset, load-factor, doubling, and negative
missing-slot bounds. These arithmetic results retain explicit machine
range premises. They do not prove that an allocation succeeds.

The raw representation uses three native `Int` words per slot and allocates
24 bytes per slot. The source hash finalizer uses `Word` and 64-bit mixing
constants. The model does not execute `MutableByteArray#` or boxed-array
primitives. It does not establish GHC atomic ordering, garbage-collector
behavior, `IORef` publication, `MVar` serialization, `noDuplicate`, or
asynchronous-exception semantics.

The native implementation must establish two publication facts. A reader
that observes the atomic first key must observe the earlier second key,
third key, and boxed value writes. A reader that observes a new arrays
reference must observe all copied source entries. The proof treats these
as the representation boundary for complete published records. It does
not add a logical axiom for either raw primitive claim.

No theorem forces a memo value. Values are uninterpreted payloads in the
model. Native lazy or recursive thunk behavior remains outside these
storage theorems.

## Source findings and concrete checks

The module documents a nonnegative first-key precondition. The actual
intersection callers use the interned domain identity as the first key.
The exported `lookupOrInsert` function does not check that precondition.
First key `-1` remains invisible after publication and therefore cannot
have first-writer retention. `sentinel_invisible` records that exact
excluded case. This is not a defect for the documented valid callers.
Negative second and third keys do not use the empty-slot sentinel.

The 24-byte allocation assumes the intended three 64-bit key words. On a
32-bit runtime it over-allocates key storage. Capacity multiplication,
doubling, occupancy arithmetic, and signed miss-index encoding need
explicit bounds. These assumptions remain distinct from the unbounded
natural-number slot model.

The primary reviewer ran all 620 existing Haskell examples on the rebased
source. The targeted native probe passed 20,000 sequential growth keys,
lazy and reentrant values, and 32,768 concurrent results across eight
workers with `-N4`. Logs are `/tmp/mcfta-20261013-pr102-103-tests.log` and
`/tmp/mcfta-flat-memo-probe.log`. These checks support the native behavior;
they do not verify the raw publication primitives.
