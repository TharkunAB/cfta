# Ordered cold source edge reader

The physical Lean reader now models the ordered `nodeEdges` branches in
`microcfta/src/Data/CFTA/Interned/Operations.hs`. It executes actual
stored-body unfolding against the cache returned by each earlier call.
It needs no eager warmup.

## Implemented source behavior

`MergedSourceExposure.collect` processes the worklist from left to right.
It skips empty values, appends ordinary edges, and reports an unresolved
reference reached by the union closure. It records the numeric canonical
identity before it expands a union or unfolds a Mu. Union members precede
the old worklist tail. A Mu's actual returned value precedes that tail.

`MergedSourceExposure.nodeEdges` includes the source's separate fast
paths. An ordinary node returns its stored edges. Empty and direct
reference roots return no edges. A Mu first unfolds once. An ordinary
result returns its edges directly. Other results start the closure at the
original root in the returned cache. The closure fallback applies the
existing canonical edge-identity ordering and deduplication.

The result type distinguishes successful edges, an unresolved reference,
a pending construction, and exhausted proof fuel. A reference error is
never converted to an empty edge list. Proof fuel bounds worklist steps;
it does not bound the already-total stored-body executor.

## Termination and closedness

The scope is `MergedPhysicalWarmup.Prepared`: every complete Mu body must
satisfy `InternedStoredClosedMuCompletion.PreparedWithoutMu`. This permits
depth-zero bodies and closed nested Mu records of arbitrary depth. It
excludes preparation through an open nested Mu.

`MergedColdReaderTermination.collect_complete` proves that every
available worklist in this fragment finishes or reports its explicit
reference error. The proof uses the lexicographic measure:

1. The number of remaining initial issued Mu-identity allowances.
2. The finite structural weight of the pending union records.

An unseen Mu consumes its allowance. Actual unfolding completes and adds
no Mu record, so later recursive records retain an earlier allowance or
already occur in the visited set. Union expansion decreases the second
measure. The actual initial issued counter supplies all allowances.
The proof assumes no finite future-state inventory and compares no
alternative allocation histories.

`nodeEdges_complete` includes the initial Mu fast-path call.
`collect_stable` and `nodeEdges_stable` prove that extra fuel preserves
the exact successful or error result and its exact returned cache.

`MergedColdReaderClosedInputs` proves that actual binder-free construction
preserves closed lexical inputs. It includes ordinary and union cache
readback. `MergedColdReaderClosed.unfold_closed` uses that result for the
prepared body of an available closed Mu. It requires source `Facts`, not
a separately assumed free-name semantic heap.

`MergedColdReaderClosed.nodeEdges_closed` excludes unresolved references
for available closed roots. It returns actual edges and proves that each
returned edge child is closed.

`MergedColdReaderFacts.read_closed` combines successful completion,
stable fuel, complete record facts, preparation, cache growth, issued-name
history, absence of new Mu records, and returned edge residency. These
properties apply to the exact cache returned by the reader.

`MergedSourceExposureLanguage.nodeEdges_origins` proves that every returned
edge comes from an actual epsilon path in the returned cache or any later
extension. Each cold unfolding on that path replays with its exact result.
`nodeEdges_sound` therefore proves that the reader cannot introduce an
accepted finite term. The reverse edge-coverage direction remains open.

## Checked examples

`MergedSourceExposureExample` executes four source branches in Lean:

- The natural-number Mu's first read returns labels `[0, 1]`, retains
  recursive child `.mu 2`, and increases the node counter from `4` to `5`.
- A raw bare-self Mu returns no edges after its canonical identity enters
  the visited set. Two worklist steps suffice; one step exhausts fuel.
- A retained union of unresolved primitive references reports the first
  unresolved reference.
- A direct primitive reference uses the separate top-level empty-edge
  branch.

These are checked executions of the physical Lean source model. They are
not a new Haskell runtime replay.

## Remaining work

This closes the cold ordered edge-reader completion boundary for the
prepared structural fragment. The complete ordered stateful `subsumes`
worker still needs composition with these reads and its ancestor-pair
test. The previous cold-schedule inventory and pair bound remain
available for that proof. This result does not establish arbitrary Mu
totality or convergence of repeated outer merge passes.

## Validation

The pinned Lean 4.34.1 build checks `MicroCFTA.MergedSourceExposureExample`
and all five supporting reader modules. The isolated imported-theorem
audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
The validation transcript is `/tmp/mcfta-merged-cold-reader-audit.log`.
