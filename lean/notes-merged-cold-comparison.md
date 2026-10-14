# Cold physical comparison schedules

The cold comparison proof no longer needs an eager warmup to derive a
finite inventory for one actual request trace. It uses the cache returned
by each preceding query. It does not compare allocations from different
execution orders.

## Source boundary

`subsumes` in `cfta/src/Data/CFTA/Interned/Operations.hs` checks the
ancestor pair before it reads `nodeEdges`. The edge reader follows union
members and completed recursive unfoldings. Its closure traversal checks
the identities of recursive and union records before it processes them
again. Ordinary records supply their stored edge children.

The proof uses `MergedPhysicalWarmup.Prepared`. Every complete Mu body
must satisfy `InternedStoredClosedMuCompletion.PreparedWithoutMu`.
This includes depth-zero bodies and closed nested Mu records of arbitrary
depth. It does not include arbitrary open nested Mu preparation.

## Checked results

`MergedColdUnfolding.Schedule` records one chronological sequence of
actual `InternedStoredSubstitution.unfold` calls. Each query starts with
the previous query's returned state. It requires available inputs.

- `invariants` preserves the actual source record facts, preparation,
  cache growth, and the absence of new Mu records.
- `repeated` proves that a repeated actual input returns the exact earlier
  result and leaves its current cache unchanged.
- `changed_origin` and `changed_first` prove that a cache-changing query
  is the first encounter of an initial complete Mu record.
- `changes_bounded` bounds the number of distinct cache-changing calls by
  the initial complete-record inventory length and the initial issued
  node counter. This bound counts calls, not allocated records.
- `stabilizes` proves that every such infinite schedule has a finite
  prefix after which its entire cache remains constant. Every observed
  recursive result occurs in that finite prefix.

`MergedColdInventory.Generated` restricts requests to a finite initial
root list, a retained child of an earlier input, or an earlier result.
This condition prevents an external selector from introducing an
unbounded supply of primitive references.

- `finite_inventory` derives the physical inventory at the stable cache.
  It contains every actual input and result. The roots and retained
  results have source availability in that cache.
- `replay_stable` proves that every actual query returns its exact actual
  result in the stable cache. The proof uses only later states of the
  same trace.
- `pair_repetition` proves that any infinite sequence of pairs selected
  from the actual inputs repeats within the square of this inventory's
  length. `no_fresh_pairs` excludes infinite ancestor-fresh descent.

`MergedColdExecution` discharges the per-query completion premise.
`next_exists` uses the actual stored-body executor and preserves the
prepared configuration. Any selector of an available value in the
current configuration generates a total chronological `schedule`.
`execution_stabilizes` applies to every such selector. These definitions
use classical choice to retain the executor's proved result. They are
proof definitions, not a replacement Haskell executor.

## Remaining correspondence work

These results prove finite allocation, finite physical request inventory,
and bounded ancestor-fresh descent for the cold structural fragment.
They do not yet provide an extracted stateful implementation of the full
`nodeEdges` and `subsumes` call tree. That bridge must show that the actual
ordered helper calls form a generated schedule and that the source's
ancestor and visited sets enforce the proved repetition conditions.
It must also retain the source's unresolved-union-reference error case.

The schedule contains unfolding effects. It does not permit arbitrary
ordinary construction between requests. The existing prepared merge
context theorem treats those later constructor effects separately.
The results do not prove termination of repeated outer merge passes or
remove the open nested Mu preparation boundary.

## Validation

The pinned Lean 4.34.1 build checks `MicroCFTA.MergedColdExecution`, which
imports both other cold modules. The isolated imported-theorem audit
accepts only `propext`, `Classical.choice`, and `Quot.sound`.
The validation transcript is `/tmp/mcfta-merged-cold-audit.log`.
