# Complete cold source merge worker

The following modules compile with Lean 4.34.1:

- `MicroCFTA/MergedColdMerge.lean`
- `MicroCFTA/MergedColdMergeCompletion.lean`
- `MicroCFTA/MergedColdMergeStability.lean`
- `MicroCFTA/MergedColdMergeSoundness.lean`
- `MicroCFTA/MergedColdMergeBounds.lean`

The joint dependency build includes 360 jobs. The completion and stability
theorems use only `propext`, `Classical.choice`, and `Quot.sound`. The audit
is `/tmp/mcfta-cold-merge-axioms-20261013.log`.

`MergedColdMerge.worker` executes the actual ordered cold source filter in
each large-group column. Its result retains the exact cache on success or
failure. It processes groups of at most four rows with their original
guards. Larger groups process child columns in order and build a Top-guard
edge. Each column finishes `MergedSourceSelection.select` before it checks
the retained singleton, recursive/union boundary, and ordinary-union
branches. Actual edge and parent interning complete the result.

The worker has two proof fuel parameters. `execute` derives ordinary
recursive fuel from the original input's ordinary height. Comparison fuel
is uniform across the run. `execute_complete` proves that there is a finite
comparison bound above which the exact returned value and cache stabilize.
The bound follows from actual cold comparison completion at each demanded
cache and finite ordered sequencing. It is an existence theorem for a
stable bound, not an executable closed-form bound.

The result certificate derives final `Facts`, final `Prepared`, growth of
the actual constructor and record caches, extension of issued references,
preservation of every earlier available record, and availability of the
complete returned value. No recursive callback or `CallLaw` premise remains.
No initial `Ready`, warmup outputs, or prepared observation replaces the
runtime input. Initial `Facts`, `Prepared`, and available input remain
explicit. The stored-body preparation fragment is unchanged.

Generic completion accepts the exact structural `Grouping` contract.
`source_execute_complete` supplies it from `MergedSourceGrouping.groups`
and `groups_correct`. Outer HashMap bucket order remains a source
representation boundary. Original row order within each full symbol/arity
class and the four-row threshold are explicit in the model.

`worker_refines` proves that increasing either fuel preserves every
successful returned value and exact final cache. It has no availability,
preparation, grouping, or semantic premises. `successful_results_eq` proves
that any two successful choices of both fuels return the same complete
record and cache. `worker_saturated` derives one comparison bound that
works uniformly for every ordinary bound at least the original height.
`successful_verified` transfers the derived final facts, preparation,
growth, history, and result availability to every successful fuel choice.

`MergedColdMergeSoundness.source_execute_complete` now derives language
inclusion in the actual returned cache and every later common extension.
It derives each recursive certificate by ordinary-height induction. Concrete
grouping needs no supplied partition premise. A sound clear-guard test and
true Top guard remain explicit. `source_successful_sound` applies the result
to any successful pair of fuel choices. `MergedColdMergeBounds.group_bound`
separately proves that each successful group returns at most four rows.

These results do not assert language transfer from an arbitrary cold input
graph to a different final graph. Repeated equality fixed-point termination,
the outer memoization wrapper, and complete Haskell source correspondence
remain separate.
