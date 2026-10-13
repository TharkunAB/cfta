# Complete adaptive physical merge worker

Stable on 2026-10-13 at 14:21 CEST:

- `MergedAdaptiveEffects.lean`
- `MergedAdaptiveColumns.lean`
- `MergedAdaptiveEdges.lean`
- `MergedAdaptiveGroups.lean`
- `MergedAdaptiveMerge.lean`

Lean 4.34.1 compiled these modules and their dependencies, 344 jobs.
`worker_complete`, `execute_complete`, and `execute_ne_none` use only
`propext`, `Classical.choice`, and `Quot.sound`. The axiom report is
`/tmp/mcfta-adaptive-worker-axioms-20261013.log`.

`MergedAdaptiveMerge.execute` is the complete state-dependent worker.
It uses the input's ordinary height as its derived recursive fuel.
`execute_complete` proves that every prepared available input returns an
actual value and state. Its result certificate derives:

- The final prepared context.
- Growth of the actual constructor and record caches.
- Preservation of all earlier available records.
- Availability of the returned complete record in the actual final cache.
- Inclusion of the original finite-term language in the returned language.

No `CallLaw`, recursive semantic law, or termination premise remains in
`execute_complete`. Induction on the derived height supplies each recursive
call. `execute_ne_none` excludes fuel exhaustion under the same input
conditions. The proof does not require output-height monotonicity.

An ordinary closed root processes its current canonical rows. Groups of at
most four retain each source guard and recursively process each child.
Larger groups process child columns and build one unconstrained edge.
Each column reads the actual cache left by earlier columns. It derives the
comparison fuel from the square of the current physical inventory length.
The physical checker justifies the recursive-operand filter. Ordered
identity removal then retains the complete source records. A singleton
returns unchanged. A recursive or union boundary uses actual `makeUnion`,
which models the repaired source `createUnion`. Other closed operands use
the actual ordinary union and one smaller recursive merge call. Actual
edge and parent interning complete the result.

Recursive, union, primitive, and open ordinary boundaries return unchanged.
The result uses the prepared physical epsilon graph. Its initial `Context`
and `Available` premises remain explicit. It does not extend the proven
stored-body preparation fragment. The full guard interpretation, its
unconstrained-row test, and the meaning of the supplied Top guard remain
parameters. HashMap group order remains a parameter. The structural
`Grouping` contract pins each full symbol/arity class, original order
within that class, and permutation of the original canonical rows.
The theorem does not assume a semantic grouping property.

This closes the earlier composition gap between finite state-independent
`Work` callbacks and comparisons chosen at each actual current cache.
It is a complete physical model of the worker. It is not a mechanically
extracted Haskell program. The outer memoization wrapper, concrete HashMap
implementation, and concrete guard interpretation remain source
correspondence boundaries. Repeated equality fixed-point termination is
still separate. No production source file changed in this step, so the
existing 620 Haskell example results at `c76d1ec` remain the source tests.

## Completed proof: extra-fuel independence

`MicroCFTA/MergedAdaptiveStability.lean` now compiles with Lean 4.34.1.
The build includes 345 jobs. The original unfinished draft remains unchanged
at `MicroCFTA/MergedAdaptiveStability.lean.incomplete`. It is not imported
by the stable modules and is not a Lean build target.

`worker_refines` proves that extra recursive fuel preserves the exact
returned record and final cache of every successful run. Its zero-fuel
induction case splits the later fuel before it reduces the value cases.
The proof composes action, column, edge, group, and root trace preservation.

`successful_results_eq` proves that any two successful fuel choices return
the same complete record and cache. It requires no availability, prepared
context, guard interpretation, or grouping premises.

`enough_eq_execute` proves exact equality with `execute` for every fuel at
least the original input's ordinary height. It uses the existing prepared
context and available-input completion premises. These results concern
recursive fuel within one invocation. They do not prove termination of
repeated equality fixed-point iteration.

The three stability theorems use only `propext`, `Classical.choice`, and
`Quot.sound`. The checked axiom report is
`/tmp/mcfta-stability-axioms-20261013.log`. The preserved draft has SHA-256
`a8f71bab5b99af984c89a793cf0f153dade7fa1163fa3f18ed14e0cd08abddc9`.
