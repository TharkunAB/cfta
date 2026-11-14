# The real source no-stop entry and the next missing branch

Frozen: 2026-11-15 00:11 CET. This candidate is uncompiled.
Candidate: `SourceSynthesisCurrentNoStopSourceEntry.lean`.
SHA-256: `1354b6239a9ed05a9ef35cab3aa96372495d22ed7ceb6c372f278637425e5c8f`.

## Concrete result

`accepted_no_stop_eager_entry` consumes the same accepted raw source and
its exact original build, including the same stored U at that source heap.
It derives the original empty-cache guard preparation, physical fields,
and cold caller `Context` from the checked source initializer. The proof
identifies the initializer's chosen build with the supplied original
build by determinism. It does not assume a caller context or force result.

The accepted source factory has an ordinary node request at its root.
The physical root is therefore empty or an ordinary node. Its recursive
boundary flag is false. Complete available readback supplies its actual
initial handle. The no-stop, no-preference selector expands slot zero.

The theorem gives the literal configured `runEager` equality to
`resumeWithChild` at that actual expansion. It retains the same cold caller,
original inventory, global query memo, source root, stored U, work fuel,
recursive fuel, metadata, graph, templates, key functions, and eager child.
The real `SourcePruningOuterNarrow.narrow holeKey fits admits` remains in
the operation. No identity-narrowing substitution occurs.

## Exact next missing observations

At positive recursive depth, the actual `resumeWithNarrow` definition calls
the selected prefix with the real outer narrowing operation. The continuing
preparation branch requires an actual observation of this form:

```text
SourcePruningEnumerationSelectedStep.runPrefix
  holeKey fits admits graph templates none noPreference metadata
  workFuel workFuel workFuel workFuel workFuel workFuel
  0 coldCaller startup globals.query
= .narrowed checked narrowed reached saved
    (some [.ok ((), actionCore)]) (some candidate)
    (some [.ok ((false, updated), callbackCore)]) none
```

The ordinary shared row scan then requires the actual preparation:

```text
SourcePruningEnumerationSelectedPreparation.run
  entryFuel preparationFuel 0 reached candidate
= ([.ok ((target, readHandle, scs, decoded), entered)],
    some (.done parent@(.node ..) preparedHeap))
```

The public `initial_prepared_shared_root_scan_origin` consumes these
observations and exposes the actual shared row scan. Its literal branch
uses `SharedChildVisitors.visitCapturedWith` and
`SharedPreparedChildPolicy.runWithChild`. Its actual row and first-child
outcomes must then connect to the public first-goal-child theorem.

This packet does not assume either missing observation. It does not claim
that a visitor reaches a row or a first child. Recursive fuel zero stops
before the selected prefix. Work fuel can be insufficient. An accepted
raw source can construct an empty physical root, so acceptance alone does
not justify unconditional ordinary-row visitation.

## Identity and backend boundary

`accepted_initial_identity_prefix` computes a prefix for the explicit
identity narrowing function. The default configured `runEager` calls the
real outer narrowing operation. The identity prefix does not establish
the real prefix outcome without a separate equality or actual operation
proof. This packet uses no identity-prefix equality and no legacy/shared
worker equivalence.

The theorem closes only the actual original-source initialization and
selection connection. Primary worker history and compatible finite budgets
must establish the missing real prefix and preparation branches. The
source-position worker target and all full original clauses remain open.
No future result context, old-node-none fact, force success, provenance,
atom closure, trace, or reachability provider is added.

## Validation

`PROBES.lean.txt` lists the exact public probe name. `PINS.txt` records the
read-only source snapshots. Root owns compiler checks and publication.
No compiler, live source, Git, board, Haskell, or `/tmp` action occurred.
No Haskell fix was found. Every older packet remains immutable.
