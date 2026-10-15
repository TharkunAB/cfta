# Sized execution from a validated finite row map

The [native demand checkpoint](notes-native-checked-demand.md) passes 1,945
audit jobs and 50,309 theorem dependency checks. It adds checked native
execution with retained operation caches and surrounding memo cells. Completed
semantic provenance and actual heap preservation remain open. Sized and
canonicalClasses are unchanged. Exact classes, finite execution, sequence,
size order, and both signed inverse implications remain separate contracts.

The [checked-edge allocation checkpoint](notes-checked-edge-allocation.md)
passes 1,936 audit jobs and 50,146 theorem dependency checks. It adds source
constructor receipts and preserves recursive memo cells. Complete native
child-demand correspondence remains open. No Sized or Haskell definition
changed. Exact classes, finite execution, sequence, size order, and both
signed inverse implications remain separate contracts.

The [allocation receipt proof](notes-payload-allocation-receipts.md) preserves
Sized and canonicalClasses. Exact classes, finite execution, canonical order,
distinct size order, and both signed inverses remain separate contracts.
The aggregate audit passes 1,929 jobs and 50,083 theorem dependency checks.
Older counts below describe historical checkpoints.

The [physical identity bridge](notes-constraint-identity-renaming.md) adds
conditional result-memo correspondence. Sized and canonicalClasses are unchanged.
Exact classes, finite execution, size order, and both inverses remain distinct.
The aggregate audit passes 1,918 jobs and 49,920 theorem dependency checks.
Older counts below describe their historical checkpoints.

The [completed result-memo proof](notes-result-memo-soundness.md) adds actual
recursive language and cell preservation. It leaves Sized and canonicalClasses
unchanged. Exact accepted classes, finite execution, canonical sequence,
distinct size order, and both signed rank inverses remain separate contracts.
The aggregate audit passes 1,914 jobs and 49,869 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. Log:
`/tmp/mcfta-memo-invariant-audit-20261015.log`.
Older audit counts below describe their historical checkpoints.

Upstream `c351674e` moves canonicalClasses to Data.CFTA.Interned without
changing its implementation. Sized changes only that import. Existing exact
classes, finite execution, size order, and both rank inverses retain their
source definitions. The optimized dispatch still returns the reference
sequence. Read [the upstream comparison](notes-canonical-upstream.md).
The aggregate audit passes 1,902 jobs and 49,621 theorem dependency checks.
The later upstream refresh to 33148e6d leaves Sized and canonicalClasses
unchanged. Its retained traversal repair is identical to the local repair.
The refresh to main 239feb64 also leaves those source definitions unchanged.
Read [the source comparison](notes-main-refresh-20261015.md).
The refresh to main `1eb4ab05` also preserves Sized and canonicalClasses.
Its applied-name sort inference changes the solver adapter. The additive
`SourceSizedFiniteKeysAppliedLiquid` endpoint now runs the current full encoded
preparation on the actual original-state raw fold. It preserves exact size
classes, finite outcomes, source order, prefix coverage, and both inverse laws.
Read [the current source comparison](notes-main-1eb4ab05.md). Historical fixed-
preparation endpoints below retain their older meaning; app-free compatibility
is proved. The new named-measure frontend remains an uncovered source bridge.
Later counts in this note are historical component evidence.

The common full query specification now covers original-map reference,
optimized, and actual bounded encoded solver paths in `221bb23a`.
Read [the common API note](notes-sized-api-laws.md). The current aggregate
audit passes 1,554 jobs and 44,359 theorem dependency checks. Later counts
in this note describe historical component checkpoints.

A finite FTA can use an infinite state type such as `Nat`. The earlier public
input contains a complete finite state carrier. This work constructs that
carrier from the actual validated map keys. It does not require every value
of the original state type to occur in the map.

`SourceSizedFiniteKeys` reads the original raw row table. Successful
`FTAValidation.validateRows` supplies root membership and closed children.
The derived subtype retains symbols, complete constraints, repeated children,
and every alternative in its original order. Unreachable and dead rows remain
present for canonical refinement. Acceptance and ordered first-occurrence
size classes have exact original-state readback.

`SourceSizedFiniteKeysCanonical` follows the actual dense numbering used by
`Sized.sortedRows`. It proves canonical class equality at each numbered key,
exact sort-key equality, and complete sorted-row readback. The order proof
requires lawful symbol comparison. It includes tied transitions.

`SourceSizedFiniteKeysTrim*` transports each structural productivity round,
live-row filter, successor list, and reachable-state round. The resulting
inventory is exactly the actual raw `trimKeys` list, in order, with the root
retained even when it is unproductive. Complete trimmed constraints also
have exact readback.

`SourceSizedFiniteKeysExecution` derives equality of actual candidates,
constraint/term pairs, filtering, duplicate removal, insertions, state folds,
and signed bounded size folds. This includes the first error.
`SourceSizedFiniteKeysOperational` transfers relational class, state, and size
traces with the same occurrence work. It preserves varying evaluator replies,
Unknown, and unchanged raised failures.

`SourceSizedFiniteKeysPublic*` connects the original raw language to all four
public queries, the reference and decided paths, exact bounded coverage,
distinct size order, and both rank inverses. Raw `ActiveOption` facts derive
the trimmed finite-row invariant. No input correspondence law is assumed.

`SourceSizedFiniteKeysNativeLiquid.NativeRun` runs the original raw sorted
rows at the actual raw trim keys. `trace_readback` connects this execution to
the finite public input. `encoded_correct` proves exact independent ambient
logical acceptance, original canonical sequence, complete bounded prefixes,
and both signed inverse laws. `encoded_finite` derives finite outcomes from
finite actual encoded external attempts. It includes errors. Neither theorem
requires a finite original state type or a stable external reply function.

`SourceSizedFiniteKeysDispatch*` now derives raw constraint scans, sorted
row uniqueness, the actual raw key-pair synchronous product minimum test,
and its finite convergence. `nativeSized_eq` proves equality of the entire
public result, including errors and all four query functions. `native_success`
retains the canonical reference sequence. No opaque product-gate premise
remains. This gate uses explicit graph intersection; it does not depend on
native interned recursive construction.

## Finite optimized rank queries

`TablePositionCountBound.positions_congr` proves that ranking a finite term
reads no count above that term's node count. This includes child products,
failed child lookups, last-write selection, and offsets for earlier transitions
that do not accept the input term. The result does not require correct count
values to establish its size bound.

`TablePositionFiniteEvaluation.finite_rank` constructs a finite count inventory
and finite child maps. Every count has a finite recurrence derivation. The map
worker reads only that inventory and returns exactly `TablePosition.positionsOf`,
including failure. The graph can be cyclic and the state type can be infinite.

`SourceSizedFiniteKeysRankEvaluation.raw_finite` derives the inventory from the
actual original map keys and canonical rows. `native_rank_laws` identifies its
root result with the actual optimized public query and both signed inverse
laws. The optimized branch's ordinary constraint scan and product gate remain
explicit premises. This proof does not replace the source worker with an eager
Haskell implementation. Concrete lazy heap scheduling remains a runtime boundary.

Earlier checkpoints: `5f79d22e` and `bc7599d4`. The finite inverse proof is
`51242646`. The current audit passes 1,204 targets and 40,032 theorem dependency
checks using only the three permitted Lean
foundations.
Log: `/tmp/mcfta-cold-complete-20261014-audit.log`.
Concrete Haskell containers, lazy heap execution, primitive machine resources,
and external solver behavior retain their stated contracts.

`SourceFirstOrderSharedRows.source_sized` now supplies exact reference size
classes from actual repaired first-order recursive construction and explicit
finite warmup. The shared table has the original guarded physical language.
Native cold shared traversal allocation order remains separate. See
[first-order shared rows](notes-first-order-shared-rows.md).

`SourceFirstOrderColdSized` now derives the actual cold table without warmup
or a supplied trace. `SourceColdSharedRowsTermination.cold_finite` proves
finite stateful traversal in every prepared closed source cache. The cold
output language is exact. `Trace.native_correct` and `Trace.liquid_correct`
compose the actual returned table with canonical native and encoded
solver-decided queries, finite classes, and both signed inverses. Validation
and external solver contracts remain explicit. See
[cold shared rows](notes-cold-shared-rows.md).
