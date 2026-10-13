# Sized execution from a validated finite row map

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

Checkpoints: `5f79d22e` and `bc7599d4`. The closing audit passes 1,180 targets
and 39,689 theorem dependency checks using only the three permitted Lean
foundations.
Log: `/tmp/mcfta-closing-20261014-audit.log`.
Concrete Haskell containers, lazy heap execution, primitive machine resources,
and external solver behavior retain their stated contracts.
