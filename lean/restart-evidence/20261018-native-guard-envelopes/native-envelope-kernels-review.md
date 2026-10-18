# Source-built native guard envelope integration

Reviewed on 2026-10-18 at 06:05 CEST. This component contains one constructed endpoint. It changes no production source.

## Exact initial data

The fixture copies the source-construction prefix from `20261018-selected-read-producers/native-writer-kernels-2.source.lean` into a new namespace. It allocates the equality field and the plain field before it builds the syntax. The source has two distinct closed resident Mu values. The left body has a base row and a recursive repeat row. The right body has two finite rows. Both syntax binders use `binder false`, so the unused right binder remains a Mu record. The query uses the Mu children directly, rather than their ordinary wrapper nodes. Their physical references differ.

The fixture derives the initial native Ready, inventory, causal Plain guard heap, full Frame, and scalar Fits from the actual source build and field allocation. It derives Room 128 from the checked source counters. Formulas and solver remain parameters. No future receipt, graph, heap bound, finite alphabet, or successful output is an input to the constructed theorem.

## Actual native execution and computed bound

The literal `execute 128` query succeeds on the two Mu operands. Its result is nonempty. The returned native node counter is greater than one and the native edge counter is positive. Both native tables start empty. These assertions establish nontrivial native node and edge work.

`SourceCurrentConjunctionGuardUniverse.initial` derives membership in the finite guard alphabet of the source heap. `SourceCurrentGuardHeapBounds.initial` derives its initial flat guard bound. `GuardHeapBounds.alphabet` supplies the computed bound for each alphabet member. `NativeGuardEnvelope.complete` constructs its own query receipt and final guard heap bound from these initial facts. `AllocatedNativeColdClosedExact.completed_unique` aligns that computed completion with the literal 128-fuel execution. It identifies both the full returned Value and the full checked state. The final receipt and guard bound therefore refer to the literal execution endpoints.

The returned bound iterates `GuardLimits.step` for the initial `instructionBound profile.nodes profile.edges profile.mass`. It bounds the current raw physical guard fields. It is not a hereditary guard-origin relation, a bound on child indices, or a bound for a complete outer recursive execution. The fixture makes no finite Cap or finiteordinary claim and does not exercise resident_precheck, Parent, or Haskell execution.

## Frozen evidence and limits

The selected printer-free check is `native-envelope-kernels-2`: exit 0, log size 0 bytes, source SHA256 `e6914b08f9029bc98aa5e0a4dea13d5ccc6d645fcfa0a11500c7fa3ddd460687`. Preliminary source prefix check 1 also succeeds and remains preserved. There are no failed attempts in this component.

The selected group is `native-envelope-kernels-public-1`, with one full `#check @`, `#print`, and `#print axioms` pair for `MicroCFTA.NativeEnvelopeKernels.distinct_recursive_query`. It has all eight required options, no printer omissions, and only the standard three axioms. The public theorem is an exact typed alias of a checked private witness. Its output has 36,178 bytes.

Every check executes its immutable numbered snapshot with pinned Lean 4.34.1 and `-Dlinter.all=true`. The inner worker records MemoryMax 4,294,967,296 bytes, MemoryHigh 4,294,967,296 bytes, and SwapMax 0. The selected strict and printer checks record peak memory of 541 MiB and 568 MiB. The cap is five minutes.

## Production pins

- `SourceCurrentGuardHeapBounds.lean`: `4ceb89af54411a9c4625544572b6a683bb6cad1bd1082651f72e1b94ff937a53`; direct 2 has a zero-byte log; canonical 1 succeeds with 1,465 jobs.
- `SourceCurrentNativeGuardEnvelope.lean`: `f59271e880b1502fdd97cb81718050c6cc5921ec599dee0c4bff6e3be47d16d9`; direct 1 has a zero-byte log; canonical 1 succeeds with 1,422 jobs.

Both canonical logs replay the unchanged `InternedFreshOrdinaryClosedCompletion` warning. Neither selected source strict log contains a warning. This component does not count the production public declarations, which have separate component evidence.
