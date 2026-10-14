# Complete native callbacks and actual ordered ambiguity scans

Updated: 2026-10-14 21:48 CEST.
Proofs: `3dd34cb7`, `5de26f4b`, and `53ba5057`.
Source base: `7bfb69d1` (PR #129). All work remains local.

## Warm native completion

`SourceRecursiveIntersectionNative.Idle` means that neither native memo
family has an evaluating cell. Suspended and returned cells are permitted.
`idle_initial`, `Idle.advance`, and `done_idle` derive the reachable idle
condition before calls, after source cache growth, and after completed body
code. This property does not require empty memo tables.

`warm_node_terminal` uses the actual initial input view and the finite
semantic request bound. Idle supplies every active-bound condition.
`warm_node_complete` uses complete semantic heaps to exclude pending
construction. It derives a finite successful native return, checked kernel
correspondence, coverage, Idle, and exact larger-bound stability.
No native completion or whole product-language equation is supplied.
Per-request `WordRanges`, actual source validity, and closed Original
available operands remain explicit. Native completion for valid idle warm
states is proved. Do not repeat the initial-memo success proof.

## Exact callback control and state

`SourceFreshOrdinaryNativeCallback.Ready` collects native validity, Idle,
semantic heaps, coverage, open-depth heap, guarded probe heap, and guarded
budget probe heap. These are the invariants needed by the next callback.

`Execution` records the actual source callback. It first completes native
intersection and then root exposure. If exposure has no edges, the empty
constructor returns false immediately. The native machine receives the exact
exposure cache. Row extraction and minimum lookup are absent from this path.
For nonempty exposure, the done constructor records finite actual collection
and minimum sweeps, then returns the actual root-minimum Boolean.

`complete` derives an execution from Ready and checked words. It returns
Ready, actual machine extension, and the exact common structural finite-term
Boolean. `Execution.unique` proves identical returned Boolean and cache for
all successful native, exposure, and collection bounds. It includes both
control branches. `Execution.correct` transfers the derived result to every
actual completed execution. The independent native product theorem supplies
common-term language; it is not an assumed interface.

The earlier unconditional cold-table wrappers remain useful auxiliary
finite readback certificates. They must not define early-return control.
The initial callback relation evaluated those auxiliary phases in all cases.
`53ba5057` tightens only the formal execution relation. The live Haskell
already skips them after empty exposure. No Haskell runtime bug was found.

## Actual finite input keys

`SourceFreshOrdinaryNativeKeyCallback.complete_keys` starts from actual cold
input-table metadata. Resident rows derive closed original canonical physical
operands. Complete guarded table language identifies each finite state.
Later cache growth retains availability of the identical original operands.
Every checked query from a later Ready cache has finite actual callback
execution and the literal reference finite-product Boolean. The theorem
returns the exact next cache and machine extension. Native completion and
product-language equations are derived rather than supplied.

Input child-key closure, replayed rows, resident rows, declared children,
complete final-cache semantic heaps, and the exact finite map domain retain
their explicit types. Actual general cold tables derive those row and heap
invariants. The compiler still needs its normalized source-constraint check.

## Actual ordered scan

`SourceShortCircuitScan.Run` models all and any with an actual callback
relation and sequential state. It stops at the first decisive result.
`Ranges` checks the current query and only the suffixes reached after a
continuing actual callback. It does not assert callback completion.
The completion and correctness theorems preserve that exact order and state.

`SourceFreshOrdinaryNativeKeyScan.Step` is the complete actual native callback
on canonical physical input operands. `Invariant` retains Ready and the
original input cache history. `children_complete` and `children_correct`
connect the ordered zip-and scan to the reference child-overlap Boolean.

`EdgeExecution` rejects a different symbol or arity without callbacks.
Matching pairs execute the child scan. `edgePairs` models the ordered tails
comprehension. `edgeQueries` preserves map-key order and each row's pair order.
`scan_complete` derives finite actual all-row ambiguity execution.
`scan_correct` proves the literal reference ambiguity Boolean for every
completed run. Every executed callback passes its exact cache to the next.
The proof does not assume a native completion, a scan equality, a product
language, or either refuted exact-row adapter.

Word checks remain explicit at actual reached queries. Do not replace them
with a universal bound on arbitrary future heaps. Such a bound can be stronger
than the finite source run. No extra callback runs after a decisive result.

## Next compiler target

Construct the cyclic source input directly from the actual finite raw table.
Derive root membership, child-key closure, and retained constraint records.
The actual empty, open, and constrained checks must keep source precedence.
After the constraint check, derive equality between guarded and structural
rows. Apply the actual scan theorem and prove literal compiler-result equality,
including errors and canonical preparation. Reuse existing size classes,
finite evaluation, distinct size order, and both rank/unrank inverse laws.

`SourceCyclicRowsReadback.input` and `original_eq` show the existing row-record
conversion. They currently use the older snapshot toRows boundary.
`SourceCyclicRowsNativeGate.plain_rows` supplies guarded/structural equality
after plainness. Avoid adding an assumed whole input or product language.
The native root-table metadata already supplies canonical closed records.
No functional or exact related-row product adapter is needed.

The primary explicit-graph `Data.CFTA.Sized` reference, solver-decided,
optimized dispatcher, ordering, and inverse proofs remain complete at their
stated source-model layer. Concrete containers, lazy scheduling, verified
Haskell extraction, and external solver correctness remain their own boundaries.

## Validation

The full audit passes 1,520 jobs and 44,155 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Log: `/tmp/mcfta-native-early-scan-20261014-audit.log`.
No new warning was introduced. The old unused `inputs` warning remains.
No production Haskell code changed. The unchanged source base previously
passed 289 core, 209 generator, and 147 refinement examples, all five updated
probes, and both formatting checks. Those checks were not repeated for these
Lean-only changes. Fixtures, marked drafts, stashes, and worktrees remain.
