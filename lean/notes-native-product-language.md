# Exact native product language, Sized classes, and minima

The later [cold native Sized proof](notes-cold-native-sized.md) completes
literal compiler composition and derives raw child-key closure and final cache
metadata. It supersedes compiler next-target statements in this checkpoint.

See [complete native scans](notes-native-full-scan.md) for the later warm
completion, exact early return, and full ordered ambiguity scan. Literal
compiler composition is next. Older next-target statements below are historical.

Updated: 2026-10-14 21:24 CEST.
Rebased proofs: `dab197d2`, `70289150`, and `ede5f85a`.

## Complete recursive correspondence

`SourceRecursiveIntersectionKernel.execute_schedule_replay` proves the full
bounded kernel correspondence. It uses actual completed allocation-free
calls in one valid final cache. Induction on kernel fuel retains that cache.
The reference schedule uses twice the kernel fuel. This includes the extra
edge-worker level. Successful reference results remain exact at larger bounds.

The induction retains `NodeScope`, actual domain residency, and canonical
seen pairs. `onNode_schedule` covers every source branch. The ordinary case
retains the exact hash-join order, right-bucket reversal, and duplicate rows.
Mu entry retains the exact canonical domain and both original bindings.
Original body and reference readback supply every recursive operand.
Actual node, union, and binder normalization supply output language.

`execute_schedule` uses actual completed replay and heap/history growth to
recover the original input view. It does not assume the correspondence of
recursive child calls. The whole bounded induction derives that property.

## Exact product language

`SourceRecursiveIntersectionKernel.execute_product` identifies the derived
reference result with the finite exact original-input schedule. Closed
input and result support remove dependence on the reference environment.
The result accepts exactly the common finite terms of its original inputs.
The generic kernel entry requires its final independent-language probe heap.

`SourceRecursiveIntersectionNative.native_product` starts from actual checked
native completion. Native evaluation derives that final heap from its
initial heap. The theorem retains actual source validity, closed original
available inputs, checked `WordRanges`, semantic heaps, and exact Boolean
guard conjunction. No completed kernel run, body correspondence, row relation,
or product-language equation is supplied at this native entry.

Both raw and smart stored binders retain their existing independent language.
Different physical child identities and redundant rows are permitted.
The preserved functional and exact-row counterexamples remain valid.
They do not refute the derived language theorem.

## Finite tables and Sized

`cold_node_table_product` composes actual first native completion and finite
repaired cold extraction with the product theorem. The output table accepts
exactly the common original-input language. This holds for every guard
interpretation that respects the actual conjunction operation. Both native
and row collection bounds are stable. No output preparation is assumed.

`constructed_node_table_product` derives every source heap invariant from a
completed repaired empty-cache construction. Actual source operands remain
closed, original, and available. Domain-cache validity and `WordRanges` remain
explicit. The theorem supplies native completion and the finite cold trace.

`constructed_product_sized` uses that actual table in the reference Sized
worker. It proves distinct accepted terms at every node-count size, finite
class evaluation, size-major distinct prefixes, complete rank coverage, and
both distinct-term rank/unrank inverse laws. Accepted support is exactly the
common language of the two original inputs. The table retains its source row
order. The rank counts distinct terms, including on ambiguous product graphs.

The primary finite-map reference, solver-decided, and optimized dispatcher
proofs remain. The optimized interned core remains unchanged.

## Exact structural minimum

`constructed_product_minimum` runs the actual finite minimum recurrence on
the native cold table. It derives finite convergence and a stable sweep.
Every root minimum is precisely the least common structural term size.
`SourceRowsMinimumAdapter.productiveRows` is true exactly when the original
inputs have a common structural finite term. Constraints are erased only
for this structural test. No predicate on `emptyGuard` is needed because
the actual arity-mismatch row has an empty child.

This theorem covers the raw-table root-row precheck. The live compiler uses
`null (nodeEdges node)` before minimum lookup in
`cfta-generator/src/Data/CFTA/Gen/Internal/Automaton.hs`. Its complete
ordered scan still needs composition with actual repaired exposure.
The actual prechecked callback now has exact finite execution and Boolean
readback. See [native source-key callbacks](notes-native-key-callback.md).
The standalone `Data.CFTA.Sized.unambiguousRows` uses the explicit synchronous
product. Its existing proof does not depend on this separate native path.

## Next target

Connect actual native overlap callbacks to the complete finite source-key
ambiguity scan and its compiler result. Use language and Boolean equations.
Do not derive the refuted general functional or exact related-row adapter.

`done_node_table_exact` now retains finite cold extraction after any
completed checked native call, including warm memo states. It derives all
final heaps, coverage, resident and replayed rows, exact finite keys,
stable collection bounds, and complete independent table language.

`SourceFreshOrdinaryColdProductivity.prechecked_table` follows actual
root exposure before row collection. `done_node_productivity` now composes
native completion, finite actual exposure, collection, and minimum sweeps.
Its Boolean holds exactly when the original operands share a structural term.

`SourceFreshOrdinaryColdKeys` derives closed original physical operands and
their complete language from actual input-table metadata. The finite carrier
retains those exact languages. `SourceFreshOrdinaryNativeKeyCallback.completed`
proves that each actual native callback equals the finite reference product
test. No literal product rows or supplied product-language law are used.
`physical_grows` retains identical operands after cache growth.

`SourceFreshOrdinaryColdMemoState.prechecked_advance` retains valid unchanged
native memo tables through the actual exposure and collection effects.
Every heap needed by the next callback remains. Next compose the full ordered
scan and literal compiler result. Successful warm-call execution still needs
its reachable completed memo-state condition. General completed warm-call
correctness is already proved. Read [native source-key callbacks](notes-native-key-callback.md).

Concrete Haskell containers, lazy scheduling, source extraction, and external
solver contracts retain their documented scope. No theorem count or green
build verifies those boundaries. The whole Haskell library is not verified.

## Validation and preservation

The aggregate audit passes 1,513 jobs and 44,104 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Log: `/tmp/mcfta-cold-memo-state-20261014-audit.log`.
No new warning was introduced. The old unused `inputs` warning remains.
No production Haskell code changed. All fixtures and marked drafts remain.
Everything remains local. No worker is active.
