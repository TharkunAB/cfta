# Same-handle native edge writers and causal heap growth

The new module is SourceCurrentNativeEdgeWriterGrowth.
All earlier source and evidence files stay unchanged.

Written takes an explicit owner handle, original request, returned result, and current reader heap.
It retains the actual body-start and body-finish states.
The same explicit handle is evaluating in both states.
The literal protected finish uses that same handle.
The receipt proves Grows from both writer heaps to the current reader heap.
Written.writer projects the earlier request/result-only Writer.
Written.grows composes actual later growth without changing the captured handle.

History starts with empty native tables.
Its trace constructor records an actual completed checked trace with Clean, Good, and Fields.
Its advance constructor records the exact advancePhysical state update and past heap growth.
advancePhysical leaves the entire edge-cell function unchanged.
The explicit Grows premise belongs to that past advance event.
It is not a desired writer law or a future-completion premise.
History.forget projects to the earlier persistent History by dropping the extra growth fact.

History.writers is a producer for every current returned cell.
The proof uses strong induction on the actual trace length.
Work and optional-binder steps transport earlier receipts by their derived physical growth.
Lookup and demand retain the current heap and the handle of each old returned cell.
The protected cold finish constructs a new Written at the exact captured handle.
Its body-start growth comes from actual body effects.
Its body-finish growth starts with reflexivity and is transported through later actual effects.
No public producer assumes a predicate that already states these writer facts.

History.query derives the clean-code and field certificates for a completed literal node request.
History.warm uses actual lookup and ready-demand equations.
The physical readiness and key checks identify the full original request.
The conclusion uses the selected handle itself.
It does not replace that handle by an unrelated existential writer handle.

Grows here is InternedConstructorTemplates.Grows.
It extends both identity tables and both record tables.
It does not include issued-node history, a numeric allocation bound, operation-cache growth, or domain-cache growth.
The writer receipt does not assert those stronger facts.
A past advance also does not produce Good at its output.
A later checked trace must provide its own initial Good and Fields.
The receipts do not expose a global root-prefix embedding of the writer event.

The constructed integration builds its own closed source with a productive Mu.
It completes a literal cold native edge request and publishes handle 0.
It allocates an unrelated physical edge and derives the past growth fact from actual work effects.
It advances the same native tables with advancePhysical.
It proves the exact same-state warm edge trace at the new heap.
It then obtains Written for handle 0 and projects the older Writer and History.
The native edge fixture has zero children. The source construction contains Mu, but this fixture does not run a recursive native child call.

Direct1 passed with an empty log. Canonical1 passed for the single module.
Public1 checks eight handwritten declarations and three History constructors.
Kernels1 adds one no-premise constructed integration.
The selected total is twelve pairs in two probe groups.
Every probe uses all eight print options, complete signatures, proof output, and axiom output.
Only propext, Classical.choice, and Quot.sound occur.
There is no failed-to-pretty-print output.
Actual memory.max and memory.high are 4 GiB. Actual swap is zero.
All first attempts passed. No failed execution was discarded.

This component records causal provenance of past checked execution.
It does not produce general query completion or a global outer progress measure.
