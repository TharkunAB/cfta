# Proposed genuine-packet cluster completion

This is a precise prose contract. No new Lean header or body is supplied.
Working future theorem: MicroCFTA.SourceCurrentOriginalRowClusterCompletion.cluster_complete.
Use the SAME Symbol and Guard types and the existing DecidableEq Symbol/EdgeKey instances from H15/H16.
Fix bits, source : InternedConstructorTemplates.State, source Facts, executable formulas and solver.
Fix the public guardHolds expression with FormulaExecutable.formulaDecidableEq, InputMeaning(view source guardHolds) and RankedInput for that SAME view/model.
Fix ONE parent : Value with OriginalInput source (inputOf parent), Available source parent and parent.free = [].
Fix one symbol and define rows EXACTLY as (nodeEdges parent).filter (fun edge => decide (edge.entry.key.symbol = symbol)).
Fix initialDomains : Cache.State DomainKey, initialValid : Cache.Valid initialDomains and I := SourceInventory.domains source.
Take before : H7.State(bits+2) with actual Good before.checked, Contextual for the SAME source/view/model/ranks/guardHolds, and SemanticReady at its heap.
Require Stable at before for that SAME semantic context, native Idle, Grows source before.heap and Extends source.nodes.issued before.heap.nodes.issued.
Require the actual incoming Trace I initialDomains before.nativeDomains. The initial domain cache may already be populated.
Require ONE Room bits profile with nodes=source.nodes.next, edges=source.edges.next, domains=initialDomains.next+I.length and mass=0.
No extra comparison-success, worker-completion, future Room, callback, fresh-cache, generated-parent or result-law premise is permitted.

Derive ∃ fuel kept after at the SAME width, with ALL of these outputs:
1. H16.execute fuel (.cluster rows []) before = .done kept after.
2. Every full edge in kept belongs to rows, and kept.length <= rows.length.
3. Good after.checked, SAME Contextual and SemanticReady at after, SAME-context Stable after and native Idle after.
4. Native-machine Extension before.machine after.machine, Extends before.memo.table after.memo.table and FlatMemoThunk.Returned before.memo after.memo.
5. Trace I initialDomains after.nativeDomains for the SAME source/inventory/initial cache.
The original source Grows/history at after follow by composing the entry witnesses with Extension.heap/history. No duplicate public predicate or caller-state record is required.
The next fixed-source current Room follows from the unchanged initial reservation and final Trace.next_le, exactly as H15 does at entry.

The theorem must use the actual H16 runner. An auxiliary observed-call graph is not its conclusion.
No ordered Sublist claim is valid: promotion can reorder original rows. No generated common result may become a later operand.
The outputs do not assert pairwise maximality, physical pruning iff, hash-group ordering, node reconstruction, Mu unfolding or Haskell refinement.
An empty symbol group completes through the literal empty-cluster step; no comparison or parent-node constructor premise is required for that case.
The theorem concerns the exact typed nodeEdges group. It does not replace the separate Haskell Mu-unfolding/body-selection problem.
