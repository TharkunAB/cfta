# Edit and class resource review with exact callback counts

Date: 2026-10-16 21:32 CEST.
Result: No material defect found in the reviewed sources or final integration kernels.
This review changed no production source and ran no build.

## Initial-only construction

`SourceCurrentAllocatedFiniteOrdinaryEditResources.lean:149` uses strong induction on the size of the original input. Each recursive call uses a smaller original child or row list. A leaf invokes the actual SharedLeafResources completion endpoint. The proof derives each later Ready, computed inventory, global validity, and stored certificate from the same earlier strict Reads. It derives later headroom from the actual constructor Work trace. The public node, children, rows, and list endpoints at lines 286, 321, 357, and 393 return the constructed graph, its strict Reads, its existing physical receipt, and the literal worker StableRun at the same output and full state.

Captured forest limits and current input limits remain separate. Output profiles cover both. Ordinary row reconstruction preserves the original symbol and full guard. The constructor trace records actual makeNode and makeEdge requests. The proof bounds requests, including interner hits. It does not infer a request count from a difference between counters.

The public premises contain initial Ready, availability or residency, captured and current profiles, compiler safety, valid global memos, stored certificates, and initial counter headroom. They contain no future graph, completed callback, returned profile, range plan, or desired result law.

`SourceCurrentAllocatedFiniteOrdinaryClassResources.lean:64` constructs fresh class-local target slots at the literal class entry. It retains warm native tables, equality operations, merge memos, and global memos. It derives selected-path closure and compiled edit safety from initial finite-ordinary inputs. It invokes the edit list endpoint, then derives the existing ClassReceipt from those same Reads. Its output inventory can differ from the input inventory. The returned graph, receipt, profiles, worker StableRun, and constructor trace use the same actual result and full state.

## Exact count connection

`SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts.lean:31` indexes NodeCount, ChildrenCount, RowsCount, and ListCount by the actual raw graph, including all original values and physical states. A node leaf counts one shared Leaf call. Empty below-edits and list-root leaves count zero. Selected children and ordered rows add their actual counts. The bound uses original literal Value positions, including Empty and repeated row or identity occurrences. Recursive exposure is represented by the raw count relation; the finite-ordinary bound excludes that case through the input domain.

The final root kernel source is `edit-integration-kernels.lean`. Its three signature and axiom reports are clean in `edit-integration-5.log`. The axiom reports contain only propext, Classical.choice, and Quot.sound. No error, warning, or sorryAx occurs in that log.

- `two_selected_count` at line 29 derives two calls from a supplied exact two-selected-child graph. It assumes no count or callback law.
- `constructed_empty_leaf` at line 72 invokes EditResources.node and proves NodeCount 1 on that same constructed graph.
- `constructed_two_empty_leaves` at line 97 invokes EditResources.children and proves ChildrenCount 2 on that same constructed graph. Both literal Empty positions use the same callback token. The returned Reads, receipt, StableRun, and Work trace retain the graph's exact result and full state.

The raw helper alone is a verification lemma. The latter two kernels construct their executions from initial premises. Neither replaces its constructed graph with a second execution. Failed attempts 1 through 4 remain separate evidence. Only log 5 supports the final clean result.

## Resource and scope limits

EditBudgetNumbers charges a full first-target cost and its native query at every literal input position. Warm slot hits fit this conservative bound. The proof preserves actual sharing, but it does not claim a sharper aggregate bound of one target miss per distinct path. The callback count counts one shared Leaf call per actual node leaf. Native queries inside target construction are covered by the separate target resource budget.

The new endpoints cover finite-ordinary inputs with general guards. Initial physical, semantic, warm-cache, compiler-safety, and profile premises remain explicit. The existing ClassReceipt supplies its scoped language law. This review does not strengthen it to a general merge language equivalence.

Cumulative resource and profile accounting for the full class pass, local reduction, parent, and outer root remains a later composition. Equality-interner capacity, concrete host forcing, other machine limits, and whole-library completion remain separate boundaries.
