# Pure checked class edit plan validation

Source: `lean/MicroCFTA/SourceCurrentAllocatedClassEditPlan.lean`.
Frozen SHA256: `d5c412a76713a1a54bbfd635be0d0091ed409f3a1bc850a8986adae156fbe3ff`.
Source length: 91 lines. The frozen copy has identical bytes.

Direct pinned Lean 4.34.1 compilation passed with status 0 and no warnings in `class-plan-direct-2.log`. The first direct log records a signed-lookup simplification error. An explicit application of the existing select_natural equation resolved it. Root then built this same source canonically together with checked edit ranges. `ranges-plan-build-1.log` records terminal status 0, Plan job 1287 of 1288, and only the old unused `inputs` warning.

Direct public probes passed on the first attempt. They checked all nine public theorem axiom reports and ten public signatures, including compiled. Two integration kernels each have a separate axiom report and full signature. The final log has eleven axiom reports and twelve signature checks. All reported axioms belong to the standard set `propext`, `Classical.choice`, and `Quot.sound`. The log has no error, warning, or `sorryAx`.

The compiler facts derive Valid, Populated, Allowed, signed path disjointness, nonroot paths, exclusion of a list-root leaf, selected ChildrenSafe, and the exact natural callback-token condition. They use existing pure compiler and class coherence theorems. No compiler-correctness callback, heap readiness, native execution, whole-forest closure, or future result is supplied.

The `compiled_tokens` kernel connects literal compiler leaves to exactly the original natural token and its signed path. The `selected_plan` kernel derives the child-map form and every lower traversal precondition from coherent nontrivial records and only the selected ForestClosed domains.

This module does not prove checked class execution or class language. Those use the separate new graph, completion, physical effects, and language modules. The source runtime demand, field identity, and pending memo publication remain separate boundaries.
