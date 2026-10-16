# Current checked caller result-state validation

Source: lean/MicroCFTA/SourceCurrentAllocatedPartialState.lean.
Frozen SHA256: 631ba3b6bde5f91c45b3b82fe9332f1c1a43f62a46723b56dda64f4f547b09da.
The source has 250 lines. The frozen copy has identical bytes.

The pinned Lean 4.34.1 canonical build passed on the first attempt with 1118 jobs. The raw log is partial-state-build-1.log. It has only the existing unused inputs warning in InternedFreshOrdinaryClosedCompletion. Final direct compilation passed without warnings. Earlier direct logs preserve the resolved keyMap argument-count error.

Public direct probes passed on the first attempt. All 22 public theorem axiom reports and all 38 public signatures passed. Four independent protocol kernels have separate reports and full signatures. Total: 26 axiom reports and 42 signature checks. Four reports have no axioms. The others use only propext, Classical.choice, or Quot.sound. The final public and kernel logs have no errors, warnings, or sorryAx. The first kernel attempt records evidence-only State namespace ambiguity; the second passed. No proof source changed for that evidence correction.

State carries the complete checked machine and equality operations, warm merge memo, current fourth memo, and separate node and reduced-edge result tables. initial clears only those two result tables. advance retains both result tables. Globals remain external read indices, and computed inventories remain proof sidecars.

Node and edge keys use the allocated inherited identity and literal node reference or edge identity. beginNode and beginEdge call actual FlatMemoThunk.lookupOrInsert followed by demand. They change only the selected result table. Ready and busy hits return the identical entire state. A suspended hit evaluates its original stored request. Finish preserves that request, completes only an evaluating cell, and cannot replace a returned winner.

Valid is structural. It links every published key to its original inherited value stored in the current equality cache and its exact request key. It includes no semantic output law, physical input residency, or inherited Ready premise. Current checked Good and later cell-language invariants remain separate. Valid is derived for empty tables and retained by actual begin, finish, and equality table growth. No separate request-preparation interner is introduced.

The nested_families kernel starts an outer node request and then a reduced-edge request. Each family uses its own first handle. The original outer request remains busy, and checked, merge, and fourth components remain unchanged. The complete_both kernel completes the edge and then the original node, and checks exact whole-state ready hits for both. The allocation_retains_ready kernel transports all key links through an actual checked physical effect and reuses an existing returned node cell. The absent_observation kernel checks that a dangling handle remains absent and is never a successful result.

This file establishes the pure result-state protocol. It does not execute caller bodies, discharge recursive child laws, derive body completion, or prove general outer termination. A finish result needs its actual body proof before a semantic cell invariant can be installed. Logical publication does not establish GHC forcing, black-hole behavior, concurrent first-winner adequacy, exception behavior, or machine identity representation. These boundaries are retained in current-caller-graph-design.md.
