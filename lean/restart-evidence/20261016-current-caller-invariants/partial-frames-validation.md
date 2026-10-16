# Current caller protected-cell frames

Source: lean/MicroCFTA/SourceCurrentAllocatedPartialFrames.lean.
Frozen SHA256: 4b6c2b9f656c7aede31c4fbbdecb82c57ec5be4ee619abe223d40fe04238240e.
The source has 307 lines. The frozen copy has identical bytes.

Pinned Lean 4.34.1 canonical build passed with 1395 jobs in partial-frames-build-1.log. Only the existing unused inputs dependency warning appears. The fourth direct source check passed without warnings. Earlier raw logs retain resolved elaboration and structural recursion errors. The final proof uses the actual eight mutual recursors. A local tactic writes the same structural motives and constructor cases for each endpoint; no recursive completion callback is assumed.

All 19 public theorem axiom reports and 21 full signatures passed. Four separate integration kernels have four additional axiom reports and four signatures. Total: 23 axiom reports and 25 signature checks. Final public and kernel logs have no errors, warnings, or sorryAx. Their axiom reports use only propext, Classical.choice, and Quot.sound.

Protocol records each result family's bounded cells and exact request.key links. It is independent of the changing equality cache, physical readiness, request residency, and language. Existing PartialState.Valid derives Protocol by dropping its additional same-cache Stored fact. Empty caller tables derive Protocol directly. No malformed-table claim is made without these initial cell bounds and links.

Frame retains Protocol after the actual operation, both published-key tables, every earlier evaluating request, and every earlier returned request/result pair. Actual begin calls use literal lookupOrInsert then demand. Fresh publication cannot overwrite an allocated protected cell. Demand preserves all earlier running and returned cells. The owner helpers derive the exact retained evaluating request and equality of owner and candidate physical keys.

Each completed graph call's selected handle was not evaluating at its input. Otherwise actual lookup preserves that running cell, demand returns busy, and the graph's not_busy theorem gives a contradiction. Finishing that selected handle therefore preserves every protected input running cell. Finish also preserves every earlier returned cell unconditionally. This argument uses actual begin observations and the actual body graph, not a supplied body frame or semantic result law.

The actual mutual induction covers NodeCall, NodeBody, EdgeCall, EdgeBody, Rows, Descendants, Children, and Walk. Heap and equality-operation work uses advance and leaves both caller tables exact. Rows compose actual edge, returned-edge descendant, and tail frames in source order. Descendants and Walk thread actual prefix and descent states before their recursive graph. Binder reconstruction and the checked parent edge body retain both caller tables without replacing their execution graph.

The node_owner_completed and edge_owner_completed kernels derive the original newly started evaluating cell, retain it through the actual body graph, and prove finish installs the exact original request with its returned result. The two_calls_cross_family kernel constructs two successive indexed recursive calls and retains protected evaluating and returned cells in both families, plus both published-key tables. The node_call_protects_edge_ancestor kernel retains an active edge ancestor through a completed nested node call, derives its literal later busy observation, and excludes a successful recursive edge call on that still-running handle.

This component proves structural table frames for actual completed graphs. It does not derive completion of every caller, physical or semantic invariants, language laws for new results, GHC forcing, concurrent publication, exception behavior, or machine identity adequacy. Every older proof source remains unchanged.
