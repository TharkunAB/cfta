# Next symbol-group traversal: source-only inventory
1. Reuse the generic ordered-bucket and iterator facts. Add a small literal grouping bridge before a concrete sequential group consumer.
2. Haskell calls `clusterByHash edgeSymbol origEs`, then `concatMap reduceCluster`; it compares each bucket in input order (H-Operations:332–370,789–798).
3. `clusterByHash` keys by the symbol itself. Hash equality alone does not define a group. A lawful Eq/Hashable and HashMap storage/iteration contract is still an external refinement obligation.
4. Haskell inserts new singleton ++ old bucket and reverses each final bucket. Lean `SourceCurrentMergeGrouping.insertWith` inserts old bucket ++ new singleton (L-MergeGrouping:21–32).
5. These are different intermediate tables. Do not identify raw Haskell buckets with `fromRows` buckets before the final reverse.
6. The needed pure bridge is reversal conjugacy for singleton insertion, followed by a finite iterator transport. Its precise equations are in bridge.md; they are proposed laws, not checked theorems.
7. Preserve None versus Some and every repeated row occurrence. `lookup_some`, `lookup_nonempty` and `lookup_key` then give the exact nonempty input filter for each normalized bucket (L-MergeGrouping:60–109).
8. Instantiate the generic key with `edge.entry.key.symbol`. Do not use `MergedSourceGrouping.groupKey` or specialized `merge_grouping`; those split by symbol AND child count (L-MergedSource:40–46; L-MergeGrouping:183–188).
9. `groups_exact`, `Sized.groups_perm` and `Iteration.permutation` already supply exact bucket contents and an outer permutation (L-MergedSource:15–38; L-Sized:240–287; L-MergeGrouping:149–181).
10. `Sized.groups` uses first-occurrence key order. HashMap.elems order is unspecified here. A modeled canonical order alone does not refine the literal Haskell iteration.
11. A future modeled consumer should accept any finite iterator order with these exact complete symbol buckets. Prove completion in that literal order, not equality of final heaps across different orders.
12. For each emitted symbol, exact lookup identifies its bucket with the SAME original parent's full symbol filter. This is exactly H20's input, including within-bucket order.
13. Call H20 once per bucket at the preceding group's actual returned wrapper. Keep source/facts, formulas/solver, admitted inputModel, inputRanked, parent, bits, initialDomains and initialValid fixed (L-H20-v2:242–298).
14. H20 returns Good, Contextual, SemanticReady, native Extension, Stable, NativeIdle, pair-table Extends, Returned and the SAME global initialDomains allocation Trace.
15. Compose growth/history with Extension and compose table/returned retention at the actual middle states (L-Extension:19–35; L-Cache:28–35; L-Returned:14–23).
16. Pass the returned global Trace onward. Keep the one initial Room reservation. Do not reset the history to refl or choose a fresh width/Room for each group (L-Domains:16–21,48–75).
17. Source parent availability/originality/closedness/admission do not change: H20's premises refer to the fixed source, while the current-state packet evolves.
18. Accumulate actual kept lists in the iterator order. Membership and total length follow groupwise; concatenate the per-group all-ambient physical union iff and use the complete input partition.
19. This yields whole-original-row union preservation for the modeled group traversal. It does not identify exact kept rows or cache histories across alternative outer group orders.
20. No all-group traversal control or completion theorem was found in the inspected grouping APIs. Their existing merge `Work` consumer serves another operation and different symbol/arity groups.
21. Smallest next proof slice: the singleton-prepend/reverse bridge and iterator transport, then a concrete finite traversal using H20. Do not clone the grouping framework or add a total-meet/call-success oracle.
22. Actual Haskell HashMap refinement and lazy `concatMap` evaluation/state correspondence remain separate. The iterator contract is a container boundary, not evidence that those are checked.
23. Ordinary `withoutRedundantEdges` first maps child calls and applies this helper only to a closed ordinary node; its current/generated parent provenance remains outside this inventory (H-Operations:740–772).
24. Mu unfolding/body filtering, reconstruction, whole public pass, practical host width, Haskell refinement and convergence remain open. H6 remains the strongest combined trace theorem.
25. At the root task cut, H20 source 393/e1c54fe6 has clean strict2 and unique FULL1 reader PASS; installation and Audit are pending. These are root-reported facts, not executions in this review.
26. I authored H20 checkpoint templates and earlier source audits, not its mathematical body or the existing grouping APIs. This inventory used static reads and comparisons only; no compiler, prepared tool, Git, network or repository writes.
