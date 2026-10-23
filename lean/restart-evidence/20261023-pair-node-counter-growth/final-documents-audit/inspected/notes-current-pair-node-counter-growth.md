# Pair comparison node-counter growth

Updated: 2026-10-23 17:56 CEST. Proof checkpoint: `39da661878d9e83362947f2621e6d1110dab6897`.
Start: `de085728ebe1e905ae339eaba8d26348126e5ada`.

The public outcomeState returns the complete actual pair State from every outcome.
The step_mono and execute_mono theorems bound the input constructor node counter
by the counter in that actual outcome state. They allow arbitrary states, controls,
widths and finite fuel. They include yielded, done, failed, constraintError and blocked.
The accessor has no equality instance or axioms. Only the two existing equality
instances occur on the theorem heads. No validity, readiness, success, callback bound
or final-counter premise is required.

Memo publication, all four demand observations, ordering and return retain checked.
The native phase uses H36 at the same body and checked state. It forwards the exact
returned checked state for each outcome. The fuel induction generalizes control
and the complete pair state. Its only IH call is ih next after at predecessor fuel.
The public control has no resume operation. This module adds no resume theorem.

The unchanged 96-line source passed its first strict check with an empty log.
The sole FULL job passed and retained 1048134 raw bytes.
Root and an independent reviewer read all checked public TYPEs: 2, 35 and 35 lines.
All twelve retained slices reconstruct the complete raw output.
BODY retention was checked programmatically. No whole manual BODY review is claimed.
Raw TYPE byte identity is false for outcomeState and true for both theorems.
All three lexical identities are true. The accessor axiom set is empty.
Both theorem axiom sets contain only Classical.choice, Quot.sound and propext.
The aggregate Audit passed with 3656 build jobs and 75572 dependency checks.
It replayed the older unused-input warning. The new source has no warning.

The actual history has three successful proof jobs, one unchanged mathematical
variant, zero source patches and zero rejected public TYPEs. The collector cut
retains 1176 artifacts and eighteen successful metadata attempts. Final support
retains the collector receipt and later receipts outside that historical cut.
The declaration Observation-type parentheses correction and the added actual FULL
selection link are metadata corrections. Their original bytes remain retained.
No Haskell repair was needed. No older proof body, draft, counterexample or optimized core changes.

Lifting this counter bound through Scan/H23, fixed-source initial counter order
and transport of the original global domain history remain separate targets.
The earlier H23 conditional completion and language-preservation results remain proved.
Upper bounds, full-pipeline Room/WordRanges and complete resources, generated execution,
Mu/full pass, practical width, Haskell and solver correspondence, and convergence remain open.
H6 constructed_node_calls remains strongest combined. The goal is ACTIVE and incomplete.
The next mathematical target is the actual cluster-scan counter bound.
This note precedes the H37 seal and push. It claims neither result.

## Selected sources and complete public types

lean/MicroCFTA/SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.lean: 96 lines, SHA 6cfaf5e340d26b8c838f51d93fb3ae0e03b098510ca41b5021ada4e96b72c2e8.

MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.outcomeState: 2 TYPE lines, 140 bytes, SHA b67f5ae14be2d62553765cc37cc482ed6d2b933ed4d2eb4de7e64f50e592da33.
Printed TYPE SHA a0c7e9ecb1497cac2ce331760ed204ae93f528b763d0405104a9ac00556474a7. Raw byte identity: False. Lexical identity: True.
Actual axioms: none.
MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.step_mono: 35 TYPE lines, 2532 bytes, SHA 4fe90636f8357a287f121de75f615ada7db1bd10bba671aa527532f4180c33bb.
Printed TYPE SHA 4fe90636f8357a287f121de75f615ada7db1bd10bba671aa527532f4180c33bb. Raw byte identity: True. Lexical identity: True.
Actual axioms: Classical.choice, Quot.sound, propext.
MicroCFTA.SourceCurrentSameSymbolEdgeControlNodeCounterGrowth.execute_mono: 35 TYPE lines, 2553 bytes, SHA 19bf8eee199dd22f7d02a9e91996111185fc44b0fee0a1772bf37590452366bd.
Printed TYPE SHA 19bf8eee199dd22f7d02a9e91996111185fc44b0fee0a1772bf37590452366bd. Raw byte identity: True. Lexical identity: True.
Actual axioms: Classical.choice, Quot.sound, propext.
