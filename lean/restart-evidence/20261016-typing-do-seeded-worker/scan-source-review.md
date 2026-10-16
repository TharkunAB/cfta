# Literal ScanWorker source review

Reviewed 2026-10-16 13:29 CEST. Root source `SourceCurrentAllocatedScanWorker.lean` is 97 lines, SHA256 `fc1a933520838db4467dc2c7c037638c8f2f3ee98ddfd50944e54520f3c31aa1`.

No material branch or state/memo threading defect was found in the completed serial worker. This review does not prove GHC demand equivalence.

`Equality/Operations.hs:206–213` checks the inherited contradiction before class scanning. ScanWorker starts after that precheck. Its input class order must separately come from `unsafeSubsumptionOrderedEclasses`; each path order must come from the actual Set accessor. The worker does not derive those representations.

The source partition at line 213 is lazy. `any emptyBelowEnd refused` at line 210 demands primary tests only far enough to find successive refused classes. Each reached refused class runs secondary (lines 219–222). A false primary selects a class and skips its secondary/query/decision. A true primary and true secondary skip it. Only a false secondary reaches the projected intersection and current conjunction memo. The worker has these branches.

A true conjunction answer stops before the suffix. Previously selected heads remain as a reached prefix through `Outcome.select`. This is not the full selected partition; source rejection does not demand it. Only a successful outcome of `none` means every class was scanned and the selected list is complete. Repeated list occurrences retain their order. Normalization of each source Set is a separate input correspondence.

Source `intersectList` at lines 228–230 uses its first node as seed and folds the remaining list from the right. The worker calls checked SeededWorker, without mergeAlternatives, on the original child forest and ordered mapped paths. The SeededWorker proof supplies this exact rotation and returned checked state. This review does not replace it with intersection commutativity.

Each phase retains its literal checked return. Gates and queries keep the fourth memo. A completed conjunction miss passes its inserted memo to the suffix. A decision failure keeps the initial fourth memo and reached physical state through CheckedConjunctionWorker. Failure enters no continuation. Selected heads wrap a failed suffix diagnostic while retaining that suffix's checked state and memo. No branch resets native tables, domain cells, equality operations, or the fourth memo.

Five stage bounds are observation parameters, separate from the algorithmic conjunction budget. A failed bounded observation is not a semantic rejection or source exception. The executable worker contains no global bundle; later Reads must hold at these same endpoints. Reconstructed receipts alone do not prove host global-event execution order.

`requireAll`, the tail-first selected-class fold, and Empty propagation follow a successful scan at source lines 211 and 226. ScanWorker does not implement them. Host lazy partition, list/Set order, machine identities, containers, publication, and forcing remain adapters. General outer constrained termination and repeated-pass convergence do not follow from this worker.
