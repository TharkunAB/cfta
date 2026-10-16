# Independent checked worker capstone review

Reviewed at 2026-10-16 11:57 CEST. The final reviewed `SourceCurrentAllocatedMergeWorkerActual.lean` has 94 lines and SHA256 `221a3300686479039f9269ed320f2d0cbf015720ddaa59e1cd7ae760bf7ff9f0`.

No material defect was found in verified, caller, or finite. Verified first converts the supplied literal done observation into the same current allocated Call. It then derives the checked receipt and ProbeHeap from that Call. It does not substitute an old unallocated worker outcome or assume final validity.

Caller advances the same full checked state with the literal returned heap and equality operations. It installs the returned merge memo. It retains the fourth memo and both caller result families. Actual physical effects transport phase Sound, fourth Correct, and the warm cached inputs. The new context retains Ready, inventory At, merge Stored and CacheCovers, final global Valid, and derived probes. Native memo tables and the domain cache remain exact under advancePhysical. Generated-result admission into a later native request is not claimed by preserved At alone.

The final global bundle is existential constructed logical read evidence. The worker has no concrete global-query-table field and does not execute those host table operations. The header states this distinction. The retained actual graph and constructor heap support the read construction, but do not settle GHC demand order, selection CAF effects, pending publication, or concurrency.

Finite requires initial Context and input Available only. It constructs an actual allocated Call with the independently proved physical completion theorem. Completion derives stable work and selection bounds from that finite Call. The endpoint applies caller to the literal execution at those bounds, so the same output, equality state, heap, and saved memo receive the postcondition. There is no supplied completed graph, own-body success callback, result law, or final-state invariant. Warm Stored, CacheCovers, fourth correctness, global validity, and ProbeHeap remain legitimate explicit entry assumptions inside Context.

Direct pinned Lean validation exited 0 without warnings. `worker-actual-review.lean` probes all three public theorem axioms and signatures. Its integration kernel derives stable execution, the full caller Post, final ProbeHeap, exact returned equality operations, unchanged native node and edge tables and domain cache, unchanged outer node and edge result tables, output residency, conditional output closedness, and independent Covers from initial Context and Available. The raw log is `worker-actual-review-1.log`.

No source file was changed for this review. No canonical build was run by the reviewer for this capstone. No Haskell issue was established.
