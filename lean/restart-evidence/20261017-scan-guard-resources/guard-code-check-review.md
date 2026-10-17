# Independent native guard code review

Reviewed at 2026-10-17 13:51 CEST. No material defect was found.
The final source SHA256 is b5d66e47d2392015ebdb6e00c08a10a3e84ed5b2c4df443bb1bf0260340def90.

Fields checks literal Work guards and every captured continuation.
Work_mono, mono, bind, and walk retain these checks structurally.
CompileNode_fields covers every source decision, including Mu, union, reference, and ordinary branches.
Node compilation emits no literal edge guard. A predicate that rejects every guard can satisfy this certificate.
This is a code property. It does not assert that recursive queries return or preserve a heap predicate.

Sentinel_fields requires the literal source top guard.
Children_fields requires only the actual combined constraint readback.
Body_fields verifies an actual yielded body. It is not a body completion theorem.
Its premises are initial operation validity, current cached source fields, top/conjoin predicate facts,
and the captured continuation certificate.
The accepted branch derives the allocated readback from both actual loads and run_correct.
The rejected and mismatch branches check the literal sentinel top.
No desired emitted-code certificate or final guard heap is an input.

Fields does not certify internal allocation by optionalBinder.
It checks the continuation after that instruction.
The full step/trace proof must separately retain the guard carrier through actual primitive writes,
checked-body predicate growth, recursive publication, and finish frames.
This review does not count those later modules as proved.

The first kernel constructs a closed raw-equality parent with productive Mu and explicit union children.
It builds the normalized field and derives current FieldAvailable from actual allocation.
It derives successful loads, stored Ready, and exact raw readback through receipts.
Existing body_complete constructs its own yielded checked body at that same operation state.
The new body_fields theorem then produces its emitted-code certificate.
The predicate accepts only source top or the exact source conjunction.
The kernel does not assume a successful body, future load, or desired combined readback.
It does not assert that this body takes the accepted branch or completes its recursive children.
The second kernel checks node compilation over the same concrete Mu/union operands with the false predicate.

All nine public declarations and both kernel declarations have full imported signatures and axiom reports.
The successful logs have no diagnostics. Only standard Lean axioms occur.
Kernel attempt1 used a proof where a proposition was required. Its source and raw log are retained.
The root strict attempt2 is empty. The raw canonical log reports 1067 successful jobs.
No production or older frozen evidence was changed by this review.
