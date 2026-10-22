Let I := SourceRecursiveIntersectionSourceInventory.domains source and L := I.length.
Let reserve := Room bits ⟨source.nodes.next, source.edges.next, initialDomains.next + L, 0⟩.
The actual incoming Trace I initialDomains beforeDomains gives beforeDomains.next ≤ initialDomains.next + L.
Room.mono then gives Room bits ⟨source.nodes.next, source.edges.next, beforeDomains.next, 0⟩.
The reserve also implies initialDomains.next + L < 2^(bits+1), which is the global Resources domain condition.
Build global Resources with facts, source_closed, initialValid and the source node/edge components of reserve.
Build Current at before.checked from Good, SemanticReady, source growth, issued history and the incoming allocations.
Split the actual original and reversed pair table lookups, as in H14.
For a ready key, use H10 ready_complete and its literal checked equality to retain the global Current domain field.
For two absent keys, call H13 both_miss_complete with the derived current-call Room, retaining its receipt.
The receipt begins at exactly before.checked and ends at exactly after.checked; no warm native Receipt is asserted on hits.
Derive the canonical request's source EdgeScope from the SAME actual original parent rows. Readiness follows from source residency, growth and empty_domain.
Use SourceRecursiveIntersectionSourceInventory.empty_mem for the exact emptyDomain key.
Use SourceCurrentAllocatedRecursivePrefixControl.edge_body source I request beforeMachine scope member ready.
Use Fields (.edgeBody request .pure) before.checked = ⟨ready, fun _ => trivial⟩, as in the checked direct-range adapter.
Use receipt.trace.steps as the actual Steps argument of SourceCurrentAllocatedRecursivePrefixAdmission.prefixes.
Its Admits application receives the SAME global Resources and Current, certificate and Fields; its result is the exact prefix Receipt.
Project .current.domains to obtain Trace I initialDomains after.checked.native.machine.domains.
Retain H14's other result fields from the corresponding H10 or H13 branch. Extension composes source growth and issued history for the next call.
No observed-wrapper inverse, changed view, fresh domain cache, future Room premise or extra semantic completion oracle is used.
Estimated implementation: 180–250 total source lines including the 56-line header and local scope reconstruction; this is an untested estimate, not scope authorization.
After this writer is checked, finite scan control and membership preservation form a separate proof. The capacity reservation does not depend on a predicted comparison count.
