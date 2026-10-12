# Closed finite-cache occurrence representations

`EqualityLeafProjectionRepresentation.Represents` means that the occurrence
compiler returns an exact complete source record without allocation in the
current finite cache. The edge-list and child-forest forms preserve order.
Actual compilation establishes the representation. Later cache growth
preserves it through the proved source replay operation.

`bind_closed` derives allocation-free component requests from a completed
computation. The constructor decomposition theorems therefore expose actual
closed child, edge, and parent requests. The reconstruction theorems compose
those requests back into the original occurrence representation. No complete
constructor, worker, or pass correspondence equation is a premise.

`forest_length` retains the original child arity. `edge_fields` retains the
complete source symbol, constraint, and ordered child records. The latter
uses availability and exact cache child-payload readback, rather than only
reference-key equality.

This relation supports source-first recursive correspondence. After a worker
returns, finite proof preparation can complete representations of changed
occurrences in a common later cache while retaining the already returned
source record. The full recursive worker and fixed-schedule relation must
still be composed from these local facts.
