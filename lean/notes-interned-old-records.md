# Old records across arbitrary nested construction

`InternedNestedDenseIdentities` derives a property of the sequential source
allocator. Every identity below a cache's next counter has its canonical
table entry. The proof covers both independent caches. `build_dense`,
`buildMany_dense`, and `buildEdges_dense` preserve this property at both
successful and pending outcomes. `closed_dense` starts from empty tables.
This property does not apply to arbitrary concurrent reserve/install
interleavings in the more general `Cache` model.

`InternedNestedOldRecords.build_old_record` proves exact earlier readback.
Suppose a record is resident after an arbitrary nested source call, and
its node identity is below the counter at the start of that call. The
same complete payload was already stored at the start. Density supplies
the earlier canonical entry. If its payload was missing, pending coverage
and reservation provenance identify a Mu slot. The full pending-slot
preservation theorem prevents that payload from becoming resident later.

`build_old_available` gives the corresponding full earlier availability
result for records with an old node-identity footprint. It includes
ordinary nodes, unions, raw Mu records, and primitive references.
`completed_prefix_old_record` obtains all cache, density, and coverage
premises from any actual completed empty-cache execution. It then applies
exact readback to a later arbitrary source call.

These results support the remaining normalized-replay proof. They do not
identify which earlier source call produced a reused record. The general
completion proof still needs that correspondence when a nested call uses
some enclosing variables and normalizes away other changed variables.
