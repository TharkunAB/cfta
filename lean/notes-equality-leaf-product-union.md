# Physical leaf product and projection union

`EqualityLeafProjectionNullary` constructs a finite list of symbol and full
constraint declarations through the actual separate edge and node caches.
Its exact key theorem preserves duplicate requests and canonical readback.
The declaration theorem recovers the original row set from the stored edge
fields. No constructor decoding or row-set preservation contract is assumed.

`EqualityLeafProjectionProduct` reads the stored declarations of both leaf
nodes. Its product uses `SymbolicHashJoin.hashJoin`, including the source's
reversed right bucket order. It combines both stored equality fields and
canonical residual guards. Admitted rows have empty child lists, so every
candidate has matching arity and no recursive child intersection. Admission
closure ensures that the source `mkEdge` accepts each generated constraint.
The physical key theorem derives the abstract per-symbol row product.

`intersect_read` derives the complete leaf intersection rule. Its identity
branch compares whole physical node references. The earlier `identity_iff`
theorem turns that comparison into equality of all symbol columns together.
The product branch applies even when only one symbol column is unchanged.
`combine_row_comm` shows that source operand identity ordering does not change
the generated admitted constraint. The result assumes that both completed
leaf builds reside in the common coherent cache used for intersection.

`EqualityLeafProjectionUnion.union_edges` executes the actual `makeUnion`.
It proves exact complete edge membership after empty operand removal, node
identity deduplication, and the ordinary-node union branch. The proof derives
success of ordinary edge concatenation. Resident record uniqueness shows
that identity deduplication cannot remove a distinct complete node record.
All input roots must be ordinary or empty, and all outgoing rows must lack
an empty child. These conditions preserve the finite ordinary fragment.

`nullary_shape` derives those root and edge conditions for the actual nullary
constructor. `built_union_read` therefore has no supplied ordinary-root or
live-edge assumption. It decodes the union of two generated physical leaves
to the exact union of their admitted row predicates. Cache growth premises
place both earlier values in the common current cache.

These results remove the physical leaf product and union readback gaps.
They do not yet assemble the stateful edit and require workers into the pure
constructor and projection interfaces used by the fixed-point bound. That
composition must account for a common completed cache and replay of all
requests. The current physical leaf carrier has canonical initial guards;
the separate raw-guard normalization phase must cover other initial rows.
