# Term storage correspondence

`TermRepresentation` models all five `Data.CFTA.Term` storage constructors.
`pack_unpack` and `unpack_pack` establish the canonical representation of a
finite tree. Direct construction of `Many` requires at least four children.
The `Node` builder establishes this invariant.

`TermOperations` follows the source constructor dispatch for child adjustment,
preorder flattening, and tree folding. Adjustment changes the selected child
and preserves the root, arity, and other children. Negative or out-of-range
indices leave the term unchanged. `flatten_exact` proves exact preorder
including every child in sequence order. `fold_exact` proves agreement with
the reference tree fold for every supplied algebra.

`ChildBuilder` follows `fromAssocs`. It models unwritten sequence slots by
`none`. The input contract requires each child index exactly once, in any
order. `fromAssocs_correct` proves that all zero-, one-, two-, and three-child
fast paths agree with the indexed sequence builder. `writeAll_exact` proves
that the generic builder fills every slot. `fromAssocs_valid` derives canonical
storage and exact child order. Missing or duplicate indices are not validated
by the source API. Callers must meet the stated contract.

Lists represent ordered sequence operations. The proofs do not verify the
`Data.Sequence` implementation, machine index conversion, hashing, or compiler
runtime. They do verify the source's constructor-specific tree operations.
