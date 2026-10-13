# Nested unary endpoints under actual ancestor rows

`EqualityNestedUnaryWork` connects the nested endpoint action to the existing
finite path worker. `product_eq` and `meet_eq` prove exact result and cache
equality between finite constructor work and the action definitions. The
proof retains hash-join order, identity shortcuts, numeric orientation, child
intersections, and parent construction. `meet_safe` derives constructor safety.
`meet_empty_left` preserves the literal empty endpoint without cache effects.

`EqualityNestedUnaryAncestor` records the original unary ancestor occurrences.
`projected_nonempty` proves that canonical parent construction retains each
nonempty original endpoint. `projected_subset` excludes invented occurrences.
`projected_rows` proves that physical projection has exactly the union of the
original endpoint rows. Empty child rows and duplicate ancestor rows do not
change this union. The theorem needs unary ancestors: a dead sibling in a
larger row could remove a nonempty selected endpoint.

`projected_index_shape` specializes this result to the original finite indices
of the nested endpoint schedule. `projected_complete` executes the actual
projection union and derives its returned-cache availability, canonical
readback, and exact indexed row predicate. `leaf_ordinary` and
`endpoint_ordinary` derive the finite path-worker fragment from the concrete
nested endpoint representation. `endpoint_edit` and `unary_rebuild` identify
the selected physical child request with the exact nested intersection.

`EqualityNestedUnaryAncestorCompile.compile_complete` constructs the ancestor
rows in original finite-index order. It then builds the canonical parent and
projects the actual stored children. Its output contains the actual parent
and projection in the actual returned cache. The theorem derives original
index alignment from the source constructor requests. It permits repeated
tags, duplicate endpoint records, and literal empty endpoints.
`target_complete` also runs the current source target merger on that physical
projection. Under the existing at-most-two initial atom premise, the target
has the exact projected generated-row predicate.

The completed endpoint loop remains separate from the root loop.
`edit_original` applies the existing parent worker theorem to the concrete
nested intersection. That result reconstructs all original occurrences in an
explicit later finite cache. A full root-loop theorem still needs an
original-occurrence representation in the actual returned edit cache, then
composition of both forest-entry edits and the root identity stop test.
The new projection theorem does not supply that final edit-cache transport.
It does not cover overlapping endpoint paths or non-unary ancestors with dead
unselected siblings.

Validation: Lean 4.34.1 builds the three modules in 396 jobs. The isolated
axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
