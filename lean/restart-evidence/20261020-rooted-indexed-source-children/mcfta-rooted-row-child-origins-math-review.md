# Rooted row-child origins: independent mathematical review

Reviewed 2026-10-20 16:59 CEST. Result: no material issue found in final official source SHA256 `2186d2dc0c3079a2c669a48649230c314b7b6c56685836377c146b9969471214`.

This review reads the complete Origin and from_source_row proof and their actual source foundations. The official source is byte-identical to the revised draft snapshot inspected in the earlier design audit. The indexed_child helper's established contract is reused; its independent review is not counted again. This review runs no Lean, canonical, or runtime job and adds zero proof pairs. It changes no production source, candidate, or frozen artifact.

## Origin statements

Origin at lines 24–67 preserves the complete selected parentRow, exact childIndex, and complete child value in every branch. The node constructor retains actual buildEdges and makeNode equations, canonical row lookup, the distinct original RowCall source index, and exact equality of that call's complete output row with parentRow. Its child syntax, physical output lookup, ordered prefix and suffix, joint Context, actual completed child build, physical and issued growth, and rooted Reached describe the same call. Complete row equality retains the full symbol, guard, and ordered child fields. No source/canonical index equality or uniqueness is asserted.

The node constructor's smaller field is exactly `sizeOf childSyntax < sizeOf original`. It does not assert a generated-value decrease.

The capture constructor retains the exact input slot and complete value, RowAt of parentRow in that value, the same selected child, and Reached at the actual variable syntax. It is a capture stop. It supplies no earlier compiler binding origin.

The binder constructor retains both actual current probe callbacks, the current request, the exact complete selected Mu in that request's return heap, finish, RowAt of parentRow in the selected stored body, the same selected child, and Reached at the current binder syntax. It is a selected-body stop. The selected body is not identified with the current callback result or expression. No earlier writer is inferred.

Neither the capture nor binder constructor exposes a terminal syntax-size bound against Origin.original. Their Reached receipt is rooted in root. An arbitrary manually supplied Origin of those constructors does not acquire a stronger bound merely because the proof of from_source_row internally carries one. This omission is consistent with the declared stop contract.

## Complete from_source_row proof

The theorem at lines 70–124 consumes joint Context, rooted Reached, an actual SourceRow receipt, and an exact child lookup in its selected parent row. Its auxiliary induction tracks the current source expression, inputs, historical call heaps, and `sizeOf currentExpression ≤ sizeOf expression`. The original expression parameter remains fixed in the final Origin.

For a node, the proof transfers the selected child lookup across the exact RowCall output-row equality. It calls indexed_child on that same RowCall. Reached.node uses the exact original source edge and child membership. Reached.grows then moves that route forward from the actual node entry to the derived child entry, using the actual prefix growth. The strict original child bound from indexed_child composes with the induction's source bound. No forward equation is reversed.

For a union, SourceRow.union already retains the exact original indexed member syntax, actual output, historical member Context, prefix, completed member call, suffix, and nested SourceRow. The proof checks buildMany on the actual source prefix and rewrites its growth field with the exact prefix equation. It derives Grows from the current union entry to the selected member entry. Reached.union extends the original source route to that exact member, and Reached.grows uses this forward growth. The supplied member Context supports the recursive proof at that historical entry. The selected original member's syntax is structurally smaller than the union; that bound composes with the fixed original bound.

This union step follows actual source-row receipts. It does not assume that a leaf of a normalized output is a leaf of an original source member. It therefore does not use the refuted same-leaf-member law.

For capture and binder cases, the proof copies the corresponding exact stop data and the current rooted Reached. It introduces no semantic law, publication writer, native input ancestry, terminal syntax bound, or whole-call suffix that is absent from those constructors.

## Precise consumer boundary

The result supports an actual source child or an explicit capture/binder stop. It does not establish global original-binding ancestry, full finite-observation preservation, or a termination measure. The distinction between generated native encode inputs and original compiler inputs remains external.

Origin.binder's selected record is present at its LOCAL request return heap. Origin does not expose Grows from that heap to the whole source build's return. Reached contains growth from recorded callback starts to its indexed current state, not this later suffix. Thus the proposed next selected-writer resume must consume an explicitly selected whole-return cell or derive the same-stop suffix from actual SourceRow tails before discarding them. This is an applicability boundary, not a soundness defect in the current result. The separate suffix note records the exact next proof obligation.

The owner reports two checked public declarations, Origin and from_source_row, strict attempt 3 with an empty log, and full public readback. This review does not rerun or recount those checks. The selected official source and its ROOT-relative foundations are pinned separately from this report.
