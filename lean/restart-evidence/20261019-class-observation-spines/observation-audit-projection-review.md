# Projection read spine review

Reviewed 2026-10-19 01:39 CEST. No material proof or contract issue was found.
All 201 production lines and the selected validation receipts were read.
No Lean job or production edit was made.

## Exact linkage

`Spine` is indexed by the actual `Project`, the actual final `Read`, the selected position, and the full selected row.
The ordinary constructor retains the canonical output lookup and a raw union-row preimage.
It also retains the selected union operand, its exact earlier and later `ReadAll`, its actual read interval, and its selected row index.
The producer passes this same `operandRead` and row index to the recursive child spine.

The same operand index selects the `ProjectRows` prefix, child call, and suffix.
The selected original row and signed child lookup remain explicit.
The child projection can finish before its union operand read starts.
The intervening calls are the retained projection suffix and union-read prefix.
No equality of those distinct intermediate heaps is assumed.

The recursive constructor retains the actual Head and the remaining projection at the same residual path.
The empty-path constructor retains the actual terminal read.
That read can unfold Mu. It is not replaced by structural `RowAt` or literal stored-body row membership.

## Scope limits

The raw union index is an equal full-row preimage in `allRows`.
It is chosen independently of the selected operand/read position.
The contract does not assert `rawIndex = earlierRows.length + readIndex`.
This is sufficient for full-row provenance. A consumer that needs one exact duplicate occurrence must derive or add the offset equation.

The public theorem accepts an arbitrary actual external read entry heap.
It does not assert growth from the projection return to that reader.
Phase effects inside the actual projection and union schedules come from initial semantic readiness, cost heap, and availability.
The proof uses the success-linked effects for open operands. It adds no global closedness premise.
It derives neither read-entry physical support nor an original-source ancestry theorem.

## Selected evidence

- Production and strict snapshot SHA256: `b58d94bcae9b63cffd8b9193d0d795609efbf8206adfe14c62f0dbb5e1282499`.
- `projection-spine-direct-3`: terminal 0. The raw log has zero bytes.
- `projection-spine-canonical-1`: terminal 0. Target build passed at 1010 jobs. The log retains the pre-existing `InternedFreshOrdinaryClosedCompletion.inputs` unused-variable warning.
- `projection-spine-public-1`: terminal 0. Both public declarations have explicit signature, complete print, and axiom output with all eight required options. The axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.
- All three selected jobs recorded memory maximum and high of 4294967296 bytes, zero swap, and the 4G/5m wrapper.

This review owns zero new proof pairs and zero Lean runs. It reuses two public pairs.
The adjacent pins file records only the reviewed source, selected receipts, and this report.
