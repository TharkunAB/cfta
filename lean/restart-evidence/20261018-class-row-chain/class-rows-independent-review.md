# Independent class-fold row review

Read-only review on 2026-10-18. No source edit or Lean build was performed for this review.
The final reviewed module is `SourceCurrentClassFoldRowOrigins`.
Its SHA-256 is `d57ecf4371ed53c17ca0f64feb30994764612cac51483eb36a207a0f5fa4faab`.
No substantive mathematical issue remains in the reviewed scope.

## Exact reconstruction data

`Rebuild` retains the complete `RowsReads` for its exact `EditRows` argument.
Its initial and final memo bundles are explicit parameters.
The recorded prefix starts from that same initial bundle and the same input state.
The source row and rebuilt row have the same raw reconstruction index.
The selected survivor comes from the canonical node's filtered raw output list.
This permits canonical row permutation and duplicate removal without assuming that every original row survives.

The receipt contains the actual ordered `EditChildren` and `ChildrenReads`, its captured start and middle states, and the exact `makeEdge` pair.
It retains the full symbol, full constraint field, and complete ordered output children.
Each output-child index has an actual prefix, dispatch or identity case, and suffix `Slice`.
The start and middle native histories are derived through the actual prefix reads and child reads.
The growth facts point from both captured states and the row-constructor heap to the ordinary node's final reader.
They are not supplied future preservation callbacks.

The initially inspected snapshot `e605e8eec6bfc7ed7077a0573e6f49c7d11dbed6015f09fcfed722b49494af35`
had a phantom `_actual` parameter and existential outer memo bundles.
This was a contract-strength observation, not an unsound proof.
The final source retains full actual `RowsReads` and explicit initial/final bundles.
The old strict-9 snapshot remains preserved.

## Source events and exact indices

`NodeFlow` refers to the exact node edit proposition.
Its ordinary branch carries the complete reconstruction receipt.
Its recursive branch carries the later below-edit flow for that same literal Head branch.
Its leaf branch starts at the returned query row.

The source alternative is either a literal input row or an event in that exact edit.
A leaf event derives the actual force and query receipts and invokes the existing query row-origin producer.
A recursive exposure event derives `RecursiveHeadChainRows.Rows` internally from the actual Head and initial Ready, Available, and selected closedness.
It does not take a desired Head-row law from the caller.
The existing query row-origin residual remains visible inside the event.

`ChildFlow` follows the same local forest index through each selected or unselected prefix.
The offset is used in the literal lookup.
`ListFlow` retains that index through the list execution.
`ClassFlow` uses the literal compiled edit with its actual captured forest and base heap.
These types do not permit substitution of an unrelated source edge merely because its guard is equal.
The source row is connected by its actual raw index and reconstruction receipt.

## Right-fold composition

The class fold runs the tail before the head.
The proof first verifies the actual tail and obtains its available intermediate forest, current memo, global bundle, admitted inventory, and native History.
The head flow then starts from that exact intermediate forest and checked state.
If the head source is an existing intermediate row, the induction hypothesis uses that same forest index and row membership.
`FoldFlow.tail` links the exact intermediate row to the later head row.
If the head introduces a new native or Head event, `FoldFlow.head` starts from that actual local event.
It does not falsely claim that every final row descends from an initial literal row.

All six `fields` consequences retain the full symbol and full guard.
They do not replace a full constraint with its effective-own projection.
The pass theorem handles final Empty propagation soundly: a selected value with a positive ordinary row cannot be an erased Empty value.
That positive-row condition forces the propagation result to equal the underlying completed fold forest.

## Explicit assumptions and boundaries

The public verifiers consume actual completed Reads graphs and initial support facts.
Class and fold verification require coherent active records, per-selected-path `ForestClosed`, initial physical Ready/admission/availability, Merge.Stored, CacheCovers, valid global memos, and initial native History.
They do not require finite Cap or whole-forest closure.
These are completed-execution provenance results, not new initial completion or fuel producers.

A reconstruction receipt is not a full global event trace or a proof-term suffix-equality decomposition of every enclosing graph.
Its per-node captured histories and growth are explicit.
It does not itself export every individual child's History endpoints or extend every captured state directly to the final reader of an arbitrary later fold; the actual enclosing Reads and effects supply that further transport.

Full fields do not imply unchanged children or unchanged row identity across class phases.
Canonical row order can change.
No all-row survival, general active-owner exclusion, outer termination, or fresh-call bound is proved.
Recursive Head chains reach literal terminal ordinary rows but do not identify all reconstructed rows with earlier nested source bodies.
The retained-used callback and compileMu-to-original-operands boundaries remain open.

## Existing check receipts inspected

The final immutable direct check is `class-rows-direct-10`.
Its log is zero bytes, its receipt exits 0, and its snapshot equals the final source.
The canonical check `class-rows-canonical-2` exits 0 with 1434 jobs.
It replays one unchanged warning in `InternedFreshOrdinaryClosedCompletion.lean:24:5`.
Both effective limit receipts record 4294967296-byte memory.max and memory.high, and zero swap.
Public printing and constructed fixture validation remain owned by root; this review does not duplicate those builds or count them as independent checks.
