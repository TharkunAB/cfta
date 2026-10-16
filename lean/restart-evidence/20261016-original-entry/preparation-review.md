# Original entry and history wrapper review

Timestamp: 2026-10-16 06:42 CEST. Read-only review after the reported GREEN1280 root build. No review builds were run.

Reviewed:

- `SourceCurrentAllocatedNativeOriginalHistory.lean`
- `SourceCurrentAllocatedNativePreparedHistory.lean`
- `SourceCurrentAllocatedNativeConstructedHistory.lean`
- Their allocation history, inventory, operation-state initialization, and cold query dependencies.

No material proof or interface defect was found.

`OriginalHistory` derives normalization from the exact `History.construct` events. `History.cached` reads their explicit `Cached` proofs. `cached_inventory` transfers them through literal guard coverage. It does not derive normalization from successful interning alone. `History.fields` combines these normalized resident annotations with actual constructor origins and successful read-only loads at the same final equality cache. Its `built` equation is an explicit completed cold original construction.

`constructed` derives initial physical `Good`, `SemanticReady`, availability, closedness, and `Original` from that actual build and covered causal history. It starts the native thunk tables and domain cache empty. `SourceEqualityConstraintMemoAllocation.initial final` retains the supplied equality interner `final` and creates empty completed combination and descent tables. This is an initialization of the modeled query state. It is not preservation of an arbitrary earlier operation-table state, and it is not a claim that Haskell resets its global tables. PreparedHistory's header states this distinction.

`ConstructedHistory.query_complete` retains explicit initial interner validity, covered allocation history, actual cold build, source-heap availability and closedness of every query operand, and reached `WordRanges`. It derives `Original` for those operands using the built heap's coherence. It then derives the common finite input model and contextual/scoped cold state through `ColdHistoryExact.cold_complete`. It does not assume final semantic readiness, output correctness, a completed query, or future cache validity.

`PreparedHistory.query_complete` retains the explicit normalization premise at lines 28-29. It calls actual `prepare_complete`, obtains its causal history, and identifies its final cache with the literal `(prepare guards initialCache).2` using `prepared.done`. The range premise and final receipt use that same literal returned cache. No synthetic per-field cache snapshots or assumed successful final loads are used.

The preparation order is the literal inventory order: each row guard precedes child guards and later rows (`ConstraintOrigins.edgeGuards`), and serial preparation preserves repetitions. The wrappers do not prove that this eager inventory schedule equals GHC's lazy field forcing order. Current Haskell uses a global equality interner (`Equality/Constraint.hs:280-286`); `EqConstraints` interns without sorting (`273-276`), while `normalize` sorts normalized classes (`367-374`). `mkEdge` may short circuit to `emptyEdge` (`Interned/Type.hs:566-568`), whose unconstrained field can demand the canonical empty equality key (`537`, `544`; `Constraint.hs:205`). The current wrappers prove resident fields for the actual modeled cold build; they do not claim an exact combined GHC allocation schedule for all discarded or synthetic intermediate fields.

Remaining boundaries are explicit: normalized literal inputs or a causal history carrying those checks, completed original build, closed source-available query operands, reached machine ranges, model cold native/domain/operation tables, and runtime demand/publication/container correspondence. No hidden normalization, final-result, or future completion premise was found.
