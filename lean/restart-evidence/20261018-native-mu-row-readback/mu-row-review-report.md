# Independent review of native Mu row readback

Review scope: `SourceCurrentNativeOrdinaryMuFinish`, `SourceCurrentNativeConstructReaderReadback`, and `SourceCurrentNativeQueryMuRowOrigins`. This review reads the proof bodies and their dependencies. It does not run Lean or add a public declaration. Final receipt selection is recorded in the review manifest.

No material proof issue was found. The new result recovers an actual raw ordinary substitution origin from a physical ordinary row returned through a Mu compiler branch. It does not prove a decreasing original-source occurrence, outer termination, or public Haskell correspondence.

## Exact winning record and the corrected premise

`OrdinaryMuFinish.selected` requires `InternedFreshOrdinaryDepthHeap.Correct entry storedBody depth ordinary`. The premise is necessary. Cleanup inspects `storedBody.free`, while `usesLocal` inspects the ordinary probe's deep names. Arbitrary unrelated bodies and probes do not establish the same decision.

The proof first excludes Empty and retained Mu because neither has a physical `nodeEdges` row. Cleanup therefore returns the literal `storedBody`, and its own interned name is absent from that body. Correctness at `smart=false` identifies body depth with the depth probe. Correctness at `smart=true` then excludes the additional depth required by `usesLocal=true`. The exact selected body-row index is retained.

The comment's "original row occurrence" means an occurrence in the selected winning `storedBody`. It does not mean an occurrence in the initial public source. The correction to the proof contract is not a Haskell defect.

## Actual construct and later causal reader

`ConstructReaderReadback.construct_row` takes an actual successful construct, its initial SemanticHeap and Available body, a later reader publication history from empty, and forward `Grows after reader`. It does not require publication history at the earlier construct entry.

The proof compiles the actual construct to the repaired binder executor. `NativeBinderExecution.decompose` supplies its exact Depth callback, ordinary callback, raw ordinary build, normalized filter, and complete constructor request. It supplies semantic callback contexts and raw-to-return heap growth and issued-name extension.

`NativeRequestProbes.request_probes` identifies the actual selected winner at the requested key with the full current Depth and ordinary probe values. It uses coherent resident readback, rather than inferring full probe equality from keys alone. `finalContext.depth` derives Correct for that exact selected payload. This handles an older warm winner. It does not identify that winner with a prospective callback candidate.

The proof transports the complete winning Mu record through `growth.nodeRecords` to the reader. Only then does `NormalizedComparisonExecution.history_unused` use the reader's causal publication history. The equality is between the actual finished winner and the current ordinary probe with bare self erased. No history is inferred backwards. `Rebind.rebind_build` retains the exact raw stored substitution call and its actual heaps.

`CallbackRowOrigins.erase_self` and `.filter` preserve constructor row origins for every view. A bare self reference has no constructor row. The proof therefore obtains `Origin view [raw] row` from the actual selected physical row, including all full row fields and ordered physical children. It does not equate raw and filtered values physically.

## Actual native writer and initial request

`QueryMuRowOrigins.returned_mu` starts with the native causal writer history and the exact retained returned request cell. `NativeMuWriterOrigins.returned` supplies the actual captured evaluating owner, compiled writer Trace, entered domain, body request Trace, body value, optional-binder call, and retention to the reader.

The captured owner's Good supplies the initial semantic heap. Domain entry changes no heap. Forward `PublicationTrace.trace` along the body Trace therefore derives SemanticHeap at the actual optional-binder entry. The schedule's exact final-state equation and captured writer growth derive `Grows` from the actual optional-binder heap to the reader.

`OptionalOrigin` keeps two distinct cases. If the pair reference is absent, the actual result and heap are unchanged. If the pair is present, the actual construct equation produces `RowReadback`. Pair presence does not imply that the selected stored binder has `usesLocal=true`. An initially used recursive pair can lead to a stored-local unused cleanup.

`returned` retains the actual terminal request, closed operands, exact returned cell, and actual first-writer receipt. Its self, ordinary, union, and Mu cases preserve their existing contracts. It does not select an arbitrary equal-valued resident row.

`request` requires initial Good, native writer history, causal source publication history, closed input operands, an actual completed query Trace, and a selected physical result row. It extends both histories forward and classifies that row. The premise is an observed successful Trace; this theorem does not construct an unbounded native computation or assert that every query completes.

Native writer history alone does not provide source publication history. `NativeEdgeWriterGrowth.History.initial` admits an arbitrary initial machine. The new request theorem keeps the two histories separate. Existing `MuPublication.closed_history` supplies the initial source publication history for the actual repaired build from empty. `PublicationTrace.source_trace` composes that initial construction with the actual native Trace.

## Source-lineage producer that remains missing

The next step can reuse these exact APIs:

- `StoredSubstitutionOrigins.node` gives the original row index, exact full symbol and guard, child arity, ordered child Calls, and literal prefix/child/suffix heaps for an actual open ordinary reconstruction. Its `node_complete` endpoint constructs the execution from SemanticHeap, Covered, Available, and Replacements.
- `StoredSubstitutionOrigins.union` gives ordered indexed member Calls and a bidirectional epsilon-origin receipt. Its `union_complete` endpoint constructs the execution from the same initial support. Closed inputs have the literal identity shortcut.
- `StoredPlanEquivalence.build_execute` converts an encoded callback under local bindings to an exact actual stored execution under `resolve`. It preserves nearest-local masking, captured aliases, the full outcome, and arbitrary nested Mu. It is a usable strict-body call producer for a nested binder case.

The missing general composition is a recursive source-row relation through a stored Mu root and its actual nested normalized callbacks or earlier retained winner. Existing ordinary and union child Calls permit nested Mu, but do not recursively prove that relation. A strict-body induction must retain reference replacements and opaque captured Mu origins, and must use actual callback freshness and causal winner readback. It cannot assume the desired callback output relation.

`MergedFreshOrdinaryGraph.Origin` is epsilon reachability at a supplied view. A Mu successor follows the actual repaired stored unfolding at that view, and the graph discards the unfolding's returned heap. An Origin receipt is therefore not a proper original-source occurrence, an inherited-path decrease, or an ancestor-owner key exclusion. General used-local source correspondence and general outer progress remain open.

## Validation boundary

The manifest selects only final immutable production snapshots, their genuinely empty strict logs, terminal canonical receipts, and full imported public signature/proof/axiom probes. Existing checks are reused. This review runs no Lean build and counts no new public or constructed pair. Mutable root fixtures, shared selections, task peak logs, and full Audit outputs are excluded from the review manifest.
