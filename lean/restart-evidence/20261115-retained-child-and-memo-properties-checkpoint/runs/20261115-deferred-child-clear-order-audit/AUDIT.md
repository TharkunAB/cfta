[2026-11-15 06:17 CET]

The focused same-output-branch scenario is excluded by the configured worker's
call order. A captured parent cannot finalize and restart selection while one of
its staged children still waits on that branch. This is a source-grounded control
conclusion. It is not a new checked whole-history theorem. No accepted-source
counterexample or Haskell defect is claimed.

The reason is not IncomingAvoid. That predicate reads only current stored slots.
It says nothing about an arbitrary external captured bucket. Canonical waiting
counts have the same scope. A proof must use the actual visitor and callback-frame
origin as well as the stored-state invariant.

Actual order

1. `SharedChildVisitors.visitSelected` captures the parent bucket, performs the
   own preparation, and passes the literal staged children to `visitChildren`.
   Its completed-row consumer is reached through the child's-list done function.
2. `visitChildren` invokes done only at the empty list. A successful child passes
   its returned cache to the remaining children. A stopped child invokes the
   stopping function instead. The actual eager visitor is not an arbitrary
   caller-supplied visitor.
3. `SharedEagerChildren.eagerChild` recursively constructs an ordinary child with
   `visitSelected` and `consumeSelected done`. The completed row is passed to its
   parent tuple tail. This operation does not restart outer selection.
4. The actual `IdentityActualCallbackFrame.selected` retains the ancestor and its
   remaining tuple. Its completed callback builds the inline child fragment,
   records the residual, and runs `identity_actual_parent_tail`. It does not
   finalize a selected raw slot or invoke `continueWith`.
5. Only the `captured` frame runs `Finalize.run` on the original selected uv and
   invokes the root hook. It is reached after every nested parent tail is empty.
   `continueWith` then performs the actual Left callback and restart decision.
   The configured recur operation is `resumeWithNarrow` with the same eager child.
6. A true parked result directly invokes the next recursive resume. This occurs
   at that outer selection phase. It does not retain a same-branch staged tuple
   that can resume after the clear.

The phrase "parent slot expanded/replaced, remaining staged children retained"
therefore does not describe an actual successful parent-finalization transition
in this worker. Ordinary inline row frames do retain remaining children. They do
not run that raw-slot finalizer. The actual parent finalizer follows the completed
staged list. Entry and selected-value preparation also preserve the slot values;
`SelectedPreparation.complete` states this explicitly. This audit does not assume
that every intermediate stored parent slot is immutable under every operation.
The control exclusion does not require that stronger invariant.

Exact existing producers

- Public definitions `visitChildren`, `visitSelected`, `eagerChild`, `shallowVisit`,
  `consumeSelected`, and `continueWith` expose the concrete call order.
- Private checked `identity_selected_frame_callback` states the exact selected
  callback equation. Its result evaluates the parent tail, and wraps the returned
  complete or stopped result with the row receipt.
- Private checked `identity_actual_source_return_tail_run` identifies the resumed
  tuple with that literal parent-tail program.
- Private checked `identity_actual_source_selected_return_run` states the same
  equation at `SourceTask.run`: a selected frame with an empty inner tuple runs
  the actual restored parent tuple, then retains its receipt around the result.
- `IdentityActualSourceOrigin.selectedReturn` produces the resumed parent tuple
  only from an actual empty inner tuple. `fallbackChildTail` produces a tail from
  the actual successful shallow ChildDispatch singleton. Neither constructor is
  an arbitrary clear between children.
- `identity_captured_frame_generation` identifies the root captured-row operation
  with the exact staged `visitChildren` program and its generated root callbacks.

The existing equations keep original workFuel, recursiveDepth, graph, metadata,
selected uv, actual caller/query endpoints and captured caches. Their headers and
key definitions are copied verbatim to EXACT-SOURCE.md. No new operational or
history API was introduced.

Alternative rows

`SharedBranching.scan` completes the current visitor and hook before its suffix.
Every suffix visitor receives the same captured enumeration cache `before`.
Only the returned native caller and queries pass to the next alternative. Thus
an earlier row may complete, clear a class during its recursive continuation,
and emit an output before a later alternative starts. The later alternative can
still refer to a raw target from the earlier captured input. Its enumeration
state is the restored input of a different output branch. It is not a transition
from the earlier parked state on the same output branch. Earlier emitted output
objects retain their own cached states. A later stop keeps those output prefixes.

This distinction is required. A permanent-isolation claim across chronological
execution of all sibling alternatives is unsupported. The useful claim follows
one emitted output's enumeration-state lineage. The source's shared native heap
still grows across siblings; these control equations do not prove native-language
preservation at that grown heap.

First missing formal composition

The existing results do not state a whole-output lineage theorem. The next exact
induction should use the existing actual source origin and frame ledger:

- At each newly parked state, start from the actual clear receipt and its
  `IsolatedPending held handle` producer.
- Before a new selected preparation, preserve that same raw class through actual
  reads, narrowing, native observations and another selected target's operations.
- At each actual source tuple/child/row point, derive Avoids for every remaining
  input and every deferred ancestor tail from its real captured entry, actual
  indexed preparation and prior child results. Do not derive this from current
  IncomingAvoid alone.
- Use `prepared_stored_child_inputs` for actual stored/fresh preparation and
  `observed_retained_protected_isolated_pending` for every retained shallow cache.
  Compose their full Protected.classes laws at exact endpoints. The ordinary
  nested row and generated-frame return cases still require semantic induction.
- At `selectedReturn`, evaluate the parent tail from the actual empty inner tuple
  before the captured root hook. At the captured hook, no same-branch pending
  staged tail remains. The subsequent clear starts the next phase.
- On an alternative-row restore, use that alternative's captured entry invariant.
  Do not carry a clear created only in the previous alternative into the new
  branch's history. Keep all earlier emitted outputs when a later branch stops.

The required source premise is the configured eager visitor with the generated
captured/selected callbacks. The generic visitor and hook interfaces allow other
behaviour and do not imply this exclusion. No future protection, model or trace
oracle is a valid substitute for deriving these actual origins.

Strategy consequence

The focused deferred-tail scenario does not refute permanent isolation along an
actual output branch. The phase-based strategy remains possible. Its global
source-origin and frame induction is still open. Isolation controls suspended
references and UF classes. It does not by itself solve repeated-path equations,
proper-prefix compatibility, narrowed native-domain inhabitance, stored fragment
and residual constraints, or backward reconstruction of cleared buckets.

The original target is unchanged: each actual original emitted partial root,
including outputs before a later stop, needs one finite accepted completion and
one UF-consistent assignment for its supported native domains, all retained and
historical removed raw path occurrences, fragments, aliases and residuals. No
independent witness splicing or conditional postModel-to-removedHolds replacement
is claimed here. No Haskell fix was found or made.

This packet contains only an audit, exact existing source excerpts and hashes.
No compiler, live Lean, Git, board, Haskell or /tmp writes were used.
