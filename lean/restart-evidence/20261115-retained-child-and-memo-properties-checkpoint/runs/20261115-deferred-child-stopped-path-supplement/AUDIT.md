[2026-11-15 06:33 CET]

This supplement covers the stopped branches omitted from the complete-path
argument. It leaves the earlier packet frozen. It records source reductions and
existing equations, not a new checked global control theorem. No runtime or
accepted-source counterexample is claimed.

The focused same-branch ordering claim survives this audit. A stopped child
receipt does not invoke the root hook or restart from its candidate cache. A
completed receipt can invoke a hook that later stops and retains earlier outputs.
These are different constructors in different result types.

Stopped callback cases

| Actual callback input | Actual operation and result | Deferred children and restart |
| --- | --- | --- |
| selected frame callbacks.2 with a stopped receipt | consumeSelected uses advance; it does not apply its tail argument. | That failed attempt skips the parent tail. It does not restart from its candidate cache. |
| selected frame stopped receipt with ok(some []) and some candidate | advance returns the reached caller/query endpoint; consumeSelected returns Fold.complete [stoppedReceipt] [] reached saved. | The row scan may try another alternative from its captured cache. It does not run the failed attempt's deferred tail. |
| any other selected-frame stopped observation | advance returns none; consumeSelected returns Fold.stopped [] [] with the exact edge receipt and endpoint. | The scan suffix is not run. The failed tail is not resumed. |
| captured frame callbacks.2 with a stopped receipt | ReceiptContinuation.run selects the non-complete-receipt branch and uses advance. | The continueWith hook is passed as a function argument but is never applied on this branch. |
| captured stopped receipt with retained empty raw result | ReceiptContinuation returns Fold.complete [stoppedReceipt] [] reached saved. | The root row scan may try another alternative from its captured input. No selected-root callback or restart occurs for the failed attempt. |
| any other captured-frame stopped observation | ReceiptContinuation returns an edge stop with no new outputs. | No hook or suffix runs. |
| failed finalization | ReceiptContinuation.finalize_stopped returns an edge stop. | No hook or restart runs. |
| completed receipt whose hook later stops | ReceiptContinuation.stopped_hook retains that complete receipt, all hook outputs, the reason and optional endpoint. | The completed branch entered the hook after its staged children. Later failure does not erase its earlier outputs. |

The .selected stopped path is specifically the second callback of
`identity_actual_frame_callbacks`. It constructs a stopped SelectedEdge receipt
and passes it to `consumeSelected tail`. The non-complete branch does not apply
`tail`. Thus a stopped inner child cannot bypass its remaining parent tuple and
call the captured hook on an incomplete fragment. For an empty rejection it can
return a normal Fold.complete value with no outputs. That value returns to the
row scan. It is not a call of the child success continuation. The scan's next
alternative uses the same captured cache, not the stopped candidate cache.

The .captured stopped path constructs the same stopped SelectedEdge receipt and
passes it to `SharedReceiptContinuation.run`. That function applies its hook only
to SelectedEdge.Result.complete. The stopped receipt takes the separate advance
branch. There is therefore no actual `.captured stopped -> ReceiptContinuation
-> continueWith` invocation. The continueWith closure occurs in the passed
argument, but that branch does not call it. This distinction follows from the
literal function definition.

A stopped return after a completed receipt is different. The hook can call the
recursive driver, emit outputs, and stop at a later alternative or budget limit.
`stopped_hook` preserves those outputs. `scan_complete` appends earlier output
prefixes when its suffix stops. `finish_stopped` preserves the full list again.
The indexed `scan_output_origin` theorem already covers both complete and stopped
scan results. Its identity no-stop specialization locates each emitted output's
actual producing row and local index, including a row whose hook later stops.

What the stronger claims get wrong

- A stopped SelectedEdge receipt need not stop the row scan. The retained-empty
  observation advances normally. Its failed child tail is still not applied.
- A stopped Fold or HookResult need not have an empty output list or lack earlier
  restart/clear operations. The published stopped_hook and scan_complete equations
  explicitly retain earlier outputs. A complete-path-only proof cannot replace
  this case analysis.
- A clear can occur while later alternatives remain in an outer scan's call stack.
  Those alternatives restore the captured enumeration input. They do not resume a
  same-output-branch tuple from the cleared cache. Permanent isolation across all
  chronological alternatives remains an unsupported strategy.

These are exact source-level counterpatterns to the stronger statements. They
are not claims that a specific accepted source program exhibited a runtime bug.
No counterexample to the corrected same-output-branch order was found.

No-stop and supplied budgets

The configured frame installs `continueWith` and `resumeWithNarrow` with Unit,
empty templates, identity narrowing, stop = none, and order = fun _ _ => none.
This audit keeps that configuration and all supplied workFuel/recursiveDepth.
The absence of a user stop rule does not remove native faults, cache failures,
empty rejection, stuck selection or exhausted recursive depth. The pinned
resumeWithNarrow definition retains each of those cases.

The actual parked branch has two relevant outcomes. A parked empty restart
result returns complete [] and does not recurse. A parked successful singleton
recurses directly with its returned metadata, framed core and next decision.
There is no Left callback for the cleared slot. These branches run at the outer
selection phase. The stopped-callback equations above cannot introduce a live
same-branch staged tail into that phase. Native/callback errors preserve their
literal outcomes and endpoints; they are not converted into successful work.

A selected-frame done callback can also receive a stopped result from its parent
tail. `consumeSelected` then wraps that result with the completed row receipt and
keeps the tail's outputs. This may include outputs from an earlier completed
alternative before a later child stopped. The failed alternative still does not
resume after its stop. This is why earlier-output membership and exact branch
origins must remain in the eventual historical proof.

Remaining formal obligation and original target

The complete and stopped reductions support a phase-based proof along an actual
emitted output's state lineage. They do not establish that proof by themselves.
The full source-origin/frame induction must derive every remaining and deferred
input's avoidance at its actual entry, preserve the same raw UF class, distinguish
normal rejection from a terminal stop, and account for captured alternative
restoration. It must extract each output through stopped results as well as
complete ones. It must not infer captured-bucket avoidance from current-store
IncomingAvoid or assume a future callback result.

The original finite-witness objective is unchanged. Each actual original emitted
partial root, including earlier outputs before a later stop, requires one finite
accepted completion and one assignment satisfying all supported native domains,
UF aliases, fragments, residuals, retained obligations and every historical
removed raw target/path occurrence on its actual branch. No model, compatibility
oracle, independent-witness splicing or conditional postModel-to-removedHolds
replacement is supplied by this audit. No Haskell fix was found or made.

NORMAL-FORMS.md records the stopped reductions. EXACT-SOURCE.md retains the
literal definitions and relevant existing theorem headers. SOURCE-PINS.json pins
the complete files. No compiler, live source, Git, board or /tmp writes were used.
