# Performed enabled-check history audit

2026-11-16 10:10 CET. Read-only source audit. No new proof or compiler result.

## Exact effect on the inherited native tables

`SharedEnabledEmpty.check_performed_receipt` derives the actual true descendant gate and the actual `SharedConjunctionWorker.call p h currentTupleBudget` equation. The supplied `p` and `h` remain unchanged.

`SourceCurrentAllocatedSharedConjunctionWorker.call` builds BOTH successful and failed checked endpoints with `QueryMemo.advancePhysical`. `call_state` exposes that exact equation. `QueryMemo.advance_tables` proves equality of the WHOLE native node table, edge table, and domain cache. This includes returned, evaluating, and absent cells. This phase produces no new cell in either inherited native family.

The phase can change the constructor heap and equality operations. A successful phase can change the fourth memo. A failed phase retains the incoming fourth memo, but retains its actual changed physical endpoint and diagnostic. The outer caller uses its actual phase state and memo. No table reset or substitution by a separately initialized run occurs.

## Existing relation at the exact supplied budget

Use `SourceCurrentAllocatedSharedConjunctionOutcome.verified`, not a finite-completion theorem. Its only semantic entry assumptions are the CURRENT `PartialInvariant.Context` and actual query `Available`. At the supplied `p`, `h`, and `currentTupleBudget`, it derives:

- Actual `SourceCurrentConjunctionSharedWorkerOutcomeMemos.CallReads`.
- Full `PartialInvariant.Post` at the literal raw outcome physical endpoint.
- Query availability, retained unfolding memo, and unchanged query memo.
- Answer soundness on a successful outcome.

`Post.effects` contains constructor `Keeps` and equality-operation `Grows`. `Post.fourthRetained` records fourth-memo extension. `Post.context` supplies the reached current invariants. `Worker.call_state`, `call_memo`, and `call_observation` identify those raw fields with the actual enabled observation. Use `Outcome.verified` for all outcomes; the success-only caller API is not needed.

The descendant gate updates the endpoint query memo BEFORE this call. From its literal gate equation, `SourceEndpointMemoCorrect.run_checked` derives validity of the saved query memo. Rebuild the current Context with that valid query memo, then apply `Outcome.verified`. `SharedIncomingQuery.lean:139-154` already performs this exact gate-context construction. Its later finite-completion argument must not replace an actual performed call at supplied `p` and `h`.

## Composition with the pre-phase QueryHistory

The checked prepared incoming theorem produces the actual native-query `QueryHistory` up to the queried caller. A performed phase does not satisfy a new native-query cons equation and can change the fourth memo. Do not force `QueryHistory` to span this phase.

The existing broader carrier already has the needed constructor: `SourceCurrentNativeEdgeWriterGrowth.History.advance`. Apply it to the queried checked-state history and the actual raw physical endpoint, with growth `post.effects.keeps.growth`. Rewrite the endpoint with `Worker.call_state`. The actual fourth transition remains in `Post`; it need not be added to a new history datatype.

Any FIXED law on returned native cells transports through this phase by the literal whole-table equalities. This applies to both C/M laws and the four auxiliary clauses when all are indexed by the same fixed full H. It is preservation only. It proves neither missing inherited semantic priors nor request qualification.

## Minimal remaining source-call composition

There is no missing phase-effect or native-table preservation primitive. The next source-call composition can use the existing APIs directly:

1. Recover the actual successful incoming native query and closed available operands from the checked prepared incoming receipt.
2. From original caller Context plus its genuine Fits and Admits resource facts, apply `SourceCurrentAllocatedTargetQuery.raw_done_caller_admitted_resources` to that ACTUAL native done equation. This yields the literal queried caller Post/Context and query availability. It neither assumes a future endpoint Context nor changes the observed endpoint or original supplied native fuel.
3. Apply `SourceEndpointMemoCorrect.run_checked` at that queried heap and update Context with the actual saved query memo.
4. Recover the performed call by `check_performed_receipt`. Apply `Outcome.verified` at exactly its supplied `p`, `h`, and tuple budget. Compose the two Posts and append the existing physical History.advance.

The current prepared incoming receipt alone does not expose Fits/Admits. Those are genuine past worker-resource inputs at this integration call site. Do not insert queried Context as a new future provider merely to omit their derivation.

No new observer, history datatype, or generic engine is required for the performed phase. Arbitrary chronological warm C/M semantics and the same-root joint finite-completion witness remain open. No Haskell fix is indicated by this audit.

`EXACT-API.txt` contains pinned declaration excerpts. `SOURCE-PINS.sha256` records all source used here. No Source, compiler, Git, board, root documentation, or /tmp changes were made.
