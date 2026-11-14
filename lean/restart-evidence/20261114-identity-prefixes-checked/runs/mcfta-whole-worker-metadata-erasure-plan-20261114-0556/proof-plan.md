# Proof dependencies for whole-worker metadata erasure

The final theorem compares exact erased observations of the existing identity eager worker. It does not require successful execution. Every finite-fuel failure remains observable.

## 1. Compile the projection and local transport module

The candidate gives bodies for all five projections and five local theorem drafts. The first compilation should check the nested structural recursion in `eraseFailure`, the receipt constructor cases, and the scan induction. No other theorem depends on a new model or provider.

`scan_erasure` is the required additional fold law. Its left side maps the actual shared scan. Its right side is the same existing scan applied to the mapped actual visitor result. This is a mathematical composition equality. It does not assume that a visitor completes, produces a model, or satisfies a supplied contract.

## 2. Derive `eagerChild_erasure`

The exact header is in `obligations.lean.txt`. It maps the actual eager child result and compares it with the same eager child operation supplied with mapped success and stop continuations. All native inputs, observations, receipts, and endpoints remain fixed.

Use strong induction on `MergedOrdinaryHeight.height incoming`. Unfold the actual `eagerChild` once.

For the fallback branch, unfold `shallowVisit`. The same actual `ChildDispatch.run` observation selects the same success or stop continuation. The required equality is then reflexive.

For the ordinary branch, apply `scan_erasure`. Follow the actual `visitSelected` preparation. Its own-class allocation and staged inputs do not depend on output or reason types. In the successful singleton case, use a local list induction through `visitChildren`. Each child continuation carries the remaining tuple inside its callback. Preserve this order. Each tuple prefix receives the same fragment, caller, cache, and query memos after mapping.

The child visitor contains an explicit strict-height test. In its true branch, apply the strong induction hypothesis to the actual child. In its false branch, use the shallow transport case. No assumption that `edgesOf` returns native members is needed for this equality. The actual height test chooses the fallback whenever descent is not smaller.

Case-split the actual receipt in `consumeSelected`. A completed receipt prepends that same receipt to both folds. A stopped continuation retains the same processed prefix and mapped stop. A rejected or unsupported receipt uses the same `advance` and `endpoint`. It does not invoke a new continuation.

The local tuple transport can take the lower-height equality as an induction hypothesis. That is a mathematical equality established by the outer induction, not a premise of the final theorem or an externally supplied visitor guarantee.

## 3. Derive `prepared_erasure`

The exact header compares `(actual.1, actual.2.map eraseFold)` with the actual `runEager` preparation under the mapped hook. It retains the complete preparation result, including all entry rows, native failure, and returned fault heap.

Unfold `runEager` and `runWithChild`. Both sides use the exact same `SelectedPreparation.run` call. Case-split that observation. Missing, failed, or unsupported preparation branches are reflexive. Terminal and opaque branches use `receipt_erasure`.

The ordinary branch uses `scan_erasure`, then the eager-child law through `visitCapturedWith`. Follow the same captured finalization. It receives the same native heap, raw target, fragment, and cache. For a completed receipt, the existing hook is mapped with `eraseResult`. Its complete or stopped constructor selects the same branch. No captured receipt or endpoint changes.

## 4. Prove `resume_identity_metadata_erasure`

The exact header fixes the actual eager child on both sides. It uses the same arbitrary `Option Next` input. This stronger statement supports the real parked and callback restarts. Induct on `recursiveFuel`, generalizing both metadata records, caller, queries, cache, and decision.

| Actual branch | Equality argument |
| --- | --- |
| Decision `none` | The same output has metadata `some`; both payloads map to the canonical record. |
| Decision `some done` | The same output has metadata `none`, cache, caller, and queries. |
| Decision `some stuck` | Both sides return the same empty complete result. |
| Zero fuel and expansion | Both sides retain the same exhausted failure, selected ID, cache, and optional endpoint; metadata maps to the canonical record. |
| Parked empty raw list | Both sides return the same empty complete result. |
| Parked successful singleton | The public prefix erasure preserves the candidate, raw Core, `Next`, and singleton shape. Apply the lower-fuel hypothesis to the two returned metadata records and the same `frame core parked`. |
| Narrowed empty action | Both sides return the same empty complete result at the retained reached caller and queries. |
| Narrowed rejected Right row | The Boolean and reached endpoint survive prefix erasure, so both sides reject identically. |
| Narrowed accepted Right row | The candidate, reached caller, saved queries, false Boolean, and ordinary field agree after prefix erasure. Use prepared transport and the callback argument below. |
| Other selected observation | `eraseFailure.selected` uses the public `erasePrefix`. All retained reached or original endpoints agree. |

The public prefix equality is deliberately lossy in metadata. Do not rewrite it as equality of the un-erased prefix values. Instead, case-split its two actual result values and the relevant `Option`, list, `Except`, and product constructors. The map preserves list length and each error/success constructor. Thus it preserves empty versus singleton versus multiple rows. It also preserves each `Next`, Boolean, Core, candidate, caller, full query memos, and ordinary field. The two metadata payloads can remain different. The induction hypothesis quantifies over both of them.

For the accepted prepared branch, `prepared_erasure` retains the exact preparation and maps the optional fold. If preparation returns no fold, the same `.preparation` reason and computed endpoint follow. If a fold exists, use `finish_erasure`.

The hook equality required in that branch follows from `continue_empty_exact` on each side. Both actual Left callbacks have templates `[]`, so both return false at the same Core. Both recursive calls use the same caller, full query memos, framed cache, and metadata-independent decision. Apply the lower-fuel hypothesis to the two `updatedTypes` metadata records. Pointwise equality of the mapped hooks gives equality of the existing mapped hook functions by `funext`. This supplies the concrete prepared transport; it adds no hook or provider to the worker.

## 5. Close the final entry theorem

`final-entry-proof.lean.txt` gives the wrapper proof after the recursive theorem exists. Unfold `runEagerWithNarrow` and `runWithNarrow`. With stop `none` and the constant order, the two initial restart decisions are identical. Apply `resume_identity_metadata_erasure`.

## Remaining work

The first proof module has bodies but is uncompiled. The eager-child transport, prepared transport, and recursive theorem have exact headers and this concrete dependency plan. They do not yet have complete proof bodies. The final wrapper proof depends on those actual lemmas being proved. No whole-worker theorem is currently claimed by this handoff.
