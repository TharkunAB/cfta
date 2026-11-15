[2026-11-15 06:33 CET]

These are reductions of the pinned definitions. They are audit equations, not
new compiled declarations. All observations and endpoints below are literal
arguments of the actual functions. No result of a future call is a premise of a
new invariant.

Let `receipt := SelectedEdge.Result.stopped completed observation candidate`.
The selected-frame stopped callback has the following reduction. Its `tail`
contains the parent's deferred children.

```lean
consumeSelected tail entryCaller entryQueries receipt =
  match NativeContinuations.advance receipt with
  | none =>
      .stopped [] [] (.edge (some receipt)
        (NativeContinuations.endpoint receipt entryCaller entryQueries))
  | some (reached, saved) => .complete [receipt] [] reached saved
```

Neither branch applies `tail`. A Fold.complete result here is not a completed
SelectedEdge receipt and does not invoke a child success callback automatically.
`visitChildren` is a callback program, not a bind on Fold.complete.

The captured-frame stopped callback reduces to the same two branches through
`SharedReceiptContinuation.run hook entryCaller entryQueries (some receipt)`.
The function term `hook` is the configured `continueWith` closure. It is passed
to `run` but is not applied in either stopped-receipt branch.

For the one advancing stopped observation, both reductions specialize to:

```lean
let observation := (.ok (some []), reached, saved, outer, waiting)
let receipt := SelectedEdge.Result.stopped completed observation (some candidate)
consumeSelected tail entryCaller entryQueries receipt =
  .complete [receipt] [] reached saved

SharedReceiptContinuation.run hook entryCaller entryQueries (some receipt) =
  .complete [receipt] [] reached saved
```

For every other stopped observation/candidate constructor combination,
`advance receipt = none`. This includes native faults, ok-none, stopped raw rows,
an empty raw result without a cache, and a singleton result without a cache.
The return is Fold.stopped with no outputs from that failed attempt. The exact
stopped receipt and its actual endpoint remain in the edge stop. A failed
finalization also returns an edge stop without applying the hook, as the existing
`finalize_stopped` theorem states.

Only a SelectedEdge.Result.complete receipt applies the hook. The existing
`SharedReceiptContinuation.stopped_hook` equation is:

```lean
-- Given the actual hook equation:
hook fragment reached saved after = .stopped outputs reason actual
-- The receipt continuation is:
SharedReceiptContinuation.run hook entryCaller entryQueries
  (some (.complete fragment reached saved after)) =
  .stopped [] outputs
    (.continuation (.complete fragment reached saved after) reason actual)
```

This stop may retain outputs from earlier recursive alternatives. It does not
imply that no restart or clear occurred earlier. The completed receipt was
assembled before that hook call.

The pinned `continueWith` definition distinguishes all callback results:

```lean
let raw := ExceptT.run (recordTypes graph templates callbackFuel metadata uv
  (.inl fragment) before.core)
match raw with
| [.ok ((true, _updated), _observed)] => .complete [] caller queries
| [.ok ((false, updated), observed)] =>
    let after := EnumerationExpandableIndex.frame observed before
    recur updated caller queries after
      (Restart.decision stop order updated after)
| _ => .stopped [] (.callback uv raw) (some (caller, queries))
```

The raw true and unsupported cases do not restart. The false case uses the exact
observed core and the supplied stop/order/work budget. In the configured worker,
stop is none. No extra stop rule is introduced by this audit.

Finally, a completed scan prefix retains its outputs when the suffix stops.
This is the stopped branch of the existing `SharedBranching.scan_complete`:

```lean
-- Actual head visit:
visit edge caller queries before = .complete processed outputs reached saved
-- Actual suffix result:
scan visit before rest reached saved = .stopped later remaining current
-- Combined result:
scan visit before (edge :: rest) caller queries =
  .stopped (processed ++ later) (outputs ++ remaining) current
```

The suffix receives the original captured `before`, not a cache from a previous
hook's recursive branch. `SharedPreparedRecursive.finish_stopped` retains this
complete output list in HookResult.stopped. It does not run a deferred tuple or
remove earlier outputs.
