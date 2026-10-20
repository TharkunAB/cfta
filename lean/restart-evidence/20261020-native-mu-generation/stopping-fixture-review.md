# Actual stopping writer fixture review

Checked on 2026-10-20 at 18:02 CEST. This is the author's source review.

## Actual construction

`actual_pending_writer` has no supplied premises. It derives the empty joint Context. It executes both blocked-body callbacks. The actual cut has no blocked key. Cache.intern reserves that key and leaves the full record absent. Context.reserve derives the warm starting Context.

The root syntax is a union of two raw binders. The first has a nullary row with symbol 9. The second has a nullary row with symbol 7. The first completes. The second replays its original prepared probes, finds its reserved key, and returns pending. The whole union returns the same pending key and state. The key distinction reduces to node identities 0 and 2.

The first binder's complete Mu is absent initially and present at that pending state. The fixture invokes `StoppingBuildRootedWriters.build_writer_or_prior` once. It rules out the initial arm from the concrete lookup. It unfolds the returned old `Written` receipt and retains its one event, rooted source route, exact candidate, first-write fact, issued prefix and callback paths, physical suffix, and issued suffix. No parallel hand-built publication identifies an independently chosen event.

## Checks and attempts

Four capped Lean jobs ran with fresh usage above one percent. Every job has verified memory.max and memory.high 4294967296, memory.swap.max 0, and a five-minute cap. The pinned toolchain is Lean 4.34.1.

The first two strict attempts failed on local elaboration. Attempt 1 needed concrete key reduction and explicit unfolding of the old Written definition. Attempt 2 reduced the key inequality but needed constructor discrimination. Their exact sources, logs and receipts remain unselected.

`stopping-fixture-direct-3` returned zero with a zero-byte log. `stopping-fixture-public-1` returned zero. Its 47906-byte log prints the complete expanded public statement, the full alias proof, and the axiom report with all eight required options. Only propext, Classical.choice and Quot.sound occur. The private checked witness has the same complete statement. No omitted terms, warning, admitted proof or failed printer occurs.

There is one constructed proof pair, zero production pairs, and no canonical job in this fixture component. The official dependency source is 2ccd95c5fc0b271a4446b8f9a2b5732823171e933eacce687c874d7b1711f2ee. The parent checked its canonical build separately.

## Scope

This is an actual warm orphan-reservation stopping example. Its initial full-cell history is not supplied or inferred. The fixture proves the required rich Context from actual callbacks and reservation. It does not assert physical publication history from the empty heap through that orphan reservation.

The selected binder is raw and unused. The example does not claim a used-binder instance, fresh closed-build failure, native maybeMu ownership, original-root capture ancestry, or general termination.

## Portable evidence

The explicit manifest retains every attempt. Foundation snapshots support standalone verification. `--live-root` checks the same snapshots against the live checkout. The mutable peaks file is excluded; its four-row final snapshot is pinned. Receipt commands keep their original temporary paths.
