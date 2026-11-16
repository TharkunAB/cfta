# Entry readback and the prepared ordinary parent

The general captured row path does not imply that Entry.enter returned an ordinary .node. This is an applicability limit of the earlier d681 local header, not a Haskell defect or a counterexample to the full goal.

SharedPreparedChildPolicy.runWithChild first calls SelectedPreparation.run. That result retains decoded in the raw entry row and preparedValue in the native preparation result. SelectedValue.run unfolds a Mu once and exposes a Union before constructing an ordinary node. Therefore decoded may be a recursive-boundary value while preparedValue is an ordinary node.

Source anchors:

- SourcePruningEnumerationSharedPreparedChildPolicy.lean:25-57 dispatches captured rows from the prepared native value, while preserving the separate raw decoded entry.
- SourcePruningEnumerationSelectedPreparation.lean:45-53 retains the exact entry observation and invokes SelectedValue.run on decoded.
- SourcePruningEnumerationSelectedValue.lean:18-33 defines the distinct Mu, Union, and ordinary cases.
- SourcePruningEnumerationSharedEagerReservation.lean:20734-20856 retains decoded and value as distinct parameters and selects the captured scan using value's ordinary-node shape.
- SourcePruningEnumerationSharedEagerReservation.lean:12706-12713 stores root.incoming but no equality between it and the captured slot's native readback.
- SourcePruningEnumerationSelection.realized derives the actual selected flag !(recursiveBoundary value && scs.isEmpty).
- EnumerationDischargeHistory.packet_restart_ne already proves original selected uv != held from the original Packet, actual decision, isolated pending store, and boundary native read. PrefixIsolatedAtOriginalBudget.prefix_isolated_at_original_budget exports this same inequality at every original workFuel.

The new local producer retains both native values. It derives the actual captured target = uv from the literal successful entry and its past Ready. The original selected uv != held then discharges captured != held. It also recovers the exact entry equation, decoded lookup, and native preparation equation. No decoded=preparedValue equation is introduced.

The full structural history proof still needs the actual original selection qualification, original isolated-boundary history, and the prepared Ready receipt. Existing real-prefix resources supply the latter before the preparation call. This packet does not prove whole906, alter original5493, or replace the joint finite-completion target.
