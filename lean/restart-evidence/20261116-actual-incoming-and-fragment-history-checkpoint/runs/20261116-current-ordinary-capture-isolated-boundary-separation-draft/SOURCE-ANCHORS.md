# Actual source anchors

SourcePruningEnumerationEntry.lean:16-33 defines the literal selected entry. After the actual getValue and representative calls, it reads lookupNode at the returned pending handle. Only that read can supply the final decoded node. The local helper extracts this read from the observed singleton run. No supplied bound or force-success assertion is used.

SourcePruningEnumerationNativeOrdinary.lean:25-34 observes Entry.enter at the caller heap and enters the ordinary scan only for the literal .node singleton with a nonterminal bucket. The full worker must retain that actual observation when it creates its captured frame.

SourcePruningEnumerationSharedEagerReservation.lean:17115-17133 defines ActualFrameLedger.captured. It retains the original selected pending store, Packet, Ready, and actual own preparation. It does not retain the complete Entry.enter result. The actual parent/readback link remains an upstream whole-worker history obligation.

SourcePruningEnumerationSharedEagerReservation.lean:1482-1505 defines TupleInputs. Its returned Post originates at exactly the tuple original caller. SourceCurrentAllocatedPartialInvariant.lean:38-45 defines Post.effects. The existing effects.keeps field supplies native cache and record retention at the tuple's reached caller.

SourcePruningEnumerationNodes.lean:50-72 proves lookupNode_keeps for exact successful reads under Keeps. The local result uses this theorem, rather than adding a heap-growth premise.

SourcePruningEnumerationCachedOwn.lean:22-41 defines the actual own-class preparation. It allocates enum variables and retains the native heap as an input. The separate captured-pending producer is responsible for transporting the original captured pending lookup to rowOwn. This packet does not identify the two cores or duplicate that producer.

MergedOrdinaryHeight.lean:88-91 makes recursiveBoundary false on every ordinary .node. IsolatedPending.stored and the actual captured pending store identify their handles if their raw slots coincide. Native lookup uniqueness then contradicts the supplied actual boundary read.
