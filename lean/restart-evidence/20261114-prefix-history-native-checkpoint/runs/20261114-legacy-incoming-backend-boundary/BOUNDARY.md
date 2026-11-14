# Incoming backend boundary

Recorded: 2026-11-14 22:01 CET.

The strictly checked incoming-reading repair a8ea719d targets
SourcePruningEnumerationIncomingNode.run. It is a secondary non-shared result.
The terminal-child interval 2439392f and its syntax repair cd5ae46f target
SourcePruningEnumerationChildDispatch.run and SourcePruningEnumerationTerminal.
The syntax repair is uncompiled. Those operations do not establish an interval
for the optimized shared eager worker.

The current worker uses SharedChildDispatch, SharedCachedTerminal, and
SharedIncomingNode. SharedIncomingNode retains shared faults, caller state,
fourth memo, and private snapshots. It reuses pure finish helpers from the
older module. It does not call the older IncomingNode.run.

The pure native first-node step is the same literal NativeDemand instruction
and can be reused with its exact premises. No whole backend equivalence is
claimed. Current shared interval and incoming observation proofs need their
own actual operation equations. The shared callback and common terminal-prefix
results remain valid. No legacy interval was published as a current bridge.
No Haskell defect or fix was established.
