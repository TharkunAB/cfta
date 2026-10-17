# Direct outer edge-idle preservation

Reviewed on 2026-10-17. SourceCurrentOuterEdgeIdle covers all eight literal
bounded worker phases. It does not consume a completed graph or range
certificate. Its only state premise is EdgeIdle at that phase's entry.

EdgeIdle excludes every evaluating cell in the edge result family. It
places no condition on node owners, suspended cells, returned cells, or
physical heap validity. Safe requires EdgeIdle at a successful return.
At failure it requires NoEdgeBusy for the reported fault. NoEdgeBusy
excludes exactly the outer edgeMemo busy diagnostic.

The parent edge body retains the outer result tables on every outcome.
It makes no outer request. An edge call can create its own evaluating
edge cell. Success finishes that cell before descendants run. Existing
running-before and finish-not-running lemmas account for every other
handle. Ready demand introduces no evaluating cell. EdgeIdle excludes
the evaluating observation at entry, including malformed table states.

The mutual fuel induction follows the actual worker order. It covers
node calls and bodies, rows, descendants, children, and indexed walks.
Each successful prefix passes its returned EdgeIdle fact to the next
phase. Each failed prefix propagates without running the continuation.
Inherited combination, indexed descent, Mu reconstruction, and raw
constructor effects retain the exact outer edge table. No hereditary
condition, finite Cap, whole-forest closure, source rank, or node-idle
assumption is added.

The first constructed integration builds an ordinary root with one leaf
child. It starts an independent node owner, then runs the full nonempty
outer traversal. The traversal succeeds and retains the active node owner.
Its edge family is idle at return. A later edge demand observes the ready
edge and retains the exact full caller.

The second integration shows a literal node-busy failure from an edge-idle
caller. Thus the result does not exclude node-busy faults. The third
integration starts with a source-built heap but deliberately omits the
original equality field from the operation cache. Its edge body fails
with Parent.missingField and leaves its edge owner evaluating. The fault
propagates immediately. This caller is not asserted to satisfy the full
successful-input Context. The example checks that failure does not have
an unsupported final EdgeIdle conclusion.

Final production strict attempt4 is empty. Canonical attempt1 passes
1413 jobs under 4 GiB MemoryMax and MemoryHigh, with zero swap. It replays
only the existing ClosedCompletion unused-input warning. All twelve public
signature, proof, and axiom pairs pass. All three constructed signature
and axiom pairs pass. The stripped integration strict log is empty.
Only propext, Classical.choice, and Quot.sound occur.

Production attempts1-3 retain proof elaboration diagnostics. They fix
explicit mutual-definition unfolding, exact caller-state transport, and
an output-independent fault predicate. Integration attempt1 retains the
missing explicit name alignment before rewriting its actual outcome.
All failed sources and raw outputs remain unchanged.

This excludes one family of outer busy failures during a bounded run
whose entry is edge-idle. Failed edge bodies can leave active cells, so
a later independent restart from such a caller needs its own premise.
The result does not construct a successful outer call, exclude node-busy,
derive a decreasing origin measure, or prove general mutual termination.
It adds no Haskell behavior change or defect claim.
