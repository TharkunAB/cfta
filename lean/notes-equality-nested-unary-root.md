# Completed equality iteration through two unary ancestors

The marked `EqualityNestedUnaryAncestorEditCompletion.lean.draft` remains
byte-identical. Commit `64f06047` completes its missing lemma in a new `.lean`
file. The proof destructs the actual `node_complete` witness, retains the
exact output and returned cache, and connects `node_eq`, `edit_stored`, and
each original-index `WorkFacts.meet_correct` result.

`EqualityNestedUnaryAncestorRootStep` performs both actual snapshot unions
and ancestor edits. It derives stored endpoints and their representation in
the actual final cache. `RootIdentity` derives root equality from unchanged
original indexed predicates. Changed roots imply changed indexed state.
An unchanged physical root supplies allocation-free replay.

`RootTermination` permits early physical identity stops. It does not assume
that such a stop means the entire indexed state has reached a fixed point.
`RootSource` retains actual target-merge calls and derives their unchanged
result from the row-count bound. `source_termination` completes in at most
`4 * (left + right) + 2` passes. Additional fuel preserves both returned
output and final cache. The completed source step is a fixed point without
allocation.

`RootPaths` connects the actual `getPath [0]` projections, source union and
stored union operations, edits at `[0]`, both `editChildren` paths `[0,0]` and
`[1,0]`, and the ordered root-reference stop check. These are exact result and
cache equations, not assumed root-operation semantic contracts.

The scope is one fixed binary equality class under two ordinary unary
ancestors, represented generated endpoints, and at most two initial atoms.
The proof does not cover arbitrary equality classes, the required-path phase,
the complete propagation wrapper, inherited traversal, or recursive nodes.
Do not generalize the finite fragment to arbitrary cyclic inputs.

Checkpoint: `9e429c23`. The aggregate audit passes 1,180 targets and 39,689
theorem dependency checks using only the standard Lean foundations.
Log: `/tmp/mcfta-closing-20261014-audit.log`.
