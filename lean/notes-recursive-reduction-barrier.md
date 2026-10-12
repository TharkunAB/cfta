# Recursive equality reduction barrier

`RecursiveReductionBarrier.nodeMeets` follows the repaired
`Equality/Operations.hs` helper. Rec, InternedMu, and InternedUnion return
True before any metadata test. Other nodes return False when the stored
nested-binder depth is zero and the free-reference set is empty. At a path
endpoint, any remaining node returns True. At a longer path, an ordinary
node visits the selected child of each edge. Missing children return False.
The outer `meets` helper treats the edge root path as False.

`Read` is the projection of the source node tag and cached metadata. It does
not interpret a recursive body or assert a language for that body. The gate
does not call unfolding, intersection, or recursive-reference resolution.
`bounded_exact` proves that path length plus one is a sufficient recursion
budget for every node query, including cyclic graph views. This is a bound
on descent depth. It is not a bound on the number of alternative rows visited.

`endpoint_clear` characterizes every permitted endpoint.
`selected_iff` gives the exact whole-class filter. `class_skipped` proves that
one blocked path excludes that class from narrowing. `finite_classes_selected`
proves that finite nonopaque children retain every original selected class.
The executable fixture also checks that a finite sibling remains eligible
beside a recursive sibling.

`completed_exact` composes this exact gate with `EqualityReduction`. Every
completed pass sequence retains precisely the terms satisfying the original
local and inherited equalities. The edge constraints are not replaced by the
selected class list. The theorem uses the existing eight local graph-action
laws: empty, intersection, projection coverage, required-path narrowing and
retention, edit narrowing and retention, and contradiction soundness. It does
not assume the correctness of a whole pass or repeated reduction.

`blocked_terminates` proves one-pass termination when every class is blocked,
the constraints are consistent, and the initial children contain no EmptyNode.
Its only additional operation equation is `requireAll [] nodes = nodes`.
That equation follows directly from the source empty Needed map and its
empty `IntMap.foldrWithKey`. No representation-stabilization premise is used.
Empty-child and contradiction cases remain under `completed_exact`; this
one-pass theorem does not give them an unsupported syntactic termination bound.

`LeafTriple` models the exact six residual intersections in a simultaneous
three-leaf equality round. `RecursiveReductionSourceOrder` instantiates it
with the proved source Guard comparator and executable structural equality.
For every three equally labelled finite leaf guards, one round produces one
identical canonical common guard. The next pass is structurally unchanged.
`terminates_two` proves the source-style identity loop returns after at most
two passes. `common_exact` connects that canonical residual to the current
public evaluator: a term must be confirmed by all three original guards.
Neither result assumes language equality implies representation equality.

The finite leaf result does not prove termination for arbitrary finite DAGs.
Overlapping paths, multiple constructor alternatives, nested constraints,
and the complete source sparse-trie adapters still require representation
invariants. The recursive barrier avoids the reported repeated recursive
intersections; it does not prove termination of standalone intersection or
arbitrary repeated outer `reducePartially` passes. Cached metadata extraction
and mutable interning remain separate representation obligations.

Validation: the pinned toolchain builds both modules. The source repair's
Haskell tests and retained reproduction are recorded separately in
`notes-recursive-reduction-growth.md`. No proof uses an admitted declaration
or native proof evaluation.
