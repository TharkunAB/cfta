# Mixed editor store effects

The three public endpoints use the same actual constructor or Head return. They retain `MixedShared.Stored`, checked `Ready`, and the existing physical effects. The stored record and original captured forest stay fixed.

`node` uses the literal `makeNode` effect. The constructor creates no Mu record. `edge` uses the literal raw `makeEdge` effect and retains its exact children. Its guard can be constrained. Both endpoints derive the final current native invariant with `CurrentNative.advance`. The equality operations and native memo tables stay unchanged at this heap advance.

`head` obtains the final guard heap from `ProjectionGuard.head` at the supplied actual Head. It derives the initial causal Mu store from the initial guard heap with `GuardNative.stored`. `ConstrainedCapExposure.head` then proves the returned cap at the same depth. The endpoint requires initial available and closed input with a cap. It requires no result cap, result guard heap, hereditary annotation, `AtLeaves`, or future execution law.

The private advance proof uses the actual physical extension and the final guard heap already derived from that operation. `MixedShared.advance_stored` retains every universal Merge certificate and exact captured target-slot certificate. No source model or slot value is replaced.

## Validation

The pinned Lean 4.34.1 strict direct check has exit code 0 and an empty log. The root canonical build completes 1430 jobs. That build replays one older unused-input warning from `InternedFreshOrdinaryClosedCompletion.lean:24`. It emits no warning for this module. The imported public probe has three full explicit signature and axiom pairs. The two imported integration pairs pass without diagnostics. Their axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.

`edge_then_node` constructs a literal raw edge and then a node from its actual returned resident edge. It allows an arbitrary allocated guard and derives a depth-one cap on the actual node. It retains the stores, checked readiness, and composed effects. It proves that target slots, Merge memo, and equality operations stay equal to their initial values.

`constructed_recursive_head` starts from legitimate initial available, closed Mu input and cap facts. It constructs its own finite Head with `SourceEqualityRequiredHead.complete`. It applies the new Head endpoint to that same graph and return. It derives stored invariants, readiness, physical effects, availability, same-depth cap, closedness, and ordinary output. It also proves exact target-slot, Merge-memo, and equality-operation retention. It assumes no completed Head graph or future result law.

## Scope

The production endpoints verify actual constructor work and supplied actual Head reads. The second integration kernel independently constructs the Head. This component does not prove editor or class completion, cumulative resources, or recursive outer termination. The separate editor lift can consume these three endpoints without a hereditary callback premise.
