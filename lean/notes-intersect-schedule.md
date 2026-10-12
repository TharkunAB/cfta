# Recursive intersection schedule

`IntersectSchedule.lean` ports `Interned.Operations.intersectOpen` and its
edge worker. It follows the source guard order. It includes empty inputs,
the closed-environment reset, closed self-intersection, canonical node order,
the repeated-pair cutoff, all three binder cases, both explicit union cases,
free-reference lookup, and the equal-symbol row join. The edge worker checks
arity, preserves child positions, and conjoins complete guards.

The input type contains only fully interned references. A `RecInt` shares its
binder's identity. It retains the source's separate ordering tag. The pair
name orders identities independently of those tags. Distinct ordered pairs
have distinct names. The output uses explicit recursive syntax before
physical allocation. Empty edges and unions have their exact language
representation. Their physical smart-constructor representation is separate.

`run_scoped` proves that every free output reference names an enclosing
intersection pair. `top_closed` proves that completed top-level outputs have
no unresolved references. The only representation premise of this result is
that copying a closed input gives closed syntax. `maybeMu_exact` derives
the optional binder's least-language semantics from the proved cleanup rules.
`run_stable` proves that every successful bounded output is unchanged at
all larger bounds.

`IntersectDomain.lean` derives coverage for binder bodies, union members, and
constructor children from the cached free-variable equations. Environment
extension retains typed old bindings and adds every encountered binder.
`run_no_lookup_failure` proves the complete two-worker schedule cannot call
the partial free-variable lookup with a missing name when the inputs and
domain satisfy those structural invariants. Closed top-level inputs satisfy
the initial coverage requirement. Their bounded executions either succeed
or report fuel exhaustion.

`IntersectExamples.lean` executes intersection of two separately interned
recursive unary-chain languages. The result has one recursive binder.
`unary_intersection_exact` proves its least language equals the intersection
of both input languages for every finite term. Separate executed examples
show that a repeated pair stops before free-variable lookup, and that a raw
open pair without an enclosing binder reports the explicit missing-name error.

`IntersectSoundness.lean` proves whole-language inclusion for every successful
bounded execution. `InputMeaning` states independent constructor, union, and
binder language equations. It also states the meaning of a closed input copy.
It does not assume the meaning of intersection. The proof follows both workers,
preserves the meaning of every enclosing pair, and uses least-language
induction for each generated binder. It includes the closed-environment reset.
`top_sound` states that every accepted output term belongs to both inputs.

`IntersectCompleteness.lean` proves the reverse inclusion. It uses the combined
rank of two finite input derivations, then the execution bound. A binder unfold
strictly decreases the derivation rank. This permits induction through each
generated least binder. `run_complete` covers every schedule branch, including
resets and remembered-pair cutoffs.

`IntersectInput.lean` defines independent finite input derivations. These
derivations use input rows, unions, and binder bodies. They do not mention
intersection. `finiteInputMeaning` derives the language equations required by
soundness. `finiteRankedInput` derives the rank laws required by completeness.
`finite_intersection_exact` proves that every successful top-level output has
exactly the common input language. Its representation premises are canonical
identities, valid reachable payloads, and exact copying of closed inputs.
It does not assume language correctness of intersection or termination.

`IntersectProgress.lean` proves that all recursive calls between environment
resets form a well-founded relation. The measure counts remaining binder pairs,
then structural constructor and union weight, then the canonical-order phase.
The local weight stops at binders. Each new binder pair strictly decreases the
first component.

Termination remains open. Language equivalence now holds for every completed
execution against independent least input semantics. The closed-environment
reset clears remembered pairs before the cutoff check.
A termination proof must also measure the structure of closed descendants.
Payload lookup, cached free-variable sets, closed-copy semantics, finite input
weights, and typed memoization remain explicit representation interfaces.
