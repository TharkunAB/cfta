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

These are operational and binding invariants. They do not yet prove global
language equivalence or totality of this cyclic source schedule. The closed
environment reset clears the remembered pairs before the cutoff check.
A termination proof must use the structure of closed descendants as well
as the finite set of intersection pairs. Payload lookup, cached free-variable
sets, and typed memoization remain explicit representation interfaces.
