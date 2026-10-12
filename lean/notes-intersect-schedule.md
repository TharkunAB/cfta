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

`IntersectTotal.lean` proves totality under independent finite input structure.
`InputBounds` supplies a finite list of possible pairs, the local constructor
weight, a size that strictly decreases through direct payload containment, and
a bound on closed-root reachability. Each reachable payload is either that
closed root or strictly smaller. These premises describe the inputs. They do
not refer to intersection execution.

The proof derives environment coverage and protection of each enclosing root
pair. A reference lookup cannot restore both roots because the earlier cutoff
would stop that call. A closed-environment reset therefore strictly decreases
the combined root size. Every other recursive call decreases the local measure.
`call_eventual` proves termination of both workers. `finite_intersection_total`
combines this with exact independent finite input semantics. It gives one
stable, exact result at every sufficiently large bound.

The remaining source bridge must derive these finite lexical-payload contracts
from the smart constructors and their identity allocation. Payload lookup,
cached free-variable sets, closed-copy semantics, finite input structure, and
typed memoization remain explicit representation interfaces.

`IntersectReset.lean` proves why that representation requirement is necessary.
Its deliberate countermodel uses cyclic binder payloads instead of `RecInt`
references. It satisfies `FreeCorrect`, `LocalWeight`, and `FiniteInput`.
Nevertheless, `cyclic_reset_exhausts` proves that every execution bound fails.
`cyclic_has_no_body_weight` proves that no finite structural binder-body weight
can represent it. This is a limitation of the current graph interface. It is
not a counterexample produced by the source smart constructors.
