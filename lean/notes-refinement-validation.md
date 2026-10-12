# Finite refinement automaton validation

`RefinementValidation` models the pure traversal and validation phase in
`Data.CFTA.Refinement.Automaton`. A transition retains its base symbol,
refinement, ordered children, and complete guard. The guard-path extractor
and cycle-membership predicate are explicit inputs.

`childAt` models signed `ChildIndex` lookup. Negative indexes return no
child. `descend` visits every alternative at each index. Its deduplication
keeps the first occurrence of each identity. `descend_exact` and
`nodesAt_exact` derive exact endpoint reachability from these list
operations. `nodesAt_nodup` proves unique endpoint identities.
`transitionsAt_exact` includes the distinct empty-path behavior: the empty
path returns the supplied transition, whereas `nodesAt` returns no nodes.

The validator uses the owning node for an empty guard path.
`endpoints_exact` and `empty_guard_checks_owner` prove that rule.
`offending_exact` proves that the source scan includes every listed guard
path and every cyclic endpoint. An absent path has no endpoints. This phase
does not reject a path merely because it is absent.

`arityEntries` projects only the base symbol and child count. Refinements
cannot make two occurrences of one base symbol use different arities.
`arities_exact` connects that projection to the existing executable arity
checker. `validate` preserves error precedence: it reports an arity error
before it scans cyclic guard references.

`validate_exact` proves that validation succeeds exactly when a base-symbol
arity assignment exists and no listed guard endpoint is in the supplied
cycle set.

`located` also derives the checked rows. It uses the terminating finite
worklist from `EpsilonUnion`, follows every child of every alternative, and
sorts the resulting identities before it reads their rows. `located_exact`
proves that its rows are exactly the reachable rows. The finite identity
list must be complete and have no duplicates. `guard_endpoint_reachable`
proves that every inspected endpoint is in that same reachability domain.
`validate_located_exact` combines the traversal and validation results. It
has no desired-row or successful-validation premise.

## Remaining interfaces

The model starts after `explicitView` succeeds. It does not prove the source
`toFTA` conversion, closed binder-to-identity correspondence, or generation
of the finite complete identity list. Raw recursive references are excluded
from that supplied finite identity graph.

The cycle predicate is supplied. This module does not derive it from the
source SCC implementation. The guard-path function is also supplied in its
source traversal order. Its connection to `constraintPaths`, host maps,
identity ordering, and machine integers remains a representation adapter.
No theorem here decides guard truth or proves accepted-term equivalence.

## Validation

`lake build MicroCFTA.RefinementValidation` checks 23 theorems and ten
dependency modules. The principal declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.
