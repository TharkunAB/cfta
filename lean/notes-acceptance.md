# Shared and direct acceptance

These files model `microcfta/src/Data/CFTA/Internal/Tree.hs:acceptsBy`.

- `AcceptanceReference.lean` implements matching by symbol and exact arity,
  ordered alternatives, and ordered child conjunction. `accept_exact` connects
  the direct evaluator to `Language.Accepts`, including cyclic automata.
- `AcceptanceCache.lean` derives an immutable subtree registry from the source
  preorder numbering. `number_registered` uses the proved position uniqueness.
  The cache key contains both position and state. `visit_correct` proves the
  hit and miss branches against exact subtree acceptance.
- `AcceptanceWorker.lean` implements the shared worker, with the actual
  short-circuit child and alternative loops. `shared_correct` derives cache
  preservation and exact acceptance. `shared_extends`, `visit_stored`, and
  `visit_hit` establish retained answers and immediate subsequent cache hits.
- `AcceptanceDispatch.lean` implements the source's zero-, one-, and multiple-
  matching-alternative branches. Only the last branch numbers the subtree and
  starts an empty shared cache. `acceptsBy_exact` proves the complete entry point
  accepts every finite accepting run and no other term.

`matching_childrenAt` proves that exact arity makes the direct indexed child
loop equal the ordered child-list loop. `packed_child_safe` connects this to
the small-arity term representation. The source's partial child lookup does
not fail on these checked accesses.

The height parameter makes the Lean recursion total. The public theorem uses
the input term's height. It does not restrict the automaton to an acyclic
graph or assume a correct cache supplied by the caller. Numbering, an empty
cache, and the recursive worker establish the required invariants.

The guard interface here is a stable Boolean predicate for each state,
alternative, and complete term. The source accepts a monadic callback. Its
effects, exceptions, solver trust, and a complete trace-equivalence theorem
are outside these Boolean language proofs. The execution definitions preserve
the specified short-circuit order. Cache hits intentionally omit repeat
callback execution. Mutable or history-dependent callback truth does not
describe the same fixed language and is not assumed equivalent.

The cache model uses the extensional lookup/insert contract of `Map`; it does
not verify the balanced-map implementation. Numbered positions use natural
numbers. Correspondence with the source's `Int` counter requires that the
number of term constructors fit its nonnegative range.
