# Closed binder exposure

`EnumerationBinderExposure` derives local closedness and language obligations
from the finite lexical representation in `Binding`. The repaired source
`boundDepth` calls `nodeEdges` for every interned node form. That closure
unfolds `Mu` without consuming constructor depth. Bounded recursion then
consumes one depth unit at each constructor child. A raw `Rec` request remains
an error.

`substitute_free` proves the free-reference property of the actual masked
substitution. `substitute_closed` then proves that closed replacements for
all free references produce a closed result. These proofs do not assume a
language relation for substitution.

`unfold_closed` applies that result to prepared self-substitution.
`unfold_exact` derives freshness from the closed binder. It needs no separate
freshness premise. `unfold_bounded_exact` proves exact language preservation
at the same constructor height.

`RequestStep` contains the primitive closure and child requests: unfold a
binder, select a union member, or visit a constructor child. `reachable_closed`
proves that every finite sequence of these requests stays closed.
`no_unexpected_reference` excludes a raw reference at every reached shape.
It does not require a finite global identity set or a traversal schedule.

The executable `expose` worker checks finite fuel-based exposure. It unfolds
binders, collects ordered union rows, and retains constructor payloads and
ordered children. `expose_spec` proves exact successful row language and
closed output children. `expose_bounded_exact` retains the original depth
bound. `expose_error_fuel` separates execution exhaustion from an unresolved
reference. This worker has no semantic preservation premise.

## Closure and source repair

A valid epsilon cycle can exhaust every fuel value in `expose`. That worker
is not the visited `nodeEdges` implementation. `EpsilonUnion.collect_exact`
proves the visited algorithm on a finite graph. `LexicalBinderClosure` now
derives a concrete finite request domain from closed lexical syntax. Its
`visited_exact` and `exposed_rows_exact` connect that inventory to a terminating
visited epsilon closure, including nested binders and self-substitution.

The source formerly bypassed `nodeEdges` at a root `Mu` in `boundDepth`.
`createMuDontCleanup id` and a retained two-binder forwarding cycle are closed
public inputs, but that branch recursed at the same depth before memoization.
Both timed out after one second while their `nodeEdges` calls returned empty
immediately. The repair routes these roots through `nodeEdges`; both now
produce an empty bounded automaton. There is no separate same-depth `Mu` memo
alias branch. See `notes-lexical-binder-closure.md` and the retained
`repro/BoundRetainedBinders.hs` for source validation.

## Representation boundary

The remaining adapter must connect the source's rebuilt, interned binders to
the finite lexical instances. Runtime identities, alpha-renaming, smart
constructor cleanup, and storage are not proved by the lexical model.
`finite_identity_image` derives finiteness for a fixed identity function; it
does not establish that correspondence for the mutable Haskell allocator.
The bounded builder starts from exposed constructor rows. Neither module
claims full equivalence of its trace with the Haskell memo trace.

## Validation

`lake build MicroCFTA.EnumerationBinderExposure` checks this module.
`lake build MicroCFTA.LexicalBinderClosure` checks the derived finite closure
and visited row adapter. The principal declarations use only the standard
Lean logical axioms.
