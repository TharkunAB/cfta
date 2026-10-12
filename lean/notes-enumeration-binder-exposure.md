# Closed binder exposure

`EnumerationBinderExposure` derives two local obligations of `boundDepth`
from the finite lexical representation in `Binding`. The source unfolds
`Mu` at the same depth. The source reports an error if a request reaches a
raw `Rec`.

`substitute_free` proves the free-reference property of the actual masked
substitution. `substitute_closed` then proves that closed replacements for
all free references produce a closed result. These proofs do not assume a
language relation for substitution.

`unfold_closed` applies that result to prepared self-substitution.
`unfold_exact` derives freshness from the closed binder. It needs no separate
freshness premise. `unfold_bounded_exact` proves exact language preservation
at the same constructor height.

`RequestStep` contains the actual primitive requests: unfold a binder,
select a union member, or visit a constructor child. `reachable_closed`
proves that every finite sequence of these requests stays closed.
`no_unexpected_reference` excludes a raw reference at every reached shape.
It does not require a finite global identity set or a traversal schedule.

The executable `expose` worker also checks finite exposure. It unfolds
binders, collects ordered union rows, and retains constructor payloads and
ordered children. `expose_spec` proves exact successful row language and
closed output children. `expose_bounded_exact` retains the original depth
bound. `expose_error_fuel` separates execution exhaustion from an unresolved
reference. This worker has no semantic preservation premise.

## Boundary

The finite worker uses fuel. It does not implement `nodeEdges`' visited
identity set. A valid epsilon cycle can exhaust every fuel value in this
worker. Thus successful exposure is exact, but this worker is not a
termination proof or a complete model of the source closure algorithm.
`EpsilonUnion.collect_exact` proves the visited closure once a finite
identity graph is available.

The remaining connection must derive that finite identity graph from the
interned lexical representation. It must connect its rows to the concrete
builder, including same-depth binder aliases in the memo. The existing
builder starts from exposed constructor rows. This module does not change
that builder or prove its memo trace equivalent to the full Haskell trace.
Host identities, fresh allocation, alpha-renaming, smart-constructor
representation, and runtime storage remain separate adapters.

## Validation

`lake build MicroCFTA.EnumerationBinderExposure` checks the module and its
six dependencies. The principal declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.
