# Same-path unfolding in the current equality gate

The source gate in `Equality/Operations.hs` unfolds an open unconstrained
`InternedMu` without consuming a path index. Closed unconstrained binders
return false. References and stored unions return true before metadata
shortcuts. The source checkpoint for this work is `microcfta` at `de910ea`.

`RankedGateCompletion` proves that any supplied `UnfoldingRank` gives a
finite successful instrumented run for every path. Every larger fuel
amount returns the same result as the unbounded worker. The proof combines
finite child lists with the lexicographic path-length and unfolding-rank
measure. It does not treat exhausted fuel as a Boolean source decision.

`LexicalGateRank` derives such a rank for `InternedSubstitution.run`.
The rank counts consecutive root binders. It stops at a constructor,
reference, empty shape, or alternatives list. A root binder chain that
ends at a free reference has exactly that one free name. An open outer
binder therefore cannot replace its own reference at that head.
Fresh nested reconstruction and cleanup cannot increase the remaining
head rank. This proves strict decrease on every open binder unfolding,
independently of its constraint predicate. The concrete `ranking` has no
caller-supplied termination premise. `eventually_exact` proves finite fuel
completion for this adapter. `ranked_unfold_exact` connects the same
unfolding operation to the complete open least-language equation.

The lexical result includes nested binders and arbitrary constructor
children. Its union representation retains an alternatives list after
root self-reference removal. That detail prevents direct transfer to all
source interned nodes.

`InternedGateRank` proves the relevant source smart-constructor facts from
the existing coherent cache executor. `makeNode_rank` includes removal of
empty-child edges, canonical edge identities, and cache hits. It returns
rank zero. `ordinary_unfold_decreases` therefore supplies the actual final
substitution branch decrease for an ordinary binder body. Rebuilt children
need no rank premise. They may contain arbitrary open or closed binders.

`makeUnion_rank` gives the exact source result. Flattening and identity
deduplication produce either a singleton, whose rank is retained, or a
rank-zero result. `union_unfold_decreases` covers every nonsingleton result.
The kernel fixture `filter_can_expose_binder` constructs a recursive operand
through the actual constructor executor. Root self-reference removal then
changes head rank from zero to one by returning the remaining operand.
Thus the lexical list-filter rank equation is not a source rank equation.

The remaining general source obligation is a construction invariant for
normalized singleton unions and rebuilt nested binders during substitution
of the outer binder itself. These modules do not assume that invariant or
claim complete termination of the source gate. They also do not prove
termination of repeated equality reduction.

The temporary source probe `/tmp/mcfta-gate-head-rank.hs` runs inside the
project Nix environment. It checks 10,000 generated constructor expressions
of depth six. Of these, 3,417 roots are open unconstrained binders. All of
those unfoldings strictly decrease the actual stored head-binder count.
The concrete nested open example has ranks 2, 1, and 0. A raw closed own
reference binder unfolds to itself, which confirms why the source closed
check matters. The source root-filter example has ranks 0 and 1. These
finite checks do not establish the remaining general invariant.

The pinned Lean 4.34.1 build of `MicroCFTA.InternedGateRank` completes 134
jobs. The source probe log is `/tmp/mcfta-gate-head-rank.log`. No Haskell
source changed.
