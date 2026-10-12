# Recursive equality reduction growth

The bounded source probe on 2026-10-12 confirms rapid representation growth
inside one public `reducePartially` call. It does not prove nontermination.
It does not establish a failure of refinement `prune`. The refinement
validator rejects equality paths that reach cyclic states. This example is
a closed equality automaton, but it does not satisfy that LTA restriction.

## Small example

Use these closed, unconstrained child automata:

```haskell
leaf = Node [Edge "a" []]
step child = Node [Edge "f" [child]]
a = createMu $ \r -> union [leaf, step r, r]
b = createMu $ \r -> union [leaf, step r]
root = Node [mkEdge "triple" [a, b, a]
  (equalityConstraint $ mkEqConstraints [[path [0], path [1], path [2]]])]
```

Both children denote `{ f^n(a) | n >= 0 }`. The root accepts exactly the
triples with three copies of one term from that language. Direct membership
accepts `triple(a,a,a)` before reduction.

`reduceEqConstraints` narrows each position by an intersection of the other
positions. It repeats until the interned child identities stop changing.
For this example, the first three passes produce these maximum binder depths:

| Pass | Child 0 | Child 1 | Child 2 |
| --- | ---: | ---: | ---: |
| Input | 1 | 1 | 1 |
| 1 | 3 | 2 | 3 |
| 2 | 6 | 4 | 6 |
| 3 | 14 | 9 | 14 |

All three completed passes preserve the child term lists through depth four.
A fresh process times out after three seconds when it forces the result of
one `reducePartially root` call. A separate pass diagnostic also times out
during pass four. Each process has a 128 MiB heap limit, a 16 MiB stack limit,
and an eight-second external timeout. No diagnostic process remains active.

The direct probe is `/tmp/microcfta-reduction-small.hs`. Its `public` mode
runs the public call with `System.Timeout.timeout 3000000`. Its default mode
checks membership, binder depths, and the bounded term lists. The logs are
`/tmp/microcfta-reduction-small-public.log` and
`/tmp/microcfta-reduction-small-rounds.log`.

## Original case and boundary

The original epsilon-union masks `(23,51,54)` denote `f* a`, `f* {a,b}`, and
`f* b`. The intersection language is empty. Initial pair intersection is
fast. Repeated equality reduction instead produces binder depths
`(3,3,3)`, `(7,5,7)`, and `(17,11,17)` before the next timeout. The smaller
masks `(6,2,7)` reproduce the same depths. Their languages are empty, empty,
and `f* a`.

`createMu` removes an unused binder and a body that is only its own reference.
It retains a self-reference within a union. Intersection preserves those
unions and introduces binders for recurring pairs. The reduction fixpoint
compares interned identities. Language equality does not stop that fixpoint.
The observations show substantial intermediate growth; they do not establish
an infinite sequence or a bound on the remaining work.

## Conservative repair

`reduceEqConstraints` now skips a whole equality class when any selected path
crosses a recursive binder, a free reference, or an opaque union. It also skips
the class when a selected endpoint contains a nested binder or free reference.
The check uses the stored shape. It does not unfold a recursive node.

The original equality class remains on its transition. Membership and
enumeration still enforce it. The repair therefore removes a recursive
narrowing optimization, without adding or removing accepted terms. A path to
an acyclic sibling remains eligible even when another sibling is recursive.

The reduction suite checks the reported epsilon example, ordinary endpoints
that contain recursion, paths that cross recursion, and paths ending at a
binder below an ordinary constructor. Each case must complete and retain the
original constrained automaton. Another regression checks that an acyclic
sibling domain still narrows. `repro/RecursiveReduction.hs` forces the public
fixpoint and checks accepted and unequal triples, plus bounded enumeration.

A common intersection can replace every child in a class of direct child
paths. That idea does not extend directly to deeper paths: a projected node
can combine alternatives from distinct contexts, and replacing each
occurrence can lose correlation. The repair retains the existing path-local
intersection edits for eligible classes.

This gate removes recursive-domain intersections from the equality-narrowing
fixpoint. It does not establish a termination bound for all remaining acyclic
reductions, repeated outer passes, or the standalone intersection operation.
