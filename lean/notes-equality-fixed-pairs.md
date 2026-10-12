# Fixed binary equality schedules at child roots

`EqualityFixedPairs` isolates a structural progress invariant that does not
require associative node intersection. A binary equality class reads both
nodes from the same input forest. It edits the two distinct child roots with
those unchanged projections. Commutativity makes the two results identical.
The source self-intersection law makes the next class pass unchanged.

`sourcePair_exact` connects the ordered snapshot edits to that symmetric
update. `equal_after` proves equality of the endpoint node identities.
`narrow_commute` proves that classes on disjoint child roots commute.
`source_round_fixed` includes the complete fixed right-fold class schedule
and source empty propagation. `run_two` gives the two-call bound: one possibly
changing pass and one fixed-point test.

The node domain can contain nested alternatives. The theorem needs only the
local commutativity and self-intersection laws, not whole-node absorption,
associativity, a semantic cardinality, or a finite structural universe. It
models the selected binary classes at valid direct child indices. Required
paths already exist there. Gate selection, arbitrary path projection unions,
and larger equality classes are outside this theorem.

A focused temporary Haskell probe used the nested arbitrary-operand cycle
from `FiniteReductionGrowth.hs` as its input domains. The public
`reduceEqConstraints` pass synchronized a binary root class to the exact
pairwise intersection. It also synchronized two disjoint root pairs and
propagated an empty child to every child. The next public pass was identical
in all three cases. The log is `/tmp/mcfta-fixed-pairs-source.log`.

## Projected paths do not satisfy the same one-pass invariant

Let `A` have two leaf rows with guards `Not Bottom` and `Or [Top]`. Let `B`
have one leaf row with guard `Not (Not Top)`. Let `wrap X` be one `f` edge
with child `X`. Start with child forest `[union [wrap A, wrap B], wrap A]`
and one binary class `{0.0, 1.0}`.

The public source operation makes two changes before reaching a fixed point.
The two projected leaf-row counts are initially `(3,2)`, then `(4,5)`, then
`(6,6)`. Thus even one class with prefix-disjoint paths does not immediately
synchronize its projections. Projection unions several child occurrences,
and the closed self-intersection shortcut prevents unrestricted distribution
of intersection over that union. This is a terminating boundary example,
not a fixed-schedule cycle or a source defect.

## Bounded search evidence

The temporary model retains Cartesian row intersection, guard-atom set union,
and the global closed self-intersection shortcut. The source seeded fold is
`foldr intersect first rest`; it is not an ordinary right fold seeded by the
last element. The distinction matters for classes with four or more paths.
The initial supplied diagnostic used the latter order. The reruns below use
the exact source seed and order.

A 45-second search checked 16,548 nested direct-root schedules with three or
four class members. Seven cases exceeded the structural-size bound. The
largest observed run had four changing passes. A second 45-second search
checked 2,239 congruence-closed overlapping schedules. Of these, 104 exceeded
the bound; the largest completed run had five changing passes. No cycle was
found. These searches are evidence, not termination proofs. They use uniform
finite shapes with every requested path present, so `requireAll` is inert.

The unresolved nested case still requires a fixed-schedule progress argument
for projection unions and overlapping ancestor/descendant classes. Finiteness
of a structural universe alone does not exclude repeated distinct states.
