# Equal Cartesian closure does not supply a nested rank

A source reproduction on 2026-10-13 strengthens the arbitrary-operand
obstruction. Every operand in the two changing steps has the same recursive
Cartesian-closed image. Restricting arbitrary intersections to one such
image therefore does not produce a strict rank.

Use four distinct true residual guard atoms:

```haskell
[Not Bottom, Or [Top], Not (Not Top), Or [Not Bottom]]
```

Let `A` have one `a` leaf row for each atom. Let `B` contain those four rows
and a fifth row with the conjunction of the first two atoms. Set
`Z = intersect A B` and `W = intersect A Z`. The source row counts are
`4, 5, 12, 15`. `W` contains all fifteen nonempty conjunctions. Fully
Cartesian-closing any of `A`, `B`, `Z`, or `W` gives exactly `W`.

With `wrap X = Node [Edge "f" [X]]`, define:

```text
P = union [wrap A, wrap W]
R = union [wrap A, wrap B]
Q = wrap A
T = intersect P R
```

The source confirms `T /= P` and `intersect T Q == P`. Parent row counts
are `2, 3, 2`. Recursive Cartesian closure maps all of `P`, `R`, `Q`, and
`T` to the same one-row parent over `W`. All values have zero Mu depth and
no free references.

`EqualityFixedSaturationCounterexample` checks the finite four-atom row
algebra in the kernel. It retains the whole-node self shortcut at leaves
and unary parents. `same_closed_image` checks the shared closed image.
`no_fiber_rank` proves that no natural rank can strictly decrease on every
changing arbitrary intersection within this image. This is a concrete
algebraic model. The separate public Haskell run verifies the corresponding
source node identities; it is not an assumed model-to-source theorem.

The temporary public probe is `/tmp/mcfta-saturation-fiber.hs`. Its Nix log
is `/tmp/mcfta-saturation-fiber-source.log`. The logged results are:

```text
("leaf-row-counts",[4,5,12,15])
("leaf-saturations-equal",True)
("parent-saturations-equal",True)
("within-saturation-cycle",True,True,[2,3,2])
("ordinary-closed",True,True)
```

The two target operands differ. No fixed equality-schedule cycle follows
from this example. A general proof must use the simultaneous changes to
all peer projections, not only finite height, equal Cartesian closure, or
an arbitrary-target rank inside one closed-image class.
