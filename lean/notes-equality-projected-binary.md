# Progress for one projected binary class

`EqualityFixedProjectionInvariant.post_first_expands` proves that each
original endpoint occurrence retains all its rows after the first
reciprocal binary edit. Projection takes the union of the occurrence rows.
Each edit keeps the complete-node identity shortcut. The Cartesian row
relation can reject pairs. Its required laws are commutativity and an
admitted diagonal for each row. The proof does not require associativity
or a strict rank for intersection with an arbitrary operand.

Suppose the second pass could remove a row produced by the first pass.
If the first peer projection contains that row, its diagonal pair retains
it. Otherwise, its original producing pair is absent from the peer edit.
This can happen only when the peer occurrence uses the whole-node shortcut.
Both producing rows then belong to the shared original projection. One
remains in the original occurrence. The other remains in the peer
projection. Their pair retains the produced row on the next pass.

`EqualityFixedProjectionTermination.run_bounded` counts missing pairs of
an occurrence index and a row in a finite complete inventory. Every
changing pass after the first pass decreases that count. The fixed-point
check finishes within the count after the first pass plus two checks.
The bound includes the initial pass and the final unchanged pass. Endpoint
rows can have children. The theorem does not assume that endpoints are
nullary or that their child intersection has an arbitrary-target rank.

The public source probe `/tmp/mcfta-projected-binary-progress.hs` uses the
single class `0.0 = 1.0`. Each endpoint has unary rows whose children have
distinct canonical residual guard rows. It retains each original
occurrence position and checks every replayed pass against
`reduceEqConstraints`. The endpoint row counts are:

```text
(0,[1],[1,2])
(1,[2],[1,2])
(2,[2],[2,2])
(3,[3],[2,2])
(4,[3],[2,3])
("fixed-point",4)
```

Every original occurrence retains its rows after pass one. The command
`nix-shell --run 'cabal exec -- runghc -package=microcfta /tmp/mcfta-projected-binary-progress.hs'`
passed. Its log is `/tmp/mcfta-projected-binary-progress.log`.

The theorem describes fixed occurrence groups. It is not yet a complete
physical-source termination theorem. A source adapter must derive the
static row relation and its finite inventory, and must preserve original
occurrences through canonical duplicate removal. Removing an empty
ancestor row can remove other endpoint occurrences. That event requires a
separate finite deletion phase. Raw initial guard syntax can also require
normalization before the diagonal law holds.

A class with three or more paths uses intersections of several peer
projections. This theorem does not cover that target fold. Different
classes can edit paths inside another class's endpoints. Source
normalization excludes strict-prefix pairs within one nontrivial class,
but it does not remove every prefix relation between different classes.
The general finite-DAG fixed schedule remains open.
