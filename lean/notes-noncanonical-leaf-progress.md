# Progress from raw initial leaf guards

Initial source guards need not have canonical outer syntax. A node can keep
`And [Top, Top]` as a residual. Self-intersection returns the same node,
including that syntax. A Cartesian intersection uses `conjoinConstraints`
and canonicalizes the output guard. The progress proof retains both branches.

Constructor admission also matters. `And [Bottom]` is not literal Bottom,
so a nullary edge can retain it. Its self-intersection keeps that row.
Intersecting it with Top normalizes the guard to Bottom and removes the
edge. The source comparison in `/tmp/mcfta-raw-leaf-normalization.hs`
checks these cases and all 1,156 pairs of 34 retained raw guards. All pass
in `/tmp/mcfta-raw-leaf-normalization.log`. This is finite source evidence.

`FiniteFilteredRowProgress` extends the finite row measure to Cartesian
products followed by a constructor admission predicate. The operand being
narrowed must already pass admission. The other operand can contain a row
whose separate constructor would reject it. An unchanged upward closure
still retains every old row because each old row passes admission. Thus a
changed filtered product strictly decreases the finite measure.

`NoncanonicalLeafProgress` adds one normalization phase above the bounded
canonical potential. Every Cartesian output is canonical and admitted.
An initial raw node therefore decreases its phase on the first changing
intersection. A canonical node uses the filtered row measure. The source
whole-node identity shortcut preserves its input exactly. A derived natural
rank covers both cases, including all constructor symbols together.

`SourceNoncanonicalLeafProgress` instantiates the argument with the actual
structural guard order, outer conjunction, and source equality arity check.
The raw row carrier requires only that atoms come from the original finite
inventory. It does not require normalized initial guards. `rawJoin_exact`
derives the canonical factor operation from actual source conjunction.
`product_exact` retains literal Bottom and positive-equality rejection.
`intersect_strict` and `leaf_progress` derive strict progress from the source
operations and generated canonical inventory, without a supplied row law
or finiteness bound.

`projected_terminates` lifts this result through the retained ancestor
occurrence tree. It still requires the existing local constructor
correspondence laws. It does not assume that one finite cache contains all
possible future constructor requests. Actual stateful pass composition must
derive its finite completed-request correspondence. The current physical
leaf product and union modules separately cover canonical admitted inputs.
