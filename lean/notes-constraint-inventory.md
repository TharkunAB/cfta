# A fixed finite inventory for recursive source constraints

Proof: `3ef4f2e1`. Source: `TharkunAB/cfta`, `origin/main` at `33148e6d`.
Continue on `formalize` and push checkpoints. This note follows
[recursive constraint origins](notes-recursive-constraint-origins.md).

## Original equality geometry through actual normalization

SourceEqualityConstraintGeometry.Region records active classes, bounded
segments between recorded path prefixes, one original anchor in each
component, and a fixed child-index alphabet. Actual concatenation,
component completion, each congruence step, and the source fixed-point
normalizer preserve this geometry.

Cached operands supply active classes and canonical path lists. Input
preparation therefore leaves these classes unchanged. The source array
normalizer equation connects the actual array schedule to the proved
reference steps. Every successful source conjunction returns the original
geometry, a canonical normal state, and a contradiction-free class list.
No finite output-domain premise is supplied.

## Explicit finite physical equality and guard inventories

SourceEqualityConstraintPathInventory.inputs reads every physical equality
class occurrence from the original literal constraints. anchors retains all
their path occurrences. gap uses the original path budget. alphabet contains
only child indices in those paths. The fixed path domain is

```text
words alphabet (gap * (anchors.length + 1))
```

Every normalized component has an original anchor. Distinct components use
distinct anchors. Bounded path segments therefore give the displayed path
length bound. Canonical classes have no repeated paths. Each class has at
most domain.length paths, and there are at most anchors.length classes.
Explicit bounded lists contain every generated physical equality payload.
The inventory also retains unchanged original payloads and contradiction.
Actual normalization can create paths absent from the original literal
list. The word domain includes those paths.

SourceEqualityConstraintGuardInventory retains original guard fields,
including noncanonical fields. The actual conjunction flattens outer And
nodes, removes Top and duplicates, and sorts the retained atoms. Every
atom comes from an original literal. Canonical conjunctions over every
selection of the original atoms form a concrete finite guard list.

Both inventories use actual source normalization and structural guard order.
They are conservative proof inventories. No practical enumeration cost or
tight cardinality bound is claimed.

## Complete physical constraints and recursive public entry

SourceEqualityConstraintInventory.inventory is the explicit finite product
of these two field inventories. derived_mem_inventory proves membership for
every literal, Top, and actual conjunction-derived constraint. It requires
only that the original physical equality fields are cached source payloads.
own_mem_inventory gives the finite image of the actual own-payload accessor,
including its failures. This does not bound arbitrary inherited payloads.

Original syntax annotation checks imply checks for every literal in the
inventory, including discarded alternatives and raw and smart binder bodies.
closed derives the original constructor result, recursive Scope, closed
availability, and initial physical inventory membership. Every checked
successful public return then has physical inventory membership throughout
the constructor heap and annotation membership throughout the returned value.
Both actual source gate memo receipts, physical histories, exact public
language, and stable replay of the identical value and full native state
remain proved.

Actual success and reached native checks remain explicit. A finite constraint
inventory does not imply finite node construction, a finite caller-state
inventory, or caller termination. No decreasing node measure is proved here.
The retained ordinary-height counterexample remains valid.

## Validation and next target

All four modules pass focused builds. The aggregate audit passes 1,888 jobs
and 48,536 dependency checks. Only propext, Classical.choice, and Quot.sound
are permitted. The older unused inputs warning remains. Log:
`/tmp/mcfta-constraint-inventory-20261015-audit.log`.

No production Haskell or retained reproduction changed. Earlier focused
height, Fourmolu, three Cabal formatting, 650-example, benchmark-build, and
metadata checks were not repeated. Older proof bytes except audit imports,
counterexamples, marked drafts, stashes, and other worktrees remain unchanged.
The upstream HTTPS pull succeeded. Main is unchanged. The current read-only
HTTP board search could not connect. No board post was made.

Next inspect actual narrowed-child node origins. Test whether original node
occurrences and the proved finite constraint inventory can bound actual
constructor outputs. Prove that bound or retain a focused counterexample
before using it in a rank. Include physical combination and descent of
inherited payloads. A valid termination argument must cover constrained
bodies below ordinary endpoints, native intersections, Mu cleanup, and
actual returned warm states. Do not assume a future finite node inventory,
decreasing height, caller graph, or successful receipt to prove existence.

General constrained caller termination, the outer reduction memo table,
open contexts, repeated fixed points, getAllAtPath, native containers,
GHC scheduling, and extraction remain open. Preserve Sized exact classes,
finite size execution, size order, both distinct rank inverses, the optimized
interned core, and older constructor and equality proofs.
