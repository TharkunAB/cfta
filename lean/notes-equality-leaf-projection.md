# Fixed equality schedules with projected leaf endpoints

The `EqualityLeafProjection*` modules extend the finite leaf progress proof
to arbitrary ancestor depth. Each selected path must end in a leaf domain
at every existing occurrence. A path can project through several ancestor
alternatives. The source can merge their canonical identities.

The representation retains separate original occurrences. An ancestor edge
stores its unchanged tag and ordered children. The tag can contain the
source symbol, equality field, and residual guard. A leaf stores its complete
set of canonical residual alternatives at each symbol. Edits do not add an
ancestor edge. Required-path filtering can remove an edge. An explicit empty
root represents global empty propagation, including an unselected root.

## Checked result

`EqualityLeafProjectionSyntax` defines this finite representation, the exact
child-position edits, and the required-path filter. `requireEdges` checks
all required immediate indices before it maps the surviving child lists.
A missing child inside an ancestor alternative removes that alternative.
A missing root index has no child to edit, as in the source list operation.

`EqualityLeafProjectionProgress` proves that every arbitrary leaf target
improves the occurrence weight. The leaf weight is the sum of the existing
finite residual potential over all symbols. Each ancestor and edge adds a
positive unit. Removing a row therefore decreases weight even when every
leaf below it already has minimum potential. The proof retains the global
source self-intersection shortcut from `FiniteLeafSymbolsProgress`.

`EqualityLeafProjectionInvariant` proves that all original selected endpoints
remain leaf domains after edits, required-path filtering, and root erasure.
No synchronization of the projected domains is assumed.

`EqualityLeafProjectionLowering` derives edit and required-path correspondence
by mutual induction over occurrence trees, edges, and ordered children.
The source constructor may remove duplicate and dead supplied rows. Lowering
keeps these rows in the request and uses the canonical constructor result.
The assumptions are six local constructor equations, not a whole-pass or
whole-schedule commutation premise. The equations must hold for requests
that contain duplicate and dead rows. `InternedNodeSetCongruence` supplies
physical constructor results for those two normalization cases; connecting
the later runtime proof below derives the complete physical worker connection.

`EqualityLeafProjectionSchedule` computes every class target from the same
input forest. Its target intersection keeps the first operand as the seed
of the source right fold. The complete pass preserves the source order:
empty-constraint shortcut, contradiction, required-path filtering,
right-fold class edits, and forest-wide empty propagation. It derives exact
complete-pass lowering from the local constructor equations and the endpoint
invariant.

`EqualityLeafProjectionTermination.source_terminates` uses the source identity
test on the lowered forest. A changing source pass must change the occurrence
representation, even when lowering merges different occurrences. Each such
pass strictly decreases the natural weight. The theorem derives a fixed
point within the initial occurrence weight plus one passes.
`source_guard_terminates` supplies the row algebra and finite inventory from
the actual source guard normalizer. It does not assume a finite bound.

`EqualityLeafProjectionReads` derives the leaf representation of actual path
projections. It excludes dead ancestor alternatives before it projects a
child. This order matters: an edge with an empty second child can have a
nonempty first child, but the source constructor removes the whole edge.
The module derives the complete simultaneous target list from local source
read, union, and leaf-intersection equations. Nonempty selected paths and
a decoder for represented leaf nodes connect the target list to source
indexed forest reads. Duplicate contributions are handled by the source
union equation rather than by occurrence identity.

## Source checks

The focused temporary probe `/tmp/mcfta-projected-leaf-occurrences.hs` compares
the occurrence implementation with public `reduceEqConstraints` on 4,096
forests. Each ancestor request includes duplicate rows, a dead row with a
nonempty selected child, and a row with a missing required child. Every pass
agrees exactly after lowering. Every changing source pass decreases the
occurrence weight and stays within the derived bound. The largest case
needs four changing passes. Separate cases check paths through two ancestor
levels and global erasure of a root outside the selected class.

The probe ran inside the repository Nix environment. Its log is
`/tmp/mcfta-projected-leaf-occurrences.log`. These are focused source checks,
not a proof that every physical source operation satisfies the adapter laws.

## Boundary

The result covers fixed selected classes on finite ordinary ancestor trees
whose endpoints are leaf domains. Canonical parent merging and leaf-row
growth are included. The original abstract theorem keeps local constructor
and read equations explicit. The later physical runtime development derives
them from actual finite constructor and worker runs, then removes temporary
proof allocations by raw leaf pullback and occurrence trimming. It reaches
an allocation-free physical fixed point within the same initial potential
plus one. See [the runtime bound](notes-equality-leaf-runtime-bound.md).
Node identity injectivity is not assumed for occurrence representations.

The proof does not cover intersection at an ancestor endpoint with nested
children. Such an intersection can create Cartesian ancestor alternatives.
The known alternating-operand nested cycle is outside this fragment. The
proof also does not cover changing class eligibility through recursive
unfolding or repeated recursive child passes. It bounds the number of source
passes, not the cost of a pass or total cache allocation.
