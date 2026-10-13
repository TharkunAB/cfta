# Physical inventories for recursive coverage comparisons

Updated 2026-10-13.

The comparison bound now has a source-derived physical instance. It covers
a prepared cache fragment. It does not establish totality for arbitrary
open nested Mu reconstruction.

## Local pair bounds and source branches

`MergedComparisonInventory` replaces the old requirement to enumerate
every value of the ambient state type. Its inventory need contain only
the current comparison domain. The outgoing children remain in that
domain. `check_saturated` derives the bound `N * N` from the Cartesian
pair list, where `N` is the state inventory length.

`MergedComparisonSource.check` follows the source branch order in
`subsumes`: literal empty narrow operand, literal empty wide operand,
identity equality, ancestor-pair reuse, then edge comparison. It also
tests the child arity before the guard and child comparisons.
`inventory_terminates` constructs a finite comparison call tree. The
tree covers every child pair that the source can request. It covers
both possible answers. `check_saturated` supplies the numeric bound.
`source_to_rows` and `check_sound` retain the existing finite-term
coverage guarantee for every successful comparison.

The old row-only checker omits the two literal EmptyNode shortcuts.
It therefore does not reproduce every source result. For example, an
empty wide operand is rejected against a distinct node with no exposed
rows, even though both row languages are empty. `empty_wide_boundary`
checks this distinction. The original positive certificate theorems
remain valid.

## Derivation from actual source caches

`MergedPhysicalWarmup.Prepared` is a structural condition on actual
complete records. Each stored Mu body satisfies the existing
`PreparedWithoutMu` predicate. Preparation can traverse ordinary
constructors and unions. It stops at closed nested records. Thus the
fragment admits closed nested Mu records of arbitrary depth. Every
cache with depth-zero Mu bodies also satisfies this condition.

`warmup` executes the actual `InternedStoredSubstitution.unfold` once for
each value in the initial `nodeInventory`. `warmup_correct` proves that
this finite source schedule completes. It preserves source facts,
availability, and allocation history. It adds no Mu payload. Every Mu
in the resulting cache was therefore in the initial inventory.
`prepare` proves that all later Mu unfoldings replay one of these actual
results without allocation. No finite reachable inventory or successful
unfolding equation is assumed.

`MergedPhysicalComparison.inventory` combines the current complete
records, their immediate children, the actual warmup results, and the
current roots. It also includes EmptyNode. This finite list includes
primitive reference leaves without assuming that all reference names
form a finite type.

`successors_closed` proves closure under actual union operands and
completed stored-body unfoldings. `visited_exact` proves that the finite
epsilon reader visits precisely the reachable physical records.
`constructor_children` and `rows_closed` retain the original source
labels, guards, and ordered child records. `prepared_comparison`
derives the source checker's saturated pair bound for this physical
row view. `same_record` connects available record equality to canonical
source reference identity.

## Later merge allocations

`MergedPhysicalMergeContext.prepare_context` establishes the source
facts, available warmup results, and exact prepared unfoldings together.
`Context.makeEdge`, `Context.makeNode`, and `Context.makeUnion` preserve
these properties through the actual ordinary constructors. Their
returned edges or values retain residency or availability.

`Context.expose_exact`, `Context.compare_terminates`, and
`Context.compare_saturated` apply to new available roots in the current
cache. The roots need not have existed before the earlier merge effects.
Each query derives its inventory from that current cache. The proof
does not freeze the original list of comparison roots.

## Checked source obstruction and limits

`MergedPhysicalComparisonExample` constructs the closed unary
natural-number automaton from empty caches. The initial complete
records have identities 0 through 3. Its first actual unfolding creates
ordinary identity 4. `initial_inventory_incomplete` proves that this
new comparison state is absent from the initial record inventory.
The actual warmup completes at node counter 5 and establishes the
prepared comparison context. This refutes use of the initial cache
counter as an immediate reachable-state bound. It is not divergence.

The general source checker still needs the corresponding argument for
bodies that prepare open nested Mu records. The current result supplies
a reachable prepared cache and preserves it through ordinary effects.
It does not yet prove that a cold comparison with a different allocation
schedule has the same physical inventory. The row reader models the
closed source exposure used by `mergeAlternatives`; it does not certify
the error branches for unresolved references in open root unions.
Guard interpretation, concrete container behavior, and Haskell extraction
remain separate contracts.

This result does not establish convergence of repeated merge passes.
The ordinary merge call-height proof is a separate result.

## Validation

`MergedPhysicalLanguage.accepts_exact` connects the finite physical row reader
to the actual prepared epsilon graph. It preserves every accepted finite
term in both directions. `retained_union_exact` states the exact union law
for stored explicit unions. `comparison_sound` carries the source checker's
successful inclusion result to that physical graph language. Its guard
interpretation must make every recognized unconstrained edge true.
The preparation and concrete runtime correspondence boundaries above remain.

The focused Lean build passed 188 jobs. The isolated audit checked
8,052 theorem dependencies. It allowed only `propext`, `Classical.choice`,
and `Quot.sound`. The audit log is
`/tmp/mcfta-merged-physical-audit.log`.
