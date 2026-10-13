# Ordered physical comparison checkpoint

The ordered comparator now has sufficient-fuel completion and exact
successful-result stability. No stable module contains a partial proof
or an admitted theorem.

## Current implementation and proofs

`MergedSourceComparison.check` implements the source comparison with
explicit cache state and proof fuel. It checks narrow empty, wide empty,
tagged identity equality, and numeric ancestor pairs in that order. It
reads the narrow rows first. Each demanded narrow row reads the wide
rows, tries covers in order, and compares matching child lists from left
to right. Failed covers retain their completed cache effects. Boolean
short circuits retain the exact cache at that point.

The header requires equal symbols, equal child-list lengths, and a clear
wide guard. The `clear : Guard → Bool` parameter represents the source
`noConstraint` test. Primitive unresolved identities and reader failures
remain explicit. The intended comparison domain is available closed
roots. Open callers have no correspondence claim here.

`MergedComparisonFacts.check_verified` proves that every fuelled run on
available closed inputs preserves source `Facts`, both cache histories,
and `NoNewMu`. It also derives `Progress`: the cache is unchanged, or the
run makes one previously cold Mu from the earlier cache warm. Supporting
theorems cover the ordered child, cover, row, and reader stages. Successful
reads supply resident edges and closed children at any successful fuel
bound.

`MergedComparisonWarmProgress.Warm state value` means that actual stored
unfolding returns a result with exactly the same state. `Warm.grows`
preserves this property under later cache growth. `collect_progress` and
`nodeEdges_progress` prove that a reader which changes its cache warms a
previously cold Mu already available before the read.

`MergedComparisonColdMeasure` fixes the original complete-record list.
`CoversMu` states that every currently available Mu occurs in that list.
`covers_initial` derives it from the actual initial issued inventory.
`CoversMu.preserve` retains it through effects that add no Mu.
`coldCount_le` proves monotonicity under cache growth. `progress_lt`
proves a strict decrease whenever a verified effect changes the cache.
`reader_progress` applies that decrease to the exact physical reader.

`MergedComparisonReaderReplay.nodeEdges_replay` proves that an actual
completed read returns the same exact edge list without allocation in
any later cache extending its actual final cache. It uses original
`Facts`, `Prepared`, and availability. It requires neither closedness nor
an eager warmup. `collect_replay` and `canonical_replay` expose the same
result for the closure reader. These proofs compare only one actual
allocation history and its later extensions.

## Derived completion and fuel independence

`MergedComparisonCompletion.check_complete` proves that all sufficiently
large bounds return the same Boolean and exact final cache. It derives
the initial Mu inventory from the actual source cache. It requires source
`Facts`, `Prepared`, and available closed operands. It has no recursive
termination premise. The proof uses the lexicographic pair:

1. `coldCount originals state`.
2. The number of issued numeric identity pairs outside the ancestor list.

Every completed reader or earlier sibling comparison preserves the fixed
Mu domain. A changed cache decreases the first measure. An unchanged
cache and a fresh ancestor pair decrease the second. `identity_closed`
derives pair membership from actual source residency and the issued
counter. Finite ordered child, cover, and row traversals combine stable
bounds along the actual execution. Failed covers retain their cache
effects. No eager preparation replaces the original execution cache.

`MergedComparisonStability.check_stable` independently proves that extra
fuel preserves any successful Boolean and cache, without source invariant
premises. `successful_results_eq` compares any two successful bounds.

## Actual-cache semantic inclusion

`MergedComparisonSoundness.check_sound` now derives finite-term inclusion
from a successful true comparison in its actual returned cache. It needs
no `Ready`, warmup, recursive callback law, or coinduction premise. Source
facts, preparation, available closed operands, and a sound interpretation
of the clear-guard test remain explicit. A finite-term height induction
justifies numeric ancestor reuse through coherent record identity.

`MergedSourceSelectionSemantics.select_complete_exact` composes the theorem
through the actual ordered cold child filter. It proves stable completion
and exact union-language preservation in the actual returned cache. The
next composition is the complete cold merge worker. General Mu totality
and repeated merge-pass convergence remain separate obligations.

## Scope and validation

`Prepared` still requires every complete Mu body to satisfy
`PreparedWithoutMu`. It permits closed nested Mu records of arbitrary
depth and excludes preparation through open nested Mu records.

The pinned Lean 4.34.1 build checks `MergedComparisonFacts` and
`MergedComparisonReaderReplay` together. The isolated axiom audit permits
only `propext`, `Classical.choice`, and `Quot.sound`.
The log is `/tmp/mcfta-source-comparator-handoff.log`.
