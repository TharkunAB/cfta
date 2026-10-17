# Ordered actual source natural runs

`SourceListSortRunsOrdered.sequences_ordered` follows the actual source run detector.
It requires a transitive relation and a comparison choice that orders the selected pair.
It does not require antisymmetry, unique input values, or an already sorted input.

The descending branch keeps an ordered reversed accumulator.
The ascending branch keeps an exact function-accumulator prefix and an ordered prefix plus last element.
The proof follows both stopping branches and the subsequent actual run detector.
It uses the literal `SourceListSort.sequences`, `descending`, and `ascending` definitions.
It does not replace the source schedule with a different sorter.

The constructed integration reads five actual runs from one finite input.
It includes a descending run, an ascending run, equal values, another descending run, and a final singleton.
It proves their literal source order and invokes the generic theorem for every produced run.

Strict attempts 1 and 2 are retained with their diagnostics.
Strict attempt 3 is the selected empty-log source check.
The canonical target, full public proof and axiom probe, and constructed proof and axiom probe all pass.
All jobs record actual 4 GiB MemoryMax, 4 GiB MemoryHigh, and zero swap.
This component proves run ordering only. Full sort ordering is a separate module.
