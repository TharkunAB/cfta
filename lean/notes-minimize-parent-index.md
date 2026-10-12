# Indexed minimization schedule

`MinimizeParentIndex` models the parent-index optimization merged in
`microcfta` at `bbeb7be`. It composes that optimization with the existing
guard checks and accepted-root repair. The source is
`Data.CFTA.Refinement.Minimize`.

## Ordered copies

The old worker deduplicates the original rows followed by every redirected
copy. The new worker retains the original rows, copies only transitions
that contain the replaced child, removes copies already present, and
deduplicates the remaining copies. `copy_exact` proves exact ordered list
equality when the original row is distinct. This is stronger than term-set
or membership equality.

`copy_distinct` derives distinctness of the resulting row. The source initial
view has distinct rows because ordinary nodes and exposed union rows use
sets of interned edges. The concrete interned-to-transition conversion
remains the representation connection for this initial property.

## Parent metadata

`initialParents_complete` derives the index from every actual child link.
The invariant requires every real parent to occur in the index. It permits
stale entries after deletion. Stale entries can cause extra work but cannot
drop a copy.

`adjust_fold` connects the source fold of map adjustments to a conditional
table traversal. `indexedCopy_exact` proves that a complete distinct parent
set gives exactly the old full-table copy result, including row order.
No whole-rewrite correctness premise replaces this derivation.

A successful step adds affected parents to the destination child's index.
The accepted-root repair can also install a representative with new children
at the root. Those children need the root in their parent sets. The rebase
resolution updates these entries as well. `rewrite_complete` derives the
complete updated index for both sources of new links.

The kernel example `insertion_requires_parent_update` demonstrates the
missing link in a table rewrite that updates only the destination. The next
copy then misses a root alternative. `inserted_parent_update_restores_copy`
checks the repaired metadata. This is a structural integration example. It
does not claim that a public minimization call reaches that exact schedule.

## Complete schedule

`step_exact` preserves all six source skip conditions. It proves equality of
the row table, applied redirects, and installed-root ledger. `step_valid`
preserves parent completeness, distinct parent keys, and distinct rows.
`schedule_exact` composes these results through every finite replacement
schedule from the actual initialized parent index.

`copyFold_exact` also proves the repeated copy worker used by final
representative checks. `representativeCopies_exact` starts at the source's
singleton representative and derives the same complete ordered list.
`finish_exact` transports the unchanged final checks through the schedule
equality. Together these results preserve the existing accepted-root theorem
and the source fallback/error behavior.

This optimization preserves the representative-selection algorithm. That
algorithm deliberately removes some distinct terms. It does not acquire an
exact-language preservation contract from this proof.

## Validation and boundary

The pinned Lean build passes. The aggregate audit checks all theorem
dependencies. Independent finite checks compared 94,560 small rewrites and
77,248 chained rewrites against the full-table algorithm. All comparisons
retained exact ordered rows and checked parent completeness after each step.
Those temporary checks supplement the general proof.

After the rebase, all 618 Haskell examples passed in Nix: 282 core,
194 generator, and 142 refinement examples. Source formatting also passed.
Physical map/set operations, interned view conversion, and solver effects
retain their existing representation contracts. The proof does not claim
a wall-clock bound for map operations or for guard checks.
