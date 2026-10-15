# Main 525d722e: waiting counts by representative

Current source main is `525d722eefb722be27def2d965b75f56c7a08bdf`.
The preserving merge is `c12a0420`. The prior checkpoint is `eb3f6d07`.
Backup: `backup/formalize-before-main-525d722e-20261015-1809`.
The source delta changes Enumeration, Internal.UnionFind, and the changelog.
No Lean definition changes. All prior proofs remain valid for their models.

## Current source contract

The waiting map now counts suspended constraint occurrences by their current
union-find representative. It has no non-root keys. Zero counts have no entry.
The required invariant at an operation boundary is:

```text
waiting[r] = number of suspended occurrences in current unenumerated slots
             whose referenced UVar has current root r
```

`writeUVarValue` updates only supplied gained and lost constraints. It reads
each referenced root without changing the union-find. `setUVarValue` supplies
the complete new and old constraint lists. A node merge supplies only incoming
constraints. After union, distinct old representatives move their counts to
the final representative. The final representative is excluded from the move.

The two assimilation writes keep the map unchanged. The target first gains
the source constraints. The source slot is then eliminated. Their combined
effect retains the global occurrence multiset. The count invariant does not
hold between those two writes. It can also be temporarily stale after union
and before count relocation. Prove these compound operations at their endpoints.

`findExpandableUVars` removes waiting-map keys from the candidate set without
representative lookups or path compression. Its intended candidate order and
three outcomes are unchanged: no candidates, all blocked, or available choices.
The returned union-find can differ from the earlier compressed state.

`UnionFind.root` returns the same representative as find on a finite valid
forest. It performs no compression or insertion of an absent singleton root.
Invalid cyclic forests are outside that termination claim.

## Remaining proof transfer

`EnumerationWaitingIndex.Correct` counts raw referenced variables. The older
write and reachability models recompute full replacements. The earlier
indexed selector resolves raw waiting keys with stateful representative reads.
Those proofs are not literal models of the new physical waiting map.

Derive representative-aggregated counts, pure-root adequacy, gained/lost
delta effects, distinct-root rekeying, and current scheduler equivalence.
Reuse the existing occurrence and assimilation multiset lemmas. Relate old
and new forests by their classes rather than assume identical storage.
Frame rules need preserved roots or explicit rekeying.

The machine-count proofs need a new class-sum and rekey bridge. Earlier
bounds were per raw key. Derive class-total bounds from actual occurrences.
`insertWith (+)` does not remove an entry if a machine sum wraps to zero.
Do not claim positive exact counts without the required range proof.

Review found no valid-state algorithm defect. This is source inspection,
not proof of the new invariant. The changelog's performance measurements
were not repeated.

## Other proof scope

The declaration and body of provablyEmpty are byte-identical to 54f4c272.
The [captured-task target](notes-source-emptiness-tasks.md) therefore remains:
immutable body receipts, saved common-subtree semantics, actual accepted-row
requirements, progressive lazy demand, checked native transfer, and completion.
The [template exclusion obligations](notes-main-54f4c272.md) also remain.
Keep the complete library scope, optimized interned core, older targets,
all counterexamples, and the separate Sized contracts.

## Validation

The repository-required strict Nix build and all six suites pass 704
examples plus golden checks. Fourmolu passes both changed Haskell files.

All Lean source files remain byte-identical. Their previous pinned audit
passed 2,014 jobs and 51,484 dependency checks with permitted axioms only.
It was not repeated. The separate Sized probes and active-package Cabal
formatting checks were not repeated because those files are unchanged.
The earlier checks passed. Production definitions match main. Only the
retained constructor changelog entry and caller-repro comment differ in
the package trees. All repros, drafts, stashes, and other worktrees remain.
