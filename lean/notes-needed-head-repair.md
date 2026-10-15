# Required-path trie meaning and retained-cycle repair

Updated: 2026-10-15 02:37 CEST.
Proofs: `06353eab` and `31868723`. Source repair: `61f2c939`.
Upstream: `TharkunAB/cfta`, `origin/main` at `f201deda`.

## Actual Needed construction

`SourceEqualityNeededMap` models ascending entries of the source `IntMap`.
Keys are signed integers. The alter worker inserts before a larger key,
replaces the selected value, or continues in the remaining entries. Its
lookup theorem changes exactly one key. Its order and child-property
theorems retain the finite-map invariants. Native Patricia-tree storage and
machine integer arithmetic remain outside this representation theorem.

`SourceEqualityNeeded` copies `insertNeeded` and the source right fold.
Unlike the equality-class trie, this trie permits paths and their extensions
in one input. Empty paths add no requirement. Insertion retains exactly the
old demanded paths and the prefixes of the inserted path. The complete fold
therefore retains the exact prefix closure of its input, including duplicates.
The greatest-key theorem gives exactly the source signed arity comparison.

`SourceEqualityNeededMeaning.Matches` is an independent finite-term relation.
Every stored child must exist and satisfy its child trie. Signed subtree lookup
has the same negative-index behavior as the source term lookup. `build_exact`
proves that the actual trie construction means existence of every original
complete path. `insert_exact` conjoins one complete requirement. Empty,
duplicate, and prefix inputs need no antichain premise. `matching_row_fits`
proves that the source maximum-key row test rejects no matching finite term.
Equal input path sets have equal term meanings, without an insertion-order
premise.

The maximum-key test alone does not prove that every key is valid. A raw
negative key passes that test at zero arity. Independent signed lookup has no
matching subtree at that key. Both facts are checked in Lean. The existing
equality smart constructor rejects negative paths before positive normalized
classes reach the worker. Retain that normalization premise in the caller
proof. Do not replace signed keys by natural keys without an adapter theorem.

## Ordered source child adjustments

`SourceEqualityNeededAdjust` copies the source right fold over ascending child
entries. The natural child adjustment has the exact split-and-rebuild source
equation. Signed lookup shows that each selected position receives exactly its
own callback. The original child count stays fixed. Missing and negative
positions leave the list unchanged. Lookup uses the original input value;
unique keys exclude repeated updates at one position.

`SourceEqualityNeededAdjustMeaning` composes explicit per-node callback
contracts. `apply_exact` says that the resulting forest contains exactly the
original forest terms that satisfy each requirement at each existing selected
position. `checked_row_exact` uses the actual greatest-key row test and
normalized nonnegative keys. The original forest supplies term-list length.
These facts derive all selected child positions. No additional term-arity
premise or whole-list operation law is supplied.

The node callback contract remains explicit. It must be derived from the
actual recursive source worker before applying this theorem to the complete
required-path pass. The returned-list proof retains the source fold structure.
It does not establish the native lazy evaluation order of constructor effects.
Do not infer that a right fold evaluates all callbacks from right to left.

## Source repair

The previous checkpoint retained the actual raw self-binder stutter and a
two-second Haskell timeout. Those files remain unchanged:
`SourceClosedSelfRequireBoundary.lean` and `repro/RawClosedSelfRequire.hs`.
The old repro expects the old failure. On repaired source, it reports an
unexpected completed reduction. This is expected. Use the current regression
for a passing repair check.

`SourceClosedSelfHeadRepair.actual_head` checks the actual repaired source
construction and cold worklist. Two worklist steps return no constructor rows
for the raw self binder. The subsequent actual `makeNode []` request returns
empty with the same cache. `syntax_empty` proves that the independent source
least language has no finite term. `actual_language` uses the existing closed
construction correspondence to identify the actual binder with empty at that
independent meaning. The original stutter theorem remains valid for unfolding
alone. The path worker now uses a different operation.

The repair replaces same-path Mu unfolding by `Node (nodeEdges node)` in
`requireAll`, `editAll`, `getPath`, `getAllAtPath`, `modifyAtPath`, `requirePath`,
`nodeMapChildren`, and template `restrict`. The existing union branches already
use this operation. The ordinary fast path of `nodeEdges` remains. It returns
the edges of the first ordinary unfolding directly. Recursive epsilon fallback
retains its visited identities and edge deduplication. Root-path and unrestricted
template branches still return before traversal. Direct unresolved-reference
errors remain explicit.

General closed reader completion and exact physical graph readback already
exist in `MergedFreshOrdinaryColdTermination.read_closed` and
`MergedFreshOrdinaryExposureLanguage.actual_exact`. Reuse those theorems when
building the new path-worker graph. They are not a supplied whole-reader law.
The new self-binder fixture is a checked repair example. It is not a proof of
the complete new native path worker.

## Validation and preservation

The aggregate audit passes 1,623 jobs and checks 45,488 theorem dependencies.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. Only the old unused
`inputs` warning remains. Log:
`/tmp/mcfta-needed-adjust-20261015-audit.log`.

All three Haskell suites pass in the project Nix shell: 289 core, 209 generator,
and 147 refinement examples. The existing retained-cycle test now also checks
projection, child mapping, modification, required paths, template matching,
and reduction of two raw empty cycles. The focused retained tests pass after
removing a redundant import. Fourmolu and cabal-gild checks pass. Logs:
`/tmp/mcfta-raw-cycle-paths-20261015-tests.log`,
`/tmp/mcfta-raw-cycle-paths-20261015-focused.log`, and
`/tmp/mcfta-raw-cycle-paths-20261015-format.log`.

The Nix linker initially could not find `libgmp`. The documented
`export PATH=/usr/bin:$PATH` inside `nix-shell` resolved that setup error.
An initial multiword Hspec filter was rejected. The single-word retained
filter passed. Neither setup error is a failing semantic regression.

Snapshot: `/tmp/mcfta-needed-adjust-checkpoint-20261015-0237/`.
It retains 2,014 Lean-tree files and the four root documents. The preservation
report checks all older proof bytes except the added audit imports. It checks
all counterexamples, repros, and marked drafts. It also checks stashes and
other worktrees. The repaired production files and validation logs are copied
beside that snapshot.

## Next proof

Derive the repaired physical `requireNode` callback. The trie compiler,
independent term meaning, ordered child adjustments, and conditional forest
composition are complete. Use `checked_row_exact` after deriving the actual
callback contract. The ordinary-node maximum-key rejection must occur
before child recursion. Empty maps must return the original source value.
Missing list positions must keep the source list behavior.

Use constructor-row exposure for both Mu and stored union cases. Retain actual
row-node construction, edge reconstruction, canonical cache hits, returned
caches, and explicit errors. Derive finite execution from finite Needed depth
and complete closed exposure. Connect the actual output language to the
existing trie `Matches` relation and the one-pass required-path law. Then carry
the corresponding actual edit worker into narrowing. Do not claim the full
pass from the current self-cycle fixture or from the maximum-key check alone.
Repeated fixed-point reduction, native containers, lazy scheduling, and
verified Haskell extraction remain separate.

The [Lava note](notes-lava.md) records the function/graph method and the paper's
limits. Its non-structural recursion exclusion supplies no termination proof
for these workers. Keep Lean, the optimized interned core, the exact Sized
sequence, and both distinct-term inverse laws. Preserve the completed unary
ancestor theorem and all marked drafts. Stop all work and workers at 1% weekly
allowance or less.
