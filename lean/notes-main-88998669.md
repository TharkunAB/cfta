# Main 88998669: endpoint queries, merge pruning, and subtree exclusion

Source main is `889986690d63c63734fa4c6ba19fd6886b2d1ff6`.
The preserving merge is `6d1462c7`, with prior proof parent `6e5743d1`.
Proof checkpoints are `a9eea20e`, `86f70026`, and `60c96c89`.
Full library scope stays active. Keep the optimized interned core, older
proofs and counterexamples, and all separate exact Sized contracts.

## Source changes

The upstream delta changes eight existing files. It adds no source module.
The primary equality gate is unchanged. At an exact closed constrained Mu
endpoint, the secondary gate now returns false. Interior paths and open
constrained Mu values still return true. The branch reads unconstrained
before it returns. It does not call reachesConstrainedMu or unfoldOuterRec.

Enumeration now exports reachesConstrainedMu. Its body moved from Equality
without a semantic change. The original root computes _constrainedRecursion.
Two present unenumerated nodes form an intersection. If the flag is true,
the intersection reaches a constrained Mu, and provablyEmpty returns true,
the result becomes EmptyNode. Missing nodes skip that check. Suspended
constraints retain left-to-right concatenation.

provablyEmpty now has a separate memo. Its uncached body tests the original
free list before exploration. Open inputs return false. Exploration tests
openness before key membership. A row requirement with free references is
optimistically possible even when its key occurs in the table.

Template adds matchesNowhere, excludeAnywhere, excludeAnywhereFTA, and
preorderPrefix. The exclusion construction passes the forbidden templates
to each child. Interned adds fromRows, and fromFTA delegates to it.
fromRows keeps the existing SCC/binder reconstruction and accepts transition
rows without a consistent symbol arity. excludeAnywhere rejects free inputs
and uses obligationRows followed by fromRows.

## Checked endpoint transfer

SourceCurrentMuEndpoint defines the current two-mode worker. Its primary
node, forest, and class equations retain the entire earlier Outcome and
constructor heap at every fuel. The new secondary endpoint, constrained
interior, and constrained open laws are exact.

SourceCurrentMuEndpointMemos records the actual predicate call at a closed
Mu endpoint. It derives returned validity and retained entries for all three
gate tables. No descendant or unfolding call occurs in this branch.
The current primary class reuses the earlier exact completed receipts.

SourceCurrentMuEndpointQuery derives ForestClosed from actual selected
closed endpoints. A class starting at a closed constrained Mu is refused by
the primary gate and admitted by the secondary gate. An actual seeded query
and current uncached Decision true refute that original active class.
This covers one-index paths to closed ordinary/Mu endpoints. Unrelated
original siblings may stay open.

The old disabled-mode equality with the free worker is historical. The
earlier secondary-dependent projection and reached-Scan correspondence do
not cover the new rule automatically. Their mathematical theorems remain.
A general current secondary trace and its effects still need transfer.

## Checked emptiness and merge transfer

SourceCurrentEmptinessTable follows the new skip order and canAccept.
Actual completed task rows derive closure of every stored requirement.
That fact derives exact compatibility of current step/grow with the earlier
proved table algorithm. This is completed-record compatibility. It does
not establish equivalence of GHC field or key demand.

SourceCurrentEmptinessDecision models the initial free-list guard. A true
body result derives input closedness and sound exclusion. The literal
current grow receipt constructs the closed known-key branch through the
derived table compatibility. Completed exploration remains explicit.

SourceCurrentEmptinessMemo is a fourth completed memo family. Hits retain
the full native state. Misses execute an actual current Decision. Empty
initial state and actual misses derive conservative answers, coherence,
and retention of earlier entries. Exact runtime Boolean replay, pending
publication, and concurrent ownership remain open.

SourceCurrentEmptinessMerge retains source slot errors, missing-node cases,
and suspended constraints. Its ordered Check graph tests the flag, reaches,
and the fourth memo. Check.exact derives language preservation for the
pruning result from an actual memo call. The reaches guard is still a pure
read here. Shared predicate/descendant memo updates are not threaded through
this graph. The source initializer flag, both native merge sites, UVar
storage, waiting indexes, and full enumerator execution remain to compose.

## Checked template predicate and remaining API work

SourceTemplateAnywhere follows matchesNone and matchesNowhere. It proves
the literal root-and-children equation and exact absence at every existing
subterm path. Selected subterms retain the predicate. A forbidden Hole
rejects every complete term.

This does not prove the exclusion construction. Complete disjoint edgeCopies
partition, canonical obligation normalization, finite reachable closure,
cyclic FTA language, unambiguity, and interned fromRows/SCC transfer remain
open. preorderPrefix still needs its valid-input and exact matching laws.
The earlier root-exclusion obligations remain part of this work.

## Next proof target

Lift the complete current secondary trace, including the new closed Mu
endpoint, to actual effects, supported projection, and all gate memo calls.
Then compose Fold/Seeded, delayed Force/Expose/Run/Decision, the fourth memo
lookup, and the current reached Scan. Preserve anchored support without
closing unrelated original children. Connect concrete caller entry and
selected requireAll/class reduction/empty propagation.

General completion, GHC demand and sharing, checked state, machine bounds,
waiting counts, template exclusion, broader APIs/runtime, and the separate
Sized contracts remain open. Native intersection instructions, stored
substitution, plain projection, and Sized source are unchanged by this delta.

## Validation and preservation

The pinned full audit passes 2,078 jobs and 52,456 dependency checks. Only
propext, Classical.choice, and Quot.sound occur. No new warning occurs.
Eight new modules and three additive Audit imports contain the proof delta.
All prior proof definitions remain byte-identical.

The required strict Nix build passes all libraries, executables, tests, and
benchmarks with -Werror. All six suites pass 713 examples plus golden checks.
Fourmolu passes all seven changed Haskell files. Cabal-gild passes all four
active package files. Source code matches main except the retained caller
reproduction comment. The retained constructor changelog entry also remains.
Logs and source reviews use `/tmp/mcfta-main-889-*`.

Start: `/tmp/mcfta-native-events-checkpoint-20261015-2105/` (2,742 files).
Closing: `/tmp/mcfta-main-889-checkpoint-20261015-2122/` (2,751 files).
Script: `/tmp/mcfta-preserve-main-889-20261015.py`.
All prior artifacts, external drafts, stashes, and other worktrees remain.
Weekly allowance is 84%. Stop owned work at 1% or less. No board posts or
deployments. Push verified formalize checkpoints.
