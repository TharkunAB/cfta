# Upstream ordered enumeration and optimization coverage

Updated: 2026-10-19 12:42 CEST. Main: `184bba662`.
Merge: `a3cf692cb`. Previous verified checkpoint: `8282cca55`.

The merge adds changes from PRs #68, #87 and #88. Twelve paths change.
Six existing Haskell files take the exact upstream bytes. OrderedFrontier
is one new Haskell file. The other 261 existing Haskell files retain their
bytes. The merge retains both the local constructor-probe repair note and
all new upstream changelog entries. No local Haskell behavior patch is added.

## Ordered cursor

`cfta/src/Data/CFTA/Enumeration.hs` adds an optional ordered cursor. It
uses shallow child expansion and a separate frontier scheduler. Existing
eager entry points still call the original enumeration path.

The order contract requires admissible partial bounds and monotone pure
deterministic observers. An invalid bound can be reported after earlier
outputs. The contract leaves constrained cyclic truncation equivalence
open. Work and capacity limits count scheduler jobs and queue entries.
They do not bound callback cost or resident memory. Strengthening replaces
shared state; it does not validate the caller's monotonicity obligation.

`SourceCurrentEnumerationOrder` describes earlier edge ordering.
`EnumerationCPSRuns` describes the earlier enumerateFully composition.
Neither models the new frontier or caller-defined global keys. Their
checked laws do not establish the new cursor's implementation correctness.

## Template exclusion

`cfta/src/Data/CFTA/Template.hs` prepares a catalogue of finite template
subtrees and uses catalogue identities during exclusion. It combines
positive child patterns and rejects a requirement to both match and fail
the same pattern. The implementation uses sequences for ground groups.

The stated contract requires finite total templates, lawful equality and
ordering, and catalogue/group sizes that fit Int. Catalogue preparation
can force template parts that earlier execution did not inspect. The
preservation claim concerns the complete finite-term language. Run
multiplicity and recursive cutoff streams remain separate properties.

`SourceTemplateShapeSplits.splits_exact` models the earlier root-shape
filter. Its scope excludes the full forced/dying/ground schedule and
interned exclusion. It supplies no proof of the new prepared catalogue,
positive-pattern conjunction or identity-conflict pruning.

## Recursive subsumption

`cfta/src/Data/CFTA/Interned/Operations.hs` shares mandatory child pairs
through a visited worklist. Each narrow edge must have one compatible
unconstrained wide edge. Ambiguity discards the worklist and restarts the
original search from the original roots with fresh assumptions.

The review found no cross-alternative assumption leak. This inspection is
not an equivalence proof. `MergedAlternativesSubsumption.check` models the
earlier ancestor-stack search. The shared worklist needs an additional
equivalence or soundness proof. Existing termination requires a finite
pair inventory; it does not cover arbitrary physical unfolding.

## Typing notation

`cfta-generator/src/Data/CFTA/Gen/Typing/Do.hs` adds
`draw generator = [drawn generator]` and re-exports drawn. This is additive
syntax for the existing drawn premise. The new test compares it with an
explicit rule. No test run is claimed. Generator/refinement frontend
correspondence remains a separate whole-library obligation.

## Review and preservation

All twelve changed paths were inspected. No demonstrated new correctness
defect was found. No Haskell build or test was run. Existing upstream test
assertions are source evidence, not passed execution evidence.

Further validation should cover capacity pause/resume, strengthening of
queued completed work, invalid bounds and constrained recursive order.
Template conjunction and duplicate-ground cases need finite exhaustive
comparison. Shared-cycle subsumption needs comparison with ambiguity
fallback. These are follow-up validation tasks, not new repair requests.

The refresh manifest pins every changed post-merge path. All earlier Lean
sources retain their bytes. Existing counterexamples, repairs, marked
drafts, stashes and other worktrees remain preserved. Root FINDINGS records
this coverage change before the older repair entries. Publication awaits
direct approval. No push or board write is attempted.
