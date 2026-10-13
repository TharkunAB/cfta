# Bounded import fallback

Source: `origin/microcfta` at `a915177c`, including PR #114.
Local merge: `76a82a70`. The earlier Sized and ambient solver repairs remain.
Benchmark programs, benchmark datasets, and their workload specifications are
outside this formalization.

## Source control and errors

`SourceCompileImport.scan` follows the ordered indicator checks of reachable
edges. It retains the first unsupported guard. `route_denoted_iff` proves that
fallback requires a bound, successful pruning, and that exact residual error.
Pruning Unknown and invalid reconstruction do not select fallback.
`finish` preserves the residual guard if finite-term reconstruction fails.
`reportTimeLimit` catches only the solver timeout exception.

`SourceCompileImportExecution` records the completed external calls.
Negative bounds return the empty generator without calls. Other executions
make one pruning call and at most one denotation call. The fallback calls
denotation on the original graph. Pruning receives the depth-bounded graph.
Finite completed calls suffice for finite local control. This statement does
not prove that an external solver or native pruning call always completes.

## Exact denotation and reconstruction

`SourceDenotationEffects` models ordered residual `andM` and outer `filterM`.
`SourceDenotationRuns` projects the accepted terms and keeps their first
occurrences. All residual lists are evaluated before deduplication. A later
duplicate can therefore still return Unknown or raise an exception.
`SourceDenotationFilterM` checks the corresponding pure callback equations.

`SourceDenotationEnumeration` connects these lists to the checked CPS source
protocol. Bounded constructor rows derive a uniform sufficient protocol
bound. `SourceDenotationLiquid.eventual_exact` derives exact bounded logical
acceptance from each actual external response through the repaired mixed-sort
ambient adapter. It also proves duplicate freedom. Its depth convention gives
a leaf depth zero. It is not the node-count convention of `Data.CFTA.Sized`.
Finite completed external attempts give a finite denotation outcome, including
Unknown and exceptions. Correct replies need not be deterministic.

`SourceDenotationLevels` follows the ordinary shortcut's three tables:
the current level, terms through that level, and strictly shallower terms.
The first-deepest-child split is complete and disjoint.
`SourceDenotationLevelDistinct` proves duplicate freedom. The actual
distinct-symbol gate in `SourceDenotationPlain` derives safe set bypass.
Its signed result is exact, distinct, and ordered by depth. The global
empty-level stop preserves the finite prefix sequence. Set readback retains
an explicit membership and duplicate-freedom contract; its within-level
iteration order is not fixed by these theorems.

`SourceFromTerms` constructs the actual sorted distinct term and subterm rows.
Successful validation preserves both their order and their exact language.
`SourceFromTermsArity` proves that only inconsistent constructor arities can
reject these rows. `SourceDenotationRanked` derives consistent arities from
the accepted source language. Empty input also rebuilds successfully.

`SourceFiniteRebuild` proves strict child-height descent, acyclicity, and
finite ordered count/plan evaluation. `SourceFiniteRebuildDriver` derives the
compact driver's singleton-state contracts, intersections, cache completion,
and root ordered choice. It proves exact count and selector positions, both
rank inverse laws, and rejection outside the finite language.

`SourceDenotationRebuild.rebuild` combines the general guarded denotation and
finite count/plan statements. `SourceBoundedImport.liquid_eventual` combines
the actual ambient denotation, successful ranked reconstruction, and compact
distinct-language compiler. `compiler_fields` supplies the resulting count,
ordered selector, inverse, and rejection laws. `fallback_rebuild` excludes the
residual-guard reconstruction error for a successful ranked denotation.
`plain_correct` composes the ordinary shortcut with the same reconstruction
and compact language contract without solver calls.

## Observation groups and probabilities

`SourceImportGroups` constructs finite members for every actual graph split
part. It derives exact part languages, disjoint coverage, unique terms, and
the sum of part cardinalities. It does not assume those group properties.
`SourceImportGroupsSampling` follows cardinality weighting and empty-group
removal in `uniformlyGrouped`. It proves the uniform distinct-term law,
normalized probabilities, and public PMF event preservation. Each term has
probability one divided by the distinct accepted count.

`SourceImportGroupsFallback` obtains its language from successful
`SourceFromTerms.build`. `SourceImportGroupsRanks` constructs the three rank
query views and checks the actual final observation merge.
`SourceImportGroupsCompiler` compiles each constructed finite part through
the compact primitive driver. It derives exact emptiness, counts, decoder
positions, inverse laws, and final query-record positions.

## Remaining correspondence boundaries

The grouped reference members retain `input.eraseDups` order. The finite-term
primitive compiler uses the sorted constructor-row order. Neither statement
asserts the custom-key order of native `Flat.fromAutomaton`. A language
permutation or equal PMF does not prove rank-order equality.

Native `fromFTA` allocation, SCC readback, interned split representation, and
observation-map comparison still need their exact adapters. The constrained
denotation theorem needs complete constructor-row exposure and correct
intersection rows. A sufficient successful protocol bound does not establish
whole lazy-list termination or absence of every source error row. External
solver correctness and completion remain explicit. No verified Haskell
extraction or primitive machine-cost bound is claimed.
The ordinary shortcut also needs the exposed/trimmed finite row map and
source unconstrained-detection adapter. Outside the row inventory, the model
requires an empty outgoing row.

The existing Sized theorem and its direct original-row dispatch proof remain
the node-count, size-order, and public rank-order results. Older constructor
and equality drafts remain secondary targets.

## Validation

The pinned Lean 4.34.1 aggregate build passes 1,106 targets. Its audit checks
38,508 theorem dependencies and permits only `propext`, `Classical.choice`,
and `Quot.sound`. All 22 new modules are in the aggregate audit.
Log: `/tmp/mcfta-library-20261013-audit.log`.

The exact upstream merge previously passed 206 generator and 144 refinement
examples in Nix. Logs: `/tmp/mcfta-update-20261013-tests.log` and
`/tmp/mcfta-update-20261013-refinement-tests.log`. This continuation adds no
Haskell source edit or production test. It does not repeat those checks.
Fourmolu and cabal-gild checks pass in Nix for the newly merged library source
and package metadata. Log: `/tmp/mcfta-library-20261013-format.log`.
All 1,345 earlier Lean-tree files remain. The three marked drafts and the
untracked `NestedUnaryTwoAtom.hs` fixture retain their original bytes.
