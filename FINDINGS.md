# Current formalization findings

Updated: **2026-10-13 15:06 CEST**.

The formalization is rebased onto `origin/microcfta` at `4897831`.
Upstream contains the repairs in rows 1 through 21. Row 22 records a new
local repair for repeated recursive merge growth. PR #98 retains
groups of up to four edges during merged narrowing. The source guard check
also permits later literal identity replacements. The current proof updates
follow both changes.
All **620 existing Haskell examples** pass after the repairs: 284 core, 194
generator, and 142 refinement examples.

The full Lean development passes **919 jobs and 34,817 theorem dependency
checks**. All previously pending keyed-n-ary and recursive-join files are
integrated. New proofs cover nested heterogeneous join families, exact
public ranks and probabilities, original occurrence metadata, and the
changed upstream substitution and equality policies. See
[HANDOFF.md](HANDOFF.md) for the checkpoint and remaining work.
This is the current report. [lean/FINDINGS.md](lean/FINDINGS.md) records the
initial historical findings against an older revision. Its historical
"proposed repair" and "no production fixes" statements do not describe the
current branch. [lean/SYSTEM.md](lean/SYSTEM.md) contains detailed current
counterexamples, repair arguments, and implementation comparisons.

## Latest restart checkpoint

Proof checkpoint: **`22d0adc`**. Stable proof files are committed and imported
by the working aggregate audit. Proof work continues; inspect the live working
tree at restart. The marked draft
`lean/MicroCFTA/MergedAdaptiveStability.lean.incomplete` is preserved unchanged.
Its completed sibling now proves exact fuel independence.

The requested upstream refresh and explicit rebase were repeated at this
restart. `origin/microcfta` remains at
`489783177b0a7fd34bb6bf205e66d7d5cce0d1fe`; the branch was already up to date.
Backup `backup/formalization-before-refresh-20261013-1435` preserves `efd0ddc`.
The refresh changed no Lean file and left stashes and other worktrees intact.
New work remains local.

`MergedAdaptiveMerge.execute_complete` now proves the complete adaptive
physical merge's successful execution and finite-language coverage.
Ordinary height supplies sufficient recursive fuel. The proof derives all
smaller calls, actual current-state comparison selection, child columns,
edge interning, and parent construction. It has no recursive correctness or
termination premise. Prepared initial context, concrete guard interpretation,
structural source grouping, and the outer memo wrapper remain explicit
correspondence boundaries. `MergedAdaptiveStability.enough_eq_execute` now
proves exact extra-fuel independence, including the returned record and cache.
See [adaptive worker](lean/notes-merged-adaptive-worker.md).

`MergedSourceComparison` now executes the ordered stateful source comparison.
`MergedComparisonFacts.check_verified` preserves facts, both histories,
`NoNewMu`, and actual warming progress. Failed cover attempts retain their
cache effects. `MergedComparisonColdMeasure` proves that every changed
verified cache strictly decreases the number of cold original Mu records.
`MergedComparisonReaderReplay` proves exact completed reader replay in any
later cache. `MergedComparisonCompletion.check_complete` now derives a
stable sufficient-fuel bound from cold Mu records and unvisited identity
pairs. `MergedComparisonStability` proves fuel independence of every successful
result. `MergedComparisonReplay.check_replay` preserves the exact Boolean
and removes all effects on replay in a later cache.
`MergedComparisonSoundness.check_sound` now proves inclusion in the actual
returned cache. It requires no `Ready`, warmup, recursive callback law, or
coinduction premise. The guard interpreter and sound clear-guard test remain
explicit. See
[comparison restart](lean/notes-source-comparison-handoff.md).

`MergedSourceExposureCoverage.actual_exact` proves reverse edge coverage and
exact finite-term semantics in the original reader's returned cache. It needs
no global `Ready` or warmup. `MergedSourceSelection.select_complete` then
derives stable ordered cold child filtering with actual comparison effects.
`MergedSourceSelectionSemantics.select_complete_exact` proves its exact
union-language preservation in the returned cache. `MergedSourceGrouping`
derives the structural grouping contract from executable partitioning and
proves the source append-fold bucket equation. Cold merge composition remains
active.

`InternedOrdinaryLevelBoundary` disproves equal computed levels under
fresh-only capture changes on actual source calls. Its checked levels change
from 0 to 1. The closed embedding completes and stores nested probe depths
`(1,0,1)`. It supplies no pending or divergence counterexample.
`InternedPendingLiveMismatch.closed_live_depth_mismatch` now derives a
live lexical mismatch from any hypothetical pending run. Its later name is
a live capture of the active ancestor and occurs in the original Depth probe.
`InternedPendingOrdinaryOrigins.closed_capture_depth_mismatch` now retains
the actual earlier enclosing Depth call that introduced the captured level,
with fewer lexical inputs. `InternedOrdinaryCaptureBoundary` checks a closed
completed example with levels `0 → 1` and the later ordinary name already in
the original Depth probe. Support or alias alone cannot exclude the mismatch.
The next target is to retain both exact key components and derive descent
through the shorter producer context. See
[literal observations](lean/notes-interned-literal-observations.md).

The full formalization remains unfinished. The exact restart order,
commands, draft status, proof boundaries, source checks, and preservation
instructions are in [HANDOFF.md](HANDOFF.md).

## Baseline and required contract

The continuation branch is `formalization/microcfta-resume-20261012`.
Its implementation base is `origin/microcfta` at `4897831`, including
PRs #97 through #101. The reset continuation rebased all 274 commits.
Source conflicts kept the merged upstream implementations and all local proofs.
Backup `backup/formalization-before-refresh-20261013-1306` retains the
published checkpoint `8a80947`. The rebased proof tree initially matched it
exactly. The earlier restart rebased 267 commits onto `8ac24bb`. Backup `backup/formalization-before-refresh-20261013-0418` retains
the previous checkpoint `2aacf4f`. Proof commit `721ff6d` adds full free-name
semantics and historical probe boundaries. The previous proof branch remains
unchanged. Backup `backup/lean-before-microcfta-20261012-2200` and the retained
stash preserve the pre-rebase work. Matti explicitly requested publication of checkpoint `8a80947`; it was
pushed to `formalization/microcfta` at 04:33 CEST. New work remains local.
For a constrained language, compilation and enumeration must contain every
valid finite term and no invalid term. A finite FTA language with `n`
distinct terms must have exactly `n` ranks, with both decoder/inverse laws.
Sampling must give each term its requested normalized weight. An exact
optimization must preserve both the accepted language and the weights.

Three counts must remain separate:

- A **term** is one finite ordered constructor tree.
- A **run** is one accepting derivation. Several runs can produce one term.
- A **generator member** is one indexed source occurrence. Several members
  can have equal values and equal constructor terms.

The distinct-term rank contract applies to the FTA import path. Arbitrary
generator choices, maps, and joins retain members. They are not a quotient
by term or value equality. The checked recursive example
`label N (choice [pure, occurrence, occurrence])` has two size-two member
ranks with the same complete constructor term. Its inverse correctly returns
both ranks. This is a contract distinction, not a new decoder defect.

## Repaired source defects

Rows 1 through 21 are merged upstream at `4897831`. Rows 18 through 21
were local repairs at the earlier checkpoint. Row 22 is a new local repair. Each row has a retained source reproduction and a corresponding formal
counterexample, repair theorem, or operational model. Older per-repair test
totals in the linked reports describe their historical checkpoints. The
current combined suite total is 620.

| # | Failure before the repair | Current behavior and evidence |
| --- | --- | --- |
| 1 | Quantified substitution could capture a name in an `App` function position and change `No` to `Yes`. | Rename bound function heads and substitute nullary applications as values. Reject an unrepresentable non-name function head through the checked API. [Reproduction](lean/repro/FormulaCapture.hs). |
| 2 | A tautological observation of an atomic 9:1 choice could make bounded sampling uniform after a product. | Retain within-size atomic weights and transport their size metadata. [Reproduction](lean/repro/CurrentFindings.hs); `MassRetention`, `SizeMass`, `SizeTransport`. |
| 3 | Minimization could delete the only accepted root term without installing its chosen representative at the root. | Install root representatives and recheck an accepted derivation after the complete schedule. [Detailed finding](lean/SYSTEM.md#minimization-can-remove-the-only-accepted-root-term); `MinimizeSchedule`. |
| 4 | Union inside a nested binder could discard an enclosing reference and omit valid finite terms. | Retain open union operands and resolve their epsilon closure after binding. [Reproduction](lean/repro/OpenUnion.hs); `EpsilonUnion`. |
| 5 | Pruning a valid open nested binder could raise `nodeEdges: unresolved union reference`. | Inspect the stored open body before unsafe outer-edge unfolding. [Reproduction](lean/repro/PruneOpenBinder.hs); `PruneReads`. |
| 6 | Closing grouped applications could produce support graphs that rejected every decoded term. | Close every retained private alternative and preserve the complete callback image. [Reproduction](lean/repro/GroupedSupport.hs); `SupportAlternatives`. |
| 7 | Constructor and application closing could remove private nodes across a recursive occurrence boundary. | Use one private `Recursion` boundary consistently in support, inspection, terms, and inverse ranking. [Reproduction](lean/repro/RecursiveSupport.hs); `RecursiveSupportBoundary`. |
| 8 | Grouped function spines could lose correlation between their retained child alternatives. | Preserve correlated function prefixes while closing the support and inspection graphs. [Reproduction](lean/repro/GroupedSpine.hs); `SupportSpineAlternatives`. |
| 9 | Sparse nested substitution could discharge a guard that complete evaluation rejected, admitting an invalid term. | Retain the guard and return `SolverUnknown` for the reproduced enclosing-name conflict. Safe flat ambiguous scopes can compile. This does not assert an empty language. [Pruning reproduction](lean/repro/NestedScopeCapture.hs), [compiler reproduction](lean/repro/NestedCompileCapture.hs); `PruneAmbiguity`, `SourceEnclosingRenames`. |
| 10 | Equivalent conjunctions grew from size 9 to 29 to 89 during repeated acyclic equality reduction. | Flatten outer conjunctions, remove `Top`, sort, and deduplicate while preserving scopes. The retained case stabilizes. [Reproduction](lean/repro/PruneConjunction.hs); `GuardConjunction`. |
| 11 | Combining independently interpreted guards could change an operand's meaning and admit a term rejected by an input automaton. | Allocate each outer Boolean operand independently and preserve nonempty substitution scopes. The reproduction now reports `[Yes, No, No]`. [Reproduction](lean/repro/ConjoinScope.hs); `SourceBooleanEntry`. |
| 12 | Recursive equality narrowing repeatedly expanded equivalent domains and exceeded the retained runtime limit. | Block constrained recursion while retaining the original equality constraint. The current binder constructor also removes its bare self-reference from root unions. [Reproduction](lean/repro/RecursiveReduction.hs); `ConstrainedRecursionGate`, `BinderSelfUnion`. General nontermination of the old example was not proved. |
| 13 | Observing an imported explicit union could drop every valid term and report `EmptyGenerator`. | Expose `InternedUnion` through the finite epsilon closure before ordinary observation splitting. [Reproduction](lean/repro/ImportUnion.hs); `ImportObservations`. |
| 14 | Observation filtering could reject valid recursive groups as `UnboundedGenerator` and lose their size indexes. | Filter the ascending key map directly and retain complete recursive records. [Reproduction](lean/repro/RecursiveGroupFilter.hs); `RecursiveGroupFilter`. |
| 15 | `boundDepth` could loop on retained empty binder cycles even though their outer-edge closure was empty. | Use visited `nodeEdges` exposure uniformly before recursing into constructor children. [Reproduction](lean/repro/BoundRetainedBinders.hs); `LexicalBinderClosure`. |
| 16 | A syntactic extraction such as `v == v` could be treated as an exact integer measure and remove valid expressions. | Reject fallback measures that depend on the refined value. Preserve exact singleton extraction priority. [Reproduction](lean/repro/SelfDependentMeasure.hs); `DefiningTerm`, `ParentGuardFormula`. |
| 17 | Recursive open group positioning queried cardinalities, built an empty position map, and raised `Map.!`. | Read the available group keys directly. Unsupported recursive integer closure now returns its existing explicit error. [Reproduction](lean/repro/RecursiveOpenPositions.hs); `GroupPositions`. |
| 18 | In one substitution scope, merging equal actual identities could remove the first identity replacement and expose a later replacement for the same formal. Sparse evaluation returned `Yes`, pruning admitted a rejected term, and compilation produced one invalid tuple. | Return `Unknown` when an uncertain identity replacement has a later non-identity replacement for the same formal. Later literal identities remain accepted; allocator coherence proves this refinement safe. Pruning retains the guard; compilation returns `SolverUnknown`. The existing [guard/pruning reproduction](lean/repro/NestedScopeCapture.hs) and [compiler reproduction](lean/repro/NestedCompileCapture.hs) now check both nested and same-scope cases. `SameScopeIdentityCapture` retains the pre-repair witness; `SourceSubstitutionPrecedence` proves the new check. |
| 19 | A recursive callback could inspect temporary support and select different bodies during count, term, and support rebuilds. The public bounded generator returned four terms that its support rejected. | Keep construction tokens separate from size flags. Reject payload queries until the definition completes. Nested definitions retain enclosing tokens; both recursive and finite return paths remove their own token. `RecursiveConstructionQueries` proves marker provenance, stable rejection, and completed query behavior. The existing recursive-member case in `GenSpec.hs` checks the original callback, fourteen query paths, and nested-family completion. See [the construction-query notes](lean/notes-recursive-construction-queries.md). |
| 20 | Grouped key discovery retained an earlier minimum after a callback changed its base. `minimumSize` returned zero although counts were `[0,1,1,1]` and the smallest member had size one. | Compare the final probe's keys and minima with the accumulated discovery table. Return `InconsistentRecursiveFamily` on disagreement. `GroupedProbeValidation` derives a true body fixed point for every successful check and proves that constructor programs retain their previous least-attained minima. The existing recursive-member test retains the public callback. See [the discovery-validation notes](lean/notes-grouped-probe-validation.md). |
| 21 | `mergeAlternatives` on the union of two recursive languages repeatedly unfolded the same child union. Direct recursive operands and wrapped union operands exceeded the diagnostic timeout. | Stop recursive merging at retained recursive or union boundaries. Preserve the union and its accepted terms. The direct merge and enclosing equality reduction now complete. [Reproduction](lean/repro/MergedNarrowing.hs); [proof boundaries](lean/notes-merged-narrowing.md). |
| 22 | The retained recursive child union was immediately unfolded into an ordinary node. Repeated equality passes on five recursive alternatives added six nodes and sixteen edges per observed pass. Public pruning exceeded the diagnostic timeout. | Use `createUnion` at the recursive-boundary return to retain the explicit union. The same public prune call completes. The retained fixture has idempotent merging and reaches an equality fixed point after two changing passes. This finite evidence does not prove general nested-schedule termination. See [merged narrowing notes](lean/notes-merged-narrowing.md) and [the source reproduction](lean/repro/MergedNarrowing.hs). |

The private `Recursion` repair changes engine-term shape. User values,
surface terms, original generator counts, distributions, and rank order
retain their semantics. Importing raw support counts the new private nodes
as nodes, so an imported node-count bound can change.

## Rebase integration and optimization coverage

The new upstream equality worker performs one pass. Its proof now describes
that operation directly. Explicit pruning and partial-reduction callers still
use fixed points where the source does. The formalization no longer attributes
an internal fixed-point loop to the public one-pass worker.

The classified similarity optimization preserves the exact ordered eligible
pair list and inference-error behavior. Its candidate comparison count is
the sum of `n * (n-1) / 2` over the classes. Classification, maps, and solver
costs remain separate. See [the similarity proof notes](lean/notes-similarity-within.md).

The indexed minimizer preserves the previous full-table schedule, including
root representatives and final copy passes. Installing a root representative
creates child links. The rebase integration now adds those parent-index
entries. Otherwise a later indexed copy could miss an inserted edge.
`MinimizeParentIndex` proves complete schedule equivalence and the required
metadata invariant. This is an integration obligation; it is not counted as
a separately reproduced public defect. See
[the parent-index notes](lean/notes-minimize-parent-index.md).

Retained size masses also move when constructors pay a size unit. Earlier
integration omitted those shifts in two paths. The source and transport
proofs now preserve the member/mass alignment.

The constructor record model omitted the current root self-reference filter.
`compileBody` now applies it at both probes and at the reserved binder identity.
The coherence, pending-record, and replay proofs include that reconstruction.
Kernel checks show that a recursive body with an added bare self operand
returns the same canonical record as the body without it. A second check
covers cleanup to an ordinary node. This repairs a source-correspondence
omission in the formalization; it is not a new Haskell defect. The lexical
`InternedBinderRebuild` and full `InternedSubstitution` worker now apply the
same filter. Their capture-avoidance, exact-language, free-reference, and
finite-allocation results remain proved.

## Recursive construction query repair

The pre-repair reproduction uses only public operations:

```haskell
recur $ \self -> case support self of
  Right EmptyNode -> oneof [pure 0, node "step" ((+ 1) <$> self)]
  _ -> leaf 99 "wrong"
```

Before the repair, the bound-three generator had four ranks and values zero through three,
each with probability one quarter. Its support rejects all four returned
engine terms. Count, sampling, and term rebuilds expose EmptyNode through
the placeholder; support reconstruction exposes its live recursive node.
The original public guardedness test accepts the body. The public API does
not state that a builder must avoid inspecting its argument.

The repair makes `support self` return `QueriedRecursiveOccurrence` in every
rebuild. The callback consistently returns the finite value 99. Its term
belongs to the returned support. Independent construction tokens remain
present during closed probes, which deliberately clear size-index flags.
The reproduction and pre-repair output are `/tmp/mcfta-context-builder.hs`
and `/tmp/mcfta-context-builder.log`; the repaired result is in
`/tmp/mcfta-context-builder-repaired.log`. The existing suite retains the
callback and the nested selected-key completion case.

This repairs the observed payload-query mismatch. It does not establish
regularity of every arbitrary callback or monotonicity of key discovery.
An empty family has no active records to reject. A callback can observe that
initial state and change its finite base after keys appear. Row 20 validates
the final discovered table before the source returns a tied family.

## Behavior that does not satisfy the stronger requested contract

**Similarity minimization preserves representatives, not every original
term.** Repairing root deletion does not make it an exact-language
optimization. A caller that requires all original expressions must not use
the representative theorem as a completeness theorem for the original set.

**Pool minimization does not preserve similarity-class probability.** It
starts a uniform distribution over the retained entries. The checked example
changes class masses from `2/3, 1/3` to `1/2, 1/2`. No discarded weight is
transferred to a representative. See
[the probability notes](lean/notes-pool-minimization.md) and
[the public reproduction](lean/repro/MinimizedPoolDistribution.hs).

**Unsupported or uncertain constraints are not empty languages.** General
quantified and nonlinear constraints lack a complete terminating solver
contract. The lattice backend rejects unsupported syntax, including `Ite`.
`Unknown`, timeout, unboundedness, and missing inspection fields remain
explicit states or errors.

**Logical alpha-equivalence does not imply identical solver verdicts.** A
sound name-sensitive callback can change `Yes` to `Unknown`. The supplied
adapter also rejects a generated actual name that collides with an unused
ambient declaration. No invalid term is admitted by that example. Exact
verdict preservation needs a name-transport/freshness contract. See
[the boundary notes](lean/notes-guard-alpha-boundary.md).

## Verified model coverage

The checked development includes independent constrained grammar derivation,
FTA acceptance, finite-term enumeration, exact finite distinct-term ranks,
symbolic count/select/rank workers with caches, supported lattice counting
and ranking, and exact rational distributions. It also covers the stated
intersection, pruning, canonical guard, minimization, and interning algorithms.
Their scope and premises are recorded in [SYSTEM](lean/SYSTEM.md),
[COVERAGE](lean/COVERAGE.md), and [API-COVERAGE](lean/API-COVERAGE.md).

The latest committed recursive work connects independent value and term
indexes, source count and sampler equations, complete inverse queries,
candidate flags, ordering, distinct returned positions, and bounded global
ranks. It includes arbitrary-branch single-root bodies and binary-choice
mutual key families. `GroupedMergeAssociativity` preserves the complete
ordered member and rank-probability fields under regrouping.

The aggregate audit now includes those results for arbitrary-branch mutual
families. The new dispatch proof distinguishes bare
singleton grouped merges from raw singleton choices that add `Choice 0`.
The original typed guard proof distinguishes a user label from a plain pay.
Both add size; only the label supplies the corresponding term-growth guard.
See [the n-ary notes](lean/notes-keyed-nary.md) and
[guard notes](lean/notes-keyed-nary-guards.md).

The recursive-join adapter now composes the actual `JoinN`, `CenterKeyed`,
and `ArgKeyed` structures through typed nested joins and mutual families.
It preserves heterogeneous argument values, aligned term ranks, retained
masses, and complete ranked samplers. The record-to-selector bridge is
complete. Mutual callback induction and the public replay filter establish
all-view and bounded global decoder preimages. Original occurrence metadata
supplies the public guards. Candidate bounds include false flags. Callback
and public rank lists are ordered and have no duplicate positions under
their local finite-leaf contracts. Ordinary `Apply` remains a separate constructor.
Support, diagnostic inspection, both sampling routes, weight flags, and
absent-term branches now have constructor-derived adapters.
`RecursiveCompleteRecord` ties these fields and the original occurrence
checks to one checked program. Arbitrary runtime schema changes remain open. See
[the join notes](lean/notes-recursive-join-fields.md).

## Evidence and its limits

- Latest source suites: **620 passing examples**, on `4897831` plus local
  repair `c76d1ec`. Log: `/tmp/mcfta-20261013-retained-union-tests.log`.
  Fourmolu and Cabal-gild checks pass. Both retained recursive-merge source
  cases and both ordered-profile/rank-stutter source replays also pass.
- Repaired nested and same-scope source probes both report `(No,Unknown)`
  for complete/sparse evaluation, `(No,No)` before/after pruning, and
  `Right []` versus compiler `Left SolverUnknown`.
  Log: `/tmp/mcfta-scope-precedence-repaired.log`.
- Latest integrated Lean audit: **919 jobs; 34,817 theorem dependency checks**.
  Only `propext`,
  `Classical.choice`, and `Quot.sound` are allowed.
  Log: `/tmp/mcfta-20261013-sound-selection-audit.log`.
- The earlier formula capture, nested compiler capture, recursive equality,
  and open-union reproductions passed at the `de910ea` checkpoint. The independent two-key
  recurrence again checks all eight classes and 285 inverse ranks, including
  exact masses, conditional probabilities, and support acceptance.
  Log: `/tmp/mcfta-de910ea-focused.log`.
- Independent source probes covered 5,000 finite grammars; 1,536 mixed
  grouping/recursion descriptions; nine automaton-import variants; 144
  weighted descriptions across nine size bounds; and 2,080 bounded recursive
  intersection comparisons.
- The new heterogeneous `Bool`/expression join recurrence checks eight
  classes and 37 member inverses, exact masses, and support acceptance.
  Log: `/tmp/mcfta-heterogeneous-join-replay.log`.
- Earlier exact-rational recurrences checked 132 single-root and 254 two-key
  member inverses. The 285-rank delayed-third-branch probe was rerun above.
- Shared equality FTAs with `2^60` and `2^80` distinct terms passed exact
  counting and distant decode/rank round trips without enumerating their
  language. These are feasibility checks, not general benchmarks.

Efficiency has separate proof obligations. Balanced selection has checked
comparison/query bounds. Symbolic selection skips counted blocks, while
overlap preprocessing can be exponential. Polynomial evaluation and
arbitrary-precision arithmetic are not free. `groupBuilt` still enumerates
an already-built finite source during observation compilation.

The Lean sources are handwritten models and algorithm ports. The audit
checks their logical dependencies; it does not verify Haskell-to-Lean
translation. Source reproductions and finite probes support correspondence
but do not prove it for every runtime execution.

## Current proof results and remaining obligations

The current proof checkpoint is **`22d0adc`**. The integrated working audit passes
**919 jobs and 34,817 theorem dependency checks**. Stable proof modules
are committed and imported by the working aggregate audit. The full
formalization remains incomplete. The detailed restart order, commands,
repository safeguards, and supporting file map are in [HANDOFF.md](HANDOFF.md).

### Full nested source profiles and exact stored body tags

`InternedNestedProfiles` proves root-profile correspondence and the decoded
Mu-profile heap invariant for arbitrary full constructor `Syntax`. It covers
actual ordinary constructors, root self filtering, both probes, fresh-body
execution, smart/raw cleanup, canonical cache hits, and pending outcomes.
There is no binder-free restriction or assumed callback equation. Profiles
retain opacity and the set of literal root references. They do not retain
ordinary structure, Mu identities, or canonical union order.

`InternedStoredMuOrigins`, `InternedNestedMuOrigins`, and
`InternedProfileMuOrigins` derive the actual original source expression,
captured environment, three normalized calls, reservation, and historical
invariants for every completed stored Mu. The enclosing execution may itself
stop at another pending key.

`InternedStoredProbeTags` then proves:

- A stored body is EmptyNode exactly when both probes are EmptyNode.
- A stored body is its own reserved reference exactly when the probes are
  `RecDepth` and `RecUnint 0`.
- Smart cleanup returns EmptyNode exactly in those two key cases.

These are source-derived statements about all stored records, not finite
sample conclusions. See [the source profile notes](lean/notes-interned-root-profile-source.md),
[verified origins](lean/notes-interned-profile-reflection.md), and the dated
03:21/03:28 results in [the gate notes](lean/notes-gate-unfolding-rank.md).

### General constructor completion remains open for other keys

`InternedSpecialKeyCompletion.closed_safe` excludes pending readback at
`(Empty, Empty)` and `(Depth, Unint 0)` for **unrestricted closed Syntax**.
It has no admission grammar, callback-law, or whole-run-success premise.
The proof obtains earlier completed nested sites from the actual depth-body
trace. `InternedProfileReferenceInputs` derives the required invariance under
arbitrary literal-reference aliases.

`InternedPendingProfileBoundary.closed_remaining` restricts any remaining
hypothetical encounter to two opaque probes, or two pure probes with nonempty
fixed captured root references. `InternedPendingOldCall` independently retains
the active fresh ancestor reference and both exact probe records already
available before that ancestor reservation.

Exact local replay now covers ordinary nodes, unions, root filtering, and
cleanup through actual common cache extensions. `InternedBoundaryFreeAge`
includes free names inside old boundary Mu payloads. `InternedLiteralObservations`
derives empty-result agreement and forward bare-local reflection for actual
full-Syntax calls with arbitrary same-length literal aliases. The remaining
step is the dynamic Mu boundary/identity argument. Set equality of root
profiles cannot establish exact canonical request replay. `InternedProbeFreeSupport`
propagates free-name absence through stored probe dependencies.
`InternedProbeDependencyAge` proves strict identity descent and well-foundedness
for that graph. This is not a body-unfolding rank. `InternedOldProbeReplay`
closes the old complete-record hit case from its two smaller probe observations;
the newer smart-Mu case still needs joint boundary transport.

**Full free-name semantics and its source heap invariant are proved.**
`InternedFreeNameSemantics` covers all Syntax, with arbitrary external-name
maps. `InternedFreeNameForm` derives fixed captures and an optional argument,
including captured probe aliases. `InternedNestedFreeNames.build_free` and
`closed_heap` follow the actual mutual source execution, including cache hits,
fresh body calls, and pending outcomes. `InternedSourceFreeNames.closed_free_empty`
proves that every completed closed run has no free names.

`InternedFreeNameMuOrigins` retains both semantic tables at each stored Mu's
historical source prefix. `InternedStoredFreeNameBoundary.closed_reference_absent`
uses those origins: an old-free-name bound on the actual stored body excludes
fresh literal boundaries in both original probes. The fresh Mu-boundary half
remains open. See [the free-name proof](lean/notes-interned-free-names.md).

`InternedPureProfileIdentity.ordered_identity` identifies available pure values
from equal ordered profiles in a common normalized state. Its checked reverse
union example disproves identity from set equality. The checked warm-cache
example in `InternedPureProfileOrderBoundary` disproves exact ordered syntax
correspondence. The next proof must derive actual ordered replay; it cannot
replace profile equivalence by ordered equality.
See [the special-key proof](lean/notes-interned-special-key-completion.md),
[observed root replay](lean/notes-interned-observed-root-replay.md),
[boundary transport](lean/notes-interned-boundary-transport.md), and
[literal observations](lean/notes-interned-literal-observations.md).

### Live lexical replay and actual probe sites

`InternedFreeAbsenceReplay` proves exact raw source replay after an interned
free name disappears. `InternedLiveInputReplay` strengthens this to arbitrary
literal maps that agree at the pure interpreter's live lexical positions.
`InternedLiveInputReadiness` excludes a later pending request from an earlier
completed matching site and the later actual completed probes. It does not
assume the later binder completes.

`InternedProbeChoiceSites` extracts actual earlier sites along chosen Depth
or Unint callbacks. Each crossing retains its computed ordinary level and
chronological cache-growth evidence. `InternedLiveInputSupport` derives the
needed agreement when every changed current input is fresh and the current
probe is an older available record. General encountered scopes can also
have different Unint levels. Those differences remain an explicit gap.

`InternedProbeChoiceSites.completed_route` now retains the exact source body
at every crossing, as well as its probe choice and cache history. This
supports comparison with the actual pending descendant path. Do not assume
that a stored body's depth equals either probe's depth:
`InternedClosedProbeCostBoundary.actual_depths` checks depths `(1, 0, 0)`
in a record created by a closed source run. This is a boundary for the
proposed invariant, not a source divergence counterexample.

`InternedPendingOrdinaryMismatch.closed_depth_mismatch` now derives two
completed Depth calls of the same source body with different cached depths
from any hypothetical closed pending run. It derives the active source
origin, both lexical routes, literal contexts, and chronological histories.
No assumed callback equality or externally supplied origin is required.
The remaining ordinary-level mismatch case is not yet excluded.

### Physical comparison and cold execution

`MergedOrdinaryHeight` and `MergedMergeTermination` give a decreasing measure
for guarded recursive merge calls. `MergedComparisonSource` includes the
source EmptyNode shortcuts and ordered arity checks. `MergedPhysicalWarmup`
and `MergedPhysicalComparison` derive a finite physical inventory for the
`PreparedWithoutMu` fragment. `MergedPhysicalLanguage` proves exact finite
term semantics for its epsilon reader. `MergedPhysicalUnion` proves exact
operand-union language through actual normalization and cache readback.

`MergedColdExecution` and `MergedColdInventory` derive completion per unfold,
finite cache changes, and a finite inventory for one generated chronological
trace. They require no eager warmup and do not compare hypothetical allocation
histories. `MergedColdReaderFacts.read_closed` now proves successful ordered
source edge exposure for closed roots in that fragment. It returns resident
edges with closed children, the exact final cache, preserved facts, and exact
stability under extra proof fuel. `MergedSourceExposureLanguage` derives
actual epsilon origins for every returned edge and proves finite-term
soundness. `MergedSourceExposureCoverage.actual_exact` now supplies reverse
coverage and exact language in the actual returned cache. The full ordered
stateful comparator completes with exact fuel stability and later replay.
Its actual-cache semantic inclusion and exact child-selection language are
proved. Full cold merge composition remains active.

`MergedPhysicalGroupRoot.grouped_root_covers` proves ordinary-root language
coverage through actual child, edge, and parent effects. The checked column
worker derives filtering soundness from physical comparison and covers
singleton, retained recursive union, and ordinary union branches. Recursive
certificates apply only below the parent height. The later `MergedAdaptiveMerge.execute_complete` composes those
certificates with current-state selection and derives the complete prepared
worker result. Its remaining source correspondence boundaries are explicit.
See [physical comparison](lean/notes-merged-physical-comparison.md),
[actual union semantics](lean/notes-merged-physical-union.md), and
[cold execution](lean/notes-merged-cold-comparison.md). The new
[cold reader](lean/notes-merged-cold-reader.md) and
[physical group](lean/notes-merged-physical-groups.md) notes give exact scopes.

### Equality fixed-point termination

**Source baseline change:** PR #97 inserts `mergeAlternatives` after every
peer projection. The original `EqualityLeafProjectionRuntimeBound` still
models the previous worker. The new `MergedProjectionBound.compiled_bound`
now proves the complete merged projected-leaf schedule. It covers physical
row grouping, exact source edge and node requests, snapshot targets,
simultaneous edits, class order, required paths, and the final fixed point.
`MergedRawLeafSource.worker_actual` uses the actual runtime output cache;
no later operation executes from a proof-prepared cache. Group iteration
order is explicit and must include all source symbols. The bound remains
the original occurrence weight plus one. Endpoint domains must be leaves.

`MergedAlternativesSubsumption` proves soundness of successful bounded
recursive coverage checks, including ancestor-pair reuse. `MergedEqualityReduction`
proves full constrained-language preservation under a merge-superset contract.
The physical leaf worker now has a language-coverage theorem. Complete
group orders give equal records in a common cache, and an observed row order
derives completeness. Coverage search saturates under a complete finite pair
inventory. General recursive merge termination and the recursive physical
superset bridge remain open. See [merged narrowing](lean/notes-merged-narrowing.md).

The complete physical **projected-leaf** schedule has a derived bound of the
original occurrence weight plus one. It includes actual endpoint reads,
first-seeded target folds, recursive ancestor edits, required paths, class
order, empty propagation, and an allocation-free final fixed point in the
actual runtime cache. Endpoint domains must be leaves; ancestors may be nested.
Raw guard normalization and rejected constructor allocations are included.

Two source-correspondence gaps were repaired in the formalization. Raw leaf
pullback and dead-row trimming prevent proof-prepared caches from becoming
runtime inputs. The physical intersection model now includes the source's
ordinary-node identity orientation. The path worker uses the exact ordinary
source union branch. These were model repairs, not additional Haskell defects.
The 4,096 projected forests and 1,156 raw leaf source pairs pass again. See
[the runtime bound](lean/notes-equality-leaf-runtime-bound.md) and
[runtime trimming](lean/notes-equality-leaf-runtime-trim.md).

For one fixed **binary projected class**, `EqualityFixedProjectionInvariant`
proves that every original occurrence retains its rows after the first
reciprocal pass. `EqualityFixedProjectionTermination.run_bounded` counts missing
occurrence-row pairs in a finite complete inventory. Nested endpoint rows are
allowed. Its premises include a static commutative row relation with admitted
diagonals. The physical adapter, disappearing-ancestor phase, raw normalization,
and interaction with other classes still need composition. A public Haskell
probe with nested endpoints takes four changing passes and agrees with this
invariant. See [the binary-class proof](lean/notes-equality-projected-binary.md).

The general nested fixed schedule remains open. New checked obstructions are:

- `EqualityFixedMultiplePeers`: a convergent three-peer source-shaped example
  removes a row after the first pass. Binary occurrence growth does not extend
  directly to larger classes. Its separate abstract Steiner cycle shows that
  commutativity/idempotence alone are insufficient; it is not a source cycle.
- `EqualityFixedDegreeCounterexample`: the five-degree source leaf table has a
  nonassociative mutually reachable narrowing component. Public Haskell confirms
  the table and witness. Such components cannot be assumed to be semilattices.
- Earlier `EqualityFixedSaturationCounterexample`: alternating targets can
  return to an earlier representation even with the same recursive closure
  image. An arbitrary-target rank is unavailable.

`EqualityFixedRowProfile` derives local Boolean row behavior when higher
profiles agree. `EqualityFixedProfileMaximum` proves a removable maximum for
one finite powerset layer over a strict-ranked row base. These results do not
supply arbitrary nested lifting. Synchronized higher-profile induction is a
candidate next route. No cycle of the actual fixed source schedule is proved.

### Recursive gate rank: pure probes complete, opaque probes remain

`InternedPureProbeGate` and `InternedProbeOpacity` derive actual stored-body
unfolding completion and strict head-rank decrease from a pure depth probe.
The second probe is also pure, its level is zero, and the actual body depth is
zero. The original source syntax may have arbitrary nesting. Earlier shallow,
reachable-only, closed-nested, and marker one-step results retain their scopes.
The general case with **opaque probes** remains open.

The following checked examples rule out attempted generalizations:

- `InternedOldBodyProbeAliases`: a smart unused old body can differ from both
  normalized probes because captured sentinels are filtered differently.
- `InternedNestedProbeCostBoundary` and `InternedClosedProbeCostBoundary`:
  exact free-occurrence cost coverage fails in a completed closed source-model
  cache at slot 19. The body has external sentinel costs 1; both probes have
  those names only at cost 0. The closed program returns EmptyNode. The existing
  `FlatProbeHeap` theorem must retain its restricted scope. Haskell confirms the
  open fixture and both actual-own-to-probe substitution equations.
- `InternedSourceRankStutter`: staged scoped source-model construction with
  explicit `Depth`/`Unint 2` captures and cache prepopulation gives an actual
  modeled unfolding where both head rank and free-occurrence rank stay at 2.
  The continuation has ranks `[2,2,1,0]`. This does not establish divergence,
  closed empty-environment reachability, or universal callback admissibility.
  Haskell now confirms both rank traces and the preloaded representative. The fixture fails the unrestricted callback renaming law when the old name aliases its fixed capture. See [the source replay](lean/notes-source-rank-stutter-replay.md).
- Exact ordered root-profile correspondence is false. Reversing captured union
  operands can hit the same Mu key and return the first stored order. The
  temporary kernel check `/tmp/mcfta-profile-order.lean` passes after completing
  its inequality proof. The set-based `Equivalent` theorem remains valid.

These are proof-obligation counterexamples. They do not add production defect
rows to the repaired defects above. See
[the gate notes](lean/notes-gate-unfolding-rank.md) and
[literal profile order](lean/notes-interned-literal-observations.md).

### Other remaining source contracts

Typed nested-join families now connect support, diagnostics, both sampling
routes, weights, flags, complete inverse queries, and original occurrence
metadata. `RecursiveCompleteRecord` assembles those fields. Arbitrary opaque
Haskell builder schemas, key-discovery behavior, codecs, and lazy productivity
still require their stated contracts. Generator members remain distinct from
unique accepted FTA terms.

Full sparse Yes transports to complete logical satisfaction. Current pruning
and successful compiler classification inherit logical safety and exactness on
the success domain. A sound name-sensitive backend can still return sparse Yes
and complete Unknown. Exact backend-confirmed language equality requires
backend adequacy. The all-Int adapter derives its laws from correctly returned
external responses. See [logical read transport](lean/notes-source-read-logical.md)
and [the integer adapter](lean/notes-source-read-integer-adapter.md).

Runtime identity lifetimes, machine words, host containers, concurrency, lazy
productivity, solver IO, PRNGs, and user codecs retain explicit correspondence
contracts. There is no verified Haskell-to-Lean extraction. Similarity
minimization preserves representatives, and pool minimization starts a new
uniform distribution; neither implies exact term/mass preservation under the
stronger requested contract.

These boundaries prevent a whole-implementation verification claim. Resume
from [HANDOFF.md](HANDOFF.md), using [NEXT-PROMPT.md](NEXT-PROMPT.md). Keep the
proof checkpoint, source fixes, and all restart material local.
