# Full formalization coverage

The current preserving PR #122 rebase is `fc81eacf` on `3ea4a9d8`.
All 1,732 saved Lean-tree files matched exactly. Upstream memoizes synthesis
terms by flag, size, and ordered argument names. No Sized or interned
runtime code changed. The synthesis application has no complete formal
source model. Earlier proof hashes remain in the preserving backups.
PR #121 qualified the raw-binder identity comment. The smart-only identity
law is still unproved. See root HANDOFF.md for exact evidence.

Current checkpoint: **2026-10-14 19:20 CEST**, upstream `3ea4a9d8`.
The latest proof commit is `ddef16e6`, after `f04b8261` and `4d80735a`. No background proof worker is active.
The requested rebase preserved all saved proofs, drafts, and fixtures.

`SizedLanguageTheorem` proves exact distinct accepted node-count classes,
finite reference evaluation, complete size-major prefixes, and both inverse
laws. `SourceSizedFiniteKeys*` now derives the actual validated finite map
carrier, raw rows, canonical order, trim keys, bounded folds, and relational
traces even when the original state type is infinite.
`SourceSizedFiniteKeysDispatch.nativeSized_eq` proves complete raw dispatcher
agreement, including all four queries and errors. The finite raw product
minimum gate is derived. See [finite map Sized](notes-sized-finite-keys.md).

`TablePositionCountBound` proves that optimized ranking reads no count above
the input term's node count. `TablePositionFiniteEvaluation` constructs finite
count and child maps with the exact original result, including failure.
`SourceSizedFiniteKeysRankEvaluation.native_rank_laws` connects that finite
computation to the actual public inverse and both signed inverse laws.
The original state type need not be finite.

`SourceSizedFiniteKeysNativeLiquid.encoded_correct` connects the actual raw
fold to independent mixed-sort ambient logical acceptance and the canonical
bounded sequence. `encoded_finite` derives finite outcomes from finite
external attempts, including Unknown and unchanged exceptions. Replies may
vary. `SourceSolverNameFastEncoding` proves upstream's current two-form codec.
The historical decimal codec remains. `SourceSolverName*` proves serializer control,
quantified meaning, preparation, and public composition for repair `73223201`.
That repair prevents distinct raw names from capturing a quantified variable
in the solver. The prior ambient freshness repair also remains.
See [solver names](notes-solver-name-encoding.md).

Shared row traversal, dense numbering, minimum sizes, cyclic query records,
sampler/PMF records, normalization, support, and sampled replay are derived.
Equal complete custom sort keys retain source order. See
[shared rows](notes-shared-rows.md).
`SourceQuickCheckFrequency*` now derives actual cumulative selection,
ticket probabilities, Exact mixture agreement, and weighted rank replay.
Repair `a8b32869` removes index-sum overflow. See
[weighted selection](notes-quickcheck-frequency.md).

Ordinary native intersection dispatch, physical cache effects, completed
memo provenance, shared traversal, and minimum callbacks are now proved.
The productive single-knot fragment now has actual empty-cache construction,
exact returned records and counters, stable replay, unfolding, and shared exposure.
`SourcePhysicalRecursiveSized` derives its singleton positive-size classes, finite
evaluation, size order, and both inverses. The first-order extension now derives
actual repaired construction, a prepared heap, finite cold single-root exposure,
and fixed-cache shared rows for arbitrary binder-free trees and unions.
`SourceFirstOrderSharedRows.source_sized` proves exact distinct size classes,
finite evaluation, size order, bounded coverage, and both inverses after explicit
finite warmup. Equality between warmup and native cold allocation orders remains open.
See [first-order shared rows](notes-first-order-shared-rows.md).
`SourceColdSharedRows*` now derives finite cold traversal and exact returned
physical guarded language for closed available roots in prepared caches.
`SourceFirstOrderColdSized` derives preparation from actual repaired construction
and proves the complete reference Sized laws without warmup or a supplied trace.
The actual returned table connects to canonical native dispatch and encoded
solver-decided execution, including finite classes and both signed inverses.
Validation and external solver contracts remain explicit. See
[cold shared rows](notes-cold-shared-rows.md).

`SourceRecursiveIntersection*` now derives full physical guard order,
tagged operand comparison, independently sorted cutoff pairs, typed
canonical domain overwrite, original Mu record lookup, and domain-cache
allocation. The complete branch selector and next semantic computation
are connected. Physical-to-view closedness equations remain explicit.
See [recursive control](notes-recursive-intersection-control.md).

`InternedFreshOrdinaryPlanEquivalence`, `InternedStoredSubstitutionRebind`,
and `SourceRecursiveIntersectionMaybeMu` derive full nested stored-plan
rebinding and the exact actual optional-binder executor. They retain
probes, fresh ordinary names, pending keys, source facts, histories, and
replay. Prepared callbacks and probes complete without whole-cache
coverage. The exact pending result is an installed post-probe key without
a payload. Complete cache coverage gives successful prepared construction.
General open nested completion, result preparation, product language,
pending cyclic memo publication, and product-row readback remain open. See
[optional binder effects](notes-recursive-intersection-maybe-mu.md).

`SourceRecursiveIntersectionKernel*` composes the full uncached recursive
caller with actual domain, optional-binder, union, and guarded row effects.
`execute_checked` derives complete cache invariants and available successful
results. `execute_stable` preserves non-exhausted outcomes and exact caches
at larger bounds. Actual request traces derive conjoined guard fields, child
records, and canonical surviving rows. Completed native memo effects are
connected below. Successful first-run bounds under checked words are now
derived. Physical product-row correspondence remains open. See
[recursive caller](notes-recursive-intersection-kernel.md).

`SourceRecursiveIntersectionReplay*` proves completed guarded kernel replay
after physical and domain growth without changing either later cache.
`SourceRecursiveIntersectionMemo` derives exact request identity from checked
native machine triples and actual current records. Concrete completed
executions supply first-writer memo provenance and stable hit replay.
The nonnegative first-key bound and distinct swapped keys are checked.
`SourceRecursiveIntersectionEdgeMemo` extends concrete provenance and stable
replay to checked raw row keys. `FlatMemoThunk` and
`SourceRecursiveIntersectionThunks*` derive typed pending publication,
original request identity, recursive pending observations, demand, completion,
and retention through source growth. Completed native observations recover
concrete kernel replay. `SourceRecursiveIntersectionCode` and
`SourceRecursiveIntersectionCompile` now compile all physical guarded branches
and derive exact kernel agreement. `SourceRecursiveIntersectionNative*`
threads both memo families through recursive bodies. Request steps,
continuation composition, finite actual traces, and physical-effect retention
are checked. Actual finite completed runs and nested evaluations now agree
in both directions. Completed source bodies preserve structural memo `Shape`
and all enclosing running requests. Their original frame stores the actual
returned value in the original cell. Full completed native kernel correspondence
and semantic memo provenance are now derived under explicit checked word
bounds. `Bounds.correct` derives strong validity, exact physical/domain growth,
available results, stable kernel meaning, and new `Produced` from actual native
bodies. Public node/edge and empty-memo theorems start from actual native
completion. The original physical input view now derives exact payload
readback, cached free-name equations, original-input closedness, physical
branch agreement, and copied closedness. Actual payload ranks supply strict
structural decreases. Closed-root reference traversal retains original
available records inside a finite carrier bounded by the issued counter.
The carrier gives finite input pairs. `Original` remains an explicit input
premise. Actual canonical representatives and both independent copied-language
directions now derive the complete finite input interface. The semantic
schedule terminates with exact product language for actual closed original
records. Original input-view fields remain exact through source growth.
Least successful request bounds now strictly decrease through every immediate
call. Canonical domain allocation retains these bounds. Completed native
source bodies leave no new running cells, and original frames restore caller
cells. Active-bound lifecycle and conditional absent/busy exclusion are proved.
All compiled branches and continuations now retain original scope and strict
request limits. Successful semantic actions exclude explicit source failures.
Word checks on actual finite yielded prefixes supply completed range
certificates. Strong bound induction and structural code induction derive
`cold_node_terminal`: a finite native return or exact pending constructor
from closed original roots under checked words. Absent handles, busy cells,
source failures, and yielded outcomes are excluded from `ReturnsOrPending`.
Original completed frames derive new provenance and restore caller bounds.
No completed native trace or body termination contract is supplied.
General successful completion still needs pending-constructor exclusion at
the actual reached source states. Coverage now holds through all actual
yielded prefixes. Earlier actual completed repaired source construction
supplies complete incoming coverage. Constructor blocks derive their exact
source site and pending callback phase. An incomplete final hit after two
successful probes is excluded. Full repaired nested encounters recover both
original ancestor probe records and its newly captured reference.
`SourceRecursiveIntersectionMaybeMu.pending_encounter` connects the source
call to that witness. The repaired ordinary callback uses `ordinaryLevel depth`.
Full active paths now retain arbitrary captured values and both exact old
probe records. The two probes derive equal captured free-name memberships.
Every live interned capture predates the ancestor reservation. Its fresh name
is absent. The actual optional-binder bridge requires an incoming full repaired
semantic context. The later native no-constructor proof derives the needed
context at each actual blocked source site from completed-body preservation.
Actual earlier completed routes now retain both repaired probes and a
completed request payload before the ancestor reservation. That earlier pair
differs from the later original pair. Captured values can be arbitrary records.
Exact repaired live-input comparison now covers arbitrary fixed captured
values. Common symbolic profiles derive actual child liveness. Equal surviving
varying references give equal complete returned records in a coherent common
cache. An earlier completed binder and actual later probes derive request
readiness. Actual callback free-name observations expose every live varying
capture. Pending execution now derives an actual ordinary mismatch on the
same earlier route. Fresh interned changes are excluded. The current level is
free in the ancestor's old Depth probe, lies strictly below its ordinaryLevel,
and comes from an actual captured value. Rooted source paths now derive actual
shorter producers with full contexts, completed Depth callbacks, chosen levels,
cache histories, descendant paths, and exact captured suffixes. `StoppedReached`
retains the actual pending equation of every enclosing callback. `PendingProducedAt`
adds the shorter producer's pending ordinary callback and pending binder outcome
at the same exact key and cache. Closed empty-input pending execution has no
initial-capture alternative. Actual optional binders
retain an initial-body free-name alternative. It is excluded only under the
explicit absence of ordinary free names in that body, which is not yet derived
at all native sites. A second actual observation of the shorter producer's same
body remains open for the retained producer-descent alternative. Closed and
literal-input source completion now uses actual paired-route agreement below.
The shorter prefix alone does not establish contradictory recursive descent. A repaired dead-branch
example also excludes transfer of descendant liveness to the producer result.
Native prefix preservation of the full semantic context remains open.
An actual 22-step native prefix on repaired closed original source-built inputs
refutes preservation of `PreparedWithoutMu` at every optional-binder body.
Bounded execution of that example returns. This is a proof-invariant boundary,
not an implementation defect. A broader open nested constructor invariant,
output preparation, and physical product rows remain open.
See [constructor coverage](notes-recursive-intersection-constructor-coverage.md),
[finite native observations](notes-recursive-intersection-native-finite.md),
[request progress](notes-recursive-intersection-request-progress.md),
[exact original inputs](notes-recursive-intersection-input-exact.md),
[physical input view](notes-recursive-intersection-input-view.md),
[recursive memo](notes-recursive-intersection-memo.md),
[native memo thunks](notes-recursive-intersection-thunks.md),
[native recursive execution](notes-recursive-intersection-native.md),
[native completion](notes-recursive-intersection-completion.md), and
[native correctness](notes-recursive-intersection-native-correctness.md).

Arbitrary-record source construction now has exact cached-depth/deep
observations and successful completion in complete coherent decoded caches.
`InternedRecordDepthShape` derives the complete input observations from actual
records. `InternedRecordDepthExecution` proves the source induction; the old
literal driver specializes it. `InternedRecordDepthLevels` and `Routes`
derive equal actual ordinary choices along both scoped routes.
`InternedRecordDepthCompletion.source_complete` excludes pending construction.
`SourceRecursiveIntersectionMaybeMuCompletion.complete_decoded` composes actual
stored substitution and arbitrary available leaves without preparation. It
retains the semantic context, decoded depth heap, coverage, availability,
growth, and issued history. `SourceRecursiveIntersectionCompileSemantic*` derives the semantic conditions
of every actual compiled branch. `NativeSemantic.Bounds.semantic_heap`
preserves complete semantic heaps through actual completed nested evaluation.
`NativeNoConstructor.no_constructor` follows unfinished body/continuation
splits and excludes pending constructors. `NativeSuccessful.cold_node_complete`
derives successful stable first native execution for closed Original available
inputs from complete semantic caches under explicit `WordRanges`. Exact
returned caches, guarded kernel meaning, strong memo provenance, semantic
heaps, and coverage are retained. `constructed_node_complete` derives initial
semantic heaps and coverage from actual repaired closed source construction.
Native output scope and a broader bounded cold-reader invariant are now
proved below. Finite final cold tables and physical product rows remain open. See
[record completion](notes-record-depth-completion.md) and
[successful native execution](notes-native-successful.md).
`InternedFreeNameIndexedOrigins` and `InternedStoredPlanFreeSupport` derive
exact used lexical free-name origins and original support outside local
binders. `MaybeMuFreeSupport.free_support` and `pair_absent` derive actual
intersection-name elimination. `InternedFreshOrdinaryStoredFreeSupport`
derives free names from actual replacements of original free references.
`InternedFreshOrdinaryUnfoldCompletion` derives general stored substitution
and single unfolding without preparation, retains complete semantic caches,
and proves closed unfolding. Repeated cold-reader termination remains open. See
[stored support and unfolding](notes-stored-free-unfold.md).
`SourceRecursiveIntersectionKernelScope.execute_scoped` derives actual
source result scope from incoming seen pairs. `NativeResultScope` derives
native output closedness through exact guarded meaning and the empty domain.
`OriginalOutput` derives original payload syntax from coherent availability
and closedness. `MergedFreshOrdinaryColdEffects` proves full semantic cache,
coverage, growth/history, resident edges, and closed children for every
bounded repaired read without preparation or `NoNewMu`. Pending construction
and unresolved references are excluded. `NativeColdEffects` derives these
premises from successful native first execution. Exhaustion remains possible.
Physical finite closure and exact product language remain open. See
[native output and cold effects](notes-native-output-cold-effects.md).
`MergedFreshOrdinaryColdReplay` proves validity/growth for every bounded
repaired read, exact completed-read replay after cache growth, and larger
bound stability. Replay requires only initial validity and an actual done
result. `SourceColdUnfoldNewMuBoundary` refutes two proposed general measures
with actual closed source construction: one unfolding allocates a new Mu and
increases cached depth from 2 to 3. The reader still finishes. Live Haskell
confirms the depth increase and successful read. This is no source defect.
`SourceFreshOrdinaryColdSharedRows` defines the shared worklist with the
repaired reader directly. Finite traces and actual executable runs have
identical tables and caches. Both prepared trace bridges are derived.
General finite traces retain complete semantic caches, coverage, row
provenance, growth/history, and closed children without preparation.
`SourceFirstOrderFreshColdSized.source_sized` connects actual repaired
empty-cache first-order construction and repaired cold shared execution to
all exact finite reference Sized laws. General nested finite trace existence
remains open. See [repaired shared rows](notes-fresh-cold-shared-rows.md).
`InternedStoredRawIdentityBoundary` refutes unqualified physical identity
substitution for an open raw binder body from actual closed construction.
The smart stored rebuild removes one unused raw Mu and changes identity.
Free names remain equal. Kernel and live Haskell observations agree.
Runtime behavior was not changed. General closure must include this cleanup.
`InternedFreshOrdinaryDependencies` derives exact repaired plan congruence
from used slots and original free bindings. `InternedFreshOrdinaryBindingKeys`
recovers full available replacements from physical key equality, derives
exact computation and replay, and supplies finite keys for closed current-
cache replacements. Future new closed values are not bounded by this result.
See [repaired binding keys](notes-fresh-binding-keys.md).
`InternedStoredPlanBinderDepth.encode_depth` derives exact binder nesting
of the actual stored plan while treating closed captures as constants.
Actual callback crossings respect that static budget. Zero depth is exactly
binder-free execution and cannot add Mu records. Actual normalization
preserves open-depth bounds. `InternedStoredPlanBinderDepthOne` proves that
closed depth-one unfolding gives every newly allocated Mu a zero-depth
body. The entire returned cache is covered, including probe allocations.
Earlier records and closed captures can have arbitrary cached depth.
`InternedOpenDepthExecution` now derives exact actual source depth and
body/Depth-probe equality for complete Mu records.
`InternedStoredPlanBinderDepthProgress` proves strict body-depth decrease
for every new Mu after general closed unfolding, including all probes.
Actual empty-cache construction derives its heap premises. Subsequent
stored execution and unfolding preserve the new heap.
`InternedMuDepthInventory` counts actual canonical Mu identities by body degree.
`MergedFreshOrdinaryColdTermination.collect_complete` proves finite actual
closed worklist execution with new lower-depth Mu allocations.
`read_closed` proves successful public reads with exact returned edges/cache,
retained semantic and body/probe heaps, coverage, and larger-bound stability.
`constructed_read_closed` derives all premises from actual source construction.
`InternedFreshMuUnfoldBudget` and `MergedFreshOrdinaryColdBudget` derive
strict unfinished-degree progress or identical caches for actual closed reads.
`SourceFreshOrdinaryColdSharedTermination` proves general finite shared
traversal and stable uniform bounds from actual closed source construction.
`SourceFreshOrdinaryColdTable` derives exact finite ascending map domains,
declared nonempty children, and exact allocation-free final-cache row replay.
`SourceRecursiveIntersectionNativeOpenDepth` retains both heaps through
actual nested native evaluation. `NativeColdTable` derives finite stable
native-output tables from checked words and closed Original inputs.
`MergedFreshOrdinaryExposureLanguage` proves exact actual repaired epsilon
origins and full guarded row language. `SourceFreshOrdinaryColdTableLanguage`
identifies the complete table with the repaired graph in its final cache.
Both native cold-table entry points return that language equation.
`InternedGuardedLanguage` and `InternedGuardedSyntax` define independent
positive least-language meanings. Actual coherent free-name support, ordinary
normalization, smart cleanup, raw/smart finish, and callback root filtering
retain these meanings. `InternedGuardedStoredPlan` proves exact arbitrary
nested compilation, simultaneous-substitution plans, and outer-Mu plans.
`InternedGuardedSyntaxSupport.evaluate_related` proves semantic support for
surviving source captures. `InternedGuardedExecution.build_language` derives
actual execution language and semantic probe-heap preservation together,
including fresh completion, canonical hits, and pending outcomes. Actual
stored substitution and outer-Mu unfolding preserve independent language in
`InternedGuardedStoredExecution`. The new semantic probe heap also propagates
through actual bounded cold reads and finite shared tables.
`SourceFreshOrdinaryColdGuardedSoundness` proves final graph/table inclusion
into independent meaning. Native optional binders have their least-language
law. Native evaluation retains the new semantic heap, and its finite table
is sound for the returned value. `SourceRecursiveIntersectionGuardedInput`
identifies original stored meaning with copied lexical meaning and finite
input derivations. `InternedGuardedBudget` interprets complete stored records
at each Mu-unfolding bound. Actual ordinary normalization preserves each
budget. Cleanup retains terms without increasing it, and root-self filtering
preserves the budgeted least language. `SourceRecursiveIntersectionBudgetExact`
proves exact actual input derivations at each bound for closed available
Original records. Erasing the bound recovers independent meaning.
`InternedGuardedBudgetStoredPlan` proves exact raw compiler and substitution
budgets. Each accepted Mu has its exact compiled unfolding plan at a strictly
smaller bound before execution. `InternedGuardedBudgetExecution` now proves
exact actual smart budgets through both probes, fresh completion, canonical
hits, and pending heaps. The new invariant retains raw-Mu and empty-local
ordinary-probe languages. Actual stored substitution/unfolding retain both
heaps and have their exact smart-plan meanings. `a7b5d94e` proves raw-to-smart
plan inclusion and strict budgets for actual returned unfolding. `9ca74b4d`
proves cold/shared budget heaps, complete final graph/table language, and
general closed-source reference Sized laws. `081ce3d1` proves native budget
heaps and exact independent returned-value table language. `2e6fb87a`,
`6afdfe00`, and `dac5f26b` prove literal ordinary product-row membership,
complete guards/child order, dead-row rejection, and native closed diagonal
reuse. Native ordinary rows hold at all larger bounds and later valid caches.
A live ranked Mu witness refutes the general functional child-map adapter.
`RelatedRows` and `DiagonalProduct` now prove exact product language from
local related rows, with diagonal reuse and explicit deletion reasons.
Actual native ordinary calls derive local row relations. The relational
minimum callback and compiler retain finite classes and both rank inverses.
The observed finite Mu transcript has a full unbounded language proof and
a formal obstruction to the functional adapter. Haskell extraction remains
unverified. Derive related roots and row closure through actual Mu and union
calls. Full native two-input language remains open. See
[related physical product rows](notes-relational-product-rows.md),
[ordinary product rows and the identity boundary](notes-ordinary-product-rows.md),
[cold budget completeness](notes-cold-budget-completeness.md),
[smart budget execution](notes-smart-budget-execution.md),
[unfolding budgets](notes-unfolding-budget-language.md), and
[guarded compiler semantics](notes-independent-guarded-language.md).
A finite exploratory search found no
counterexample, which is validation only. See
[stored-plan binder depth](notes-stored-plan-binder-depth.md).
The [equality root proof](notes-equality-nested-unary-root.md) now composes both
ancestor edits and bounded iteration for the fixed unary/two-atom fragment.
General equality propagation remains open.

The [bounded import proofs](notes-bounded-import.md) remain. Native SCC/split
readback, custom import decoder order, concrete containers, lazy execution,
external solver/PRNG contracts, codecs, and verified extraction remain
boundaries. The handwritten source models do not verify the whole library.
Benchmark programs, datasets, and workload specifications are excluded.

The current audit passes **1,470 targets and 43,899 theorem dependency checks**
with only `propext`, `Classical.choice`, and `Quot.sound`.
After PR #122, all 208 generator and 145 refinement examples pass. The
unchanged core retains its earlier 289 passing examples. Fourmolu and active-package cabal-gild passed.
The broad gild check reports existing formatting failures in the unchanged
legacy microecta package files. No new production test was added locally.
See root [HANDOFF.md](../HANDOFF.md) and [FINDINGS.md](../FINDINGS.md) for exact
contracts, checkpoints, validation logs, and remaining priorities.
Everything remains local. No further push, deployment, or board post is
authorized. Stop all work at 1% weekly allowance remaining or less.

## Objective and completion rule

Formalize the complete microcfta design in Lean. Prove that generation covers
all required terms, that sampling has the specified probabilities, and that
each optimization preserves its stated semantics. Keep the correspondence to
the actual Haskell algorithms explicit. Record implementation errors while
continuing the other proof work. Report the findings at the end.

This ledger distinguishes system modeling from complete implementation
verification. Every source module has an explicit semantic role and boundary.
Passing builds, theorem counts, and finite examples do not verify the whole
implementation. A proof row is complete only when its executable algorithm
has a checked semantic theorem and its implementation correspondence is
established. A theorem whose main algorithmic obligation is a premise
does not close that obligation. An implementation counterexample prevents a
soundness claim for that path; it does not remove that path from the scope.

Source baseline: `origin/microcfta` at `7989e91a`. This includes the merged
core-formula changes at `9ad319d`. The detailed semantic specification is in
[SYSTEM.md](SYSTEM.md); root findings record the current changes. All 71 source modules
are inventoried in [API-COVERAGE.md](API-COVERAGE.md).

Current update: PR #97 adds merged peer projections to equality narrowing.
The new `MergedProjectionBound` covers the complete physical projected-leaf
schedule with that operation. The previous worker retains its separate proof. Full nested
free-name interpretation and the global decoded free-name heap are now
proved, including historical literal-probe boundary exclusion. General
Mu-boundary replay remains open. First-run no-pending is false for the
old protocol; it remains open for the repair. See root
[FINDINGS.md](../FINDINGS.md) for current status and validation.

Current continuation proofs add full live lexical input replay and actual
completed probe-choice sites. They derive guarded merge-call descent, physical
comparison and union language, and stabilization of cold unfolding traces in
the `PreparedWithoutMu` fragment. Closed cold edge exposure now completes,
retains cache facts, and has exact finite-term semantics in its actual returned
cache. Ordered stateful comparison has sufficient-fuel completion, exact fuel
stability, and successful trace replay in every later cache. The cold ordered
child filter also has stable completion. Adaptive merge has complete language
coverage and exact fuel independence under its prepared context. Its full
cold-filter composition now has completion and actual-cache language coverage. A hypothetical closed pending encounter
now requires different computed ordinary levels at a live lexical position.
The later name is a live capture of the active ancestor and occurs in its
original Depth probe. Its actual earlier introduction now has a derived
shorter lexical context. A checked closed example prevents exclusion from
alias support alone. Stateful comparison and child selection now have
actual-cache soundness. The complete cold merge now has derived completion,
language coverage, and exact two-fuel stability. Constructor alias exclusion
remains active. Executable source grouping also has a derived structural
contract and an exact append-fold bucket equation. PR #102 adds interned
intersection domains and flat memo storage. PR #103 adds cached expandable
and waiting UVar indexes. Their derived models now prove masked table probing,
first-writer retention, copy/growth, bounded memo-key identity, exact maintained
indexes, and unchanged scheduler selection. Signed waiting updates derive all
intermediate bounds from the initial/final counts. Raw runtime primitives,
concrete containers, typed families, and machine-range bounds remain explicit.
Original cold-cache language transport is now proved. Exposure, comparison,
selection, and merging have pre-effect semantic statements. Complete root
row bounds include arbitrary source bucket order. Repeated source merging
on finite ordinary trees reaches an exact value-and-cache fixed point
within original ordinary height. General equality schedules still need
intervening intersection/edit progress. Exact indexed producer paths and
pending callback equations strengthen constructor provenance; general
paired-key descent cannot exclude the preserved closed pending example.
The old constructor protocol's general completion claim is now refuted by
`InternedClosedPendingBoundary`. Local source repair `e0e1b37` selects a
placeholder above the Depth observation's free ordinary names and uses the
same stored observation for readback. `InternedFreshOrdinaryConstruction`
proves freshness, minimality, and matching readback. Kernel computations
verify both repaired fixtures. Native probes and 620 source examples pass.
Repaired Facts, normalization, source origins, stored readback, root profiles,
and free-name semantic heaps are now derived. Closed completed outputs have
no free names. The source chooser fold agrees under explicit machine bounds.
General repaired completion and unrestricted source correspondence remain open. Earlier
ordinary-name-specific theorems describe the preserved old executor and
need a new bridge before they establish repaired-source correspondence.
See [the repair](notes-fresh-ordinary-candidate.md) and root
[HANDOFF.md](../HANDOFF.md) for exact boundaries and evidence.

The latest physical equality work derives admitted leaf readback, identity,
intersection, and projection union. A normalization phase handles arbitrary
initial outer guard syntax. Physical raw construction preserves rejected
sentinel requests and derives whole-node identity from the accepted row set.
Physical Cartesian intersection derives exact raw readback and strict rank
decrease. Its generated finite carrier preserves initial raw guard syntax.
Finite occurrence compilation and recursive workers derive complete payload
availability and readback. Ordinary occurrence trees now have exact complete
recursive required-path correspondence. Physical leaf
intersection and projection union have finite-cache record correspondence;
physical path projection derives completion and available payloads. Endpoint
projection, simultaneous edit, and schedule composition remain open.
Full nested construction derives pending-reservation origins, complete old probe footprints, pending
preservation, and earlier readback of old identities. The remaining general
completion claim for that old executor is refuted; recursive erased-edge
construction already completes at arbitrary depth. Structural erasure and
mixed retained/erased source contexts also derive first completion.
The unfolding rank depends only on reachable shallow values.
Unrelated deep cache records are allowed;
arbitrary nested Mu bodies remain open. Separate actual completion and strict
decrease results allow arbitrary-depth closed Mu children in ordinary bodies.
Source marker provenance also admits open nested records for one-step
completion and decrease. General repeated unfolding remains unresolved.

The upstream base includes the seventeen earlier repairs. This continuation
also repairs same-scope identity-replacement precedence and recursive
construction payload queries. Formula substitution
preserves bound application names. Observed atomic members retain their
within-size weights. Minimization installs and checks accepted root
representatives. Open unions retain epsilon operands. Pruning inspects stored open binder bodies before following recursive reads.
Grouped private alternatives now close in agreement with decoder terms.
Recursive members retain one private boundary in every structural record.
Grouped function spines retain each alternative's correlated children.
The evaluator rejects uncertain enclosing renames and identity-precedence
changes before sparse substitution can discharge their guards.
Canonical conjunctions stop the reproduced acyclic equality-reduction loop.
The public Boolean guard entry now allocates each outer operand independently.
Recursive equality classes remain enforced when the current constrained-recursion gate skips narrowing.
Observed imports now expose explicit union alternatives instead of dropping them.
Recursive observation groups retain their size indexes during key filtering.
Bounded construction now exposes retained binder cycles with the visited closure.
Measure callers now reject self-dependent extracted values.
Open group positioning now reads recursive keys without a cardinality query.
Unfinished recursive occurrences keep independent construction tokens.
Payload queries reject them consistently across rebuilding phases. Nested
completion preserves enclosing tokens and removes the completed token.
Grouped recursion validates the discovered table against its final probe.
Typed constructor programs pass this check with their previous exact minima.
Existing suites pass 284 core, 194 generator, and 142 refinement examples on `de910ea`. Historical
counterexamples remain checked against their explicitly named baseline
models. The positive repair theorems are separate.

## Coverage ledger

| Area and source modules | Checked foundation | Source correspondence and remaining work |
| --- | --- | --- |
| Term/path semantics: `Path`, `Term`, `Internal.Tree`, `Generic`, `Simple` | `Language`: finite runs, bounded enumeration, path lookup, equality sharing. `TermRepresentation`: all small-arity constructors, invariant, round trips and lookup. `TermOperations` and `ChildBuilder`: complete indexed construction, edits, preorder traversal and arbitrary folds. `LevelEnumeration`: first-deepest split, exact next level and safe empty-level stopping. `BoundDepth`: exact graph rewrite. `Construction`: nested constrained grammar compilation and finite state closure. `Generic`: terminating finite descriptor discovery, exact language, growth/domain failures and codec rank laws. `Template`: all five patterns and exact graph restriction. | Concrete sequence/hash storage, GHC generic type metadata, binder conversion and public wrapper correspondence. `FTAValidation`, `FromTerms`, `GraphTrim` and `StateMap` now verify the explicit graph operations. |
| Constraints: `Constraint`, `Equality.Constraint`, `Refinement.Guard` | `Guards`: Boolean evaluation and splitting. Concrete trie construction, ordered paths, prefix checks and descent. Canonical connected components and congruence saturation. Unconditional termination, exact semantics, constructive finite models, and rejection iff no model exists. | `SourceGuardSplit` proves the current semantic/residual split for every constructor and all three verdicts. `ConstraintIndicators` proves the whole supported signed compiler. `SourceEqualityGuards` derives its exact indicator from the current complete evaluator, including missing equality paths. `SourceIndicatorCompiler` connects every successful full-Guard compilation to that law and preserves exact unsupported errors. `ArrayUnionFind`, `EqualityArray` and `ArrayBounds` now prove concrete array workers, complete class iteration/readback/grouping, connected components, finite execution and index bounds. `EqualityIndex`, `EqualityPartition` and `EqualitySource` close path allocation, canonical readback and repeated array normalization. Physical storage, residual guard decisions and public arity wrappers remain. `EnumerationState` models suspended-path scheduling separately. |
| Interning and recursion: `Interned.Type`, `Interned.Operations`, `Interned.Cache`, `Interned.Memo`, `Interned.FlatMemo`, `Interned` | Synchronous graph intersection in `Language`. `Cache`: fresh identities, first-writer insertion, finite interleavings, memo results, sharding with collisions. `Binding`: free-variable dependency, restricted environment cache keys, identity substitution and depth-probe distinction. `BoundDepth`: exact graph copy. `OpenUnion`: historical loss and repaired witness. `EpsilonUnion`: terminating depth-first closure and exact epsilon elimination. | `FlatMemo*` proves masked probing, physical insertion/copy/growth, and stale-reader retention. `IntersectionFlatMemoKey*` derives bounded node/edge key and structural-domain correspondence. `InternedIdentityWords` derives finite-word freshness within one allocation period and proves wraparound repetition. Runtime map/atomic/type-cast correspondence, fresh binder alpha-renaming, the SCC/lazy-map conversion adapter and lexical-to-runtime identity correspondence. `IntersectConstruction.constructed_intersection_total` derives termination and exact language from a finite payload-completion trace, cached free-variable equations, canonical identities, and exact closed copying. Sizes, finite identity sets, reference coverage, and closed reachability are derived. `IntersectInput.finite_intersection_exact` proves every successful recursive intersection against independent finite input derivations. `IntersectDomain` proves lookup coverage, and `IntersectProgress` proves local progress between resets. `BinderCycles.cycles_closed_total` proves total exact cyclic graph-to-binder construction from complete cycle marking; `BinderComponents` proves component sharing. `RedundantEdges` and `GraphRewrite` prove complete row reduction and cyclic graph preservation. `BinderLanguage` proves least-language unfolding and both cleanup cases. `EnumerationBinderExposure` proves closed self-unfolding, exact successful exposed rows, and that raw Rec is unreachable from a closed input. `LexicalBinderClosure` derives finite lexical closure and visited row exposure. `InternedBinderRebuild` derives the prepared binder substitution, fresh alpha replacement, cleanup, and closed exposure from syntax. `InternedSubstitution` derives the full nested worker, fresh allocation trace, exact open-environment language and closed unfolding. `InternedBinderProtocol` derives the source two-probe key, exact replay after cache growth, and restricted binder memo readback. `InternedConstructorTemplates` derives ordinary/union requests, cached metadata, enclosing Mu completion, and whole-record identity replay. `InternedRecordCoherence` derives global key/record coherence, complete readback and finite record inventory from empty construction traces. `InternedStagedBinders` derives nested dependency-first construction and the stable finite identity family after one root build. `InternedFreshProbeKeys` derives fresh-reference key separation and originally irrelevant-variable memo replay. Dependency erasure during normalization, full fresh-outer-dependent nested completion, and stable lexical-to-runtime identity readback remain. |
| Enumeration: `Enumeration`, `Internal.UnionFind`, `Equality.Operations` | `Language`: reference enumeration and sharing. `UnionFind`: exact terminating state operations. `Fragments`: hole resolution, slot intersection, assimilation, and combined union/assimilation assignment semantics. `EnumerationState`: complete fuelled caller, suspended paths, expansion ordering, ancestry cutoff, witness accumulation and rendering, with source behavior examples. | `Enumeration*Index*` derives the cached indexes from every mutation and proves the exact indexed selection. `EnumerationWaitingMachine` derives bounded signed updates. `EnumerationCorrectness` derives storage, allocation, union/assimilation semantics and concrete renderer soundness. `EnumerationSchedule` and `EnumerationDriver` prove the entire caller storage/live-root/alias invariant and completion state. `EnumerationSoundness` proves complete caller assignment simulation and acceptance. `EnumerationProgress` derives no-stuck expansion under a satisfying assignment. `EnumerationAssignment.runs_sound` constructs final assignments and proves actual-run acceptance under returned residual checks. `EnumerationExact.runs_exact` proves actual initialized finite-term support in both directions, including final rendering and sufficient stable execution bounds. `EnumerationConstructors`, `EnumerationIntersection`, and `EnumerationEquality` derive complete graph and intersection invariants from source rows and equality normalization. `EnumerationBoundedRows` proves exact depth copying. `EnumerationBuilderFastPaths` derives exact finite memo traversal, two-stage edge/node interning, sorted/deduplicated identity readback, terminal fast paths, and bounded language. `EnumerationBinderExposure` derives closed self-unfolding and exact successful rows. `LexicalBinderClosure` derives the finite lexical request domain and exact visited row exposure. `LexicalExposureLanguage` derives its exact least language, and `LexicalBoundedBuilder` connects the concrete memoized builder. Runtime binder interning, alpha-renaming, cleanup, and general pruning callbacks remain adapters. `AcceptanceDispatch`, `AcceptanceEffects` and `AcceptanceSoundness` prove the Boolean worker, both caches, adaptive Unknown handling and sound definite verdicts. Truncated runs are not the complete finite denotation. |
| Refinements: `Refinement.Evaluate`, `Expression`, `Verdict`, `LiquidFixpoint`, `Denotation`, `Automaton`, `Template` | `CoreFormula`: exact integer semantics, simplification, substitution and free names. `FullSyntax`: all current constructors, sorted/quantified interpretation, actual substitution counterexample, exact successful-lattice fragment extraction. Verdict laws, first-formal aliases in `Holds`, and exact template restriction. | Raw-AST sort validation, primitive target theories, serializer/solver IO and complete refinement-evaluator correspondence. Full syntax substitution, alpha-renaming, simplification and target lowering are proved. `FormulaExecutable` connects structural comparisons to the simplifier. `RefinementValidation` proves finite reachable structural validation and all signed path endpoints. `SolverAdapter` proves source query preparation, declaration coverage, response handling, and returned-verdict soundness under correct external solver answers. `SourceFormula` instantiates the full guard backend; `SourceEntailment` proves name-identification transport and its necessary negative-verdict boundary. |
| Pruning: `Refinement.Prune` | `Observation` and `ObservationGraph`: executable path plans, exact sparse views, graph variants, all-finite-term specialization coverage, homogeneous refinement decisions and successful guard discharge. `PruneSchedule`: source decision loop, ambiguous-actual restoration, unknown error, recursion bypass, bottom-up cache/binder driver. | `PruneCorrectness` proves the full successful mutual schedule and cache invariant. `PruneCandidates` derives candidate semantics and Unknown restoration from concrete specialization. `PruneMemo` and `PruneDependencies` prove split-memo coverage and dependency-local cache transport. `PruneReads` proves the repaired recursive gate. `SourceGuardRefinement` derives decided sparse/complete agreement from unambiguous source tables. `SourceGuardPlan` proves actual trie/read adequacy and `FullGuardPrune` connects every current Guard constructor to exact successful conflict-free specialization. `SourceScopeQueries`, `SourceSortedQueries`, and `SourceHoldsQueries` prove full mathematical query transport with nested scopes and generated declarations. The repaired ambiguity gate restores original guards or reports compiler uncertainty. `FullGuardPruneStable` removes the conflict-free condition for the historical whole-guard entry under an explicit backend transport contract. `SourceBooleanBridge`, `BooleanGuardPrune`, and `BooleanGuardCompile` lift these scoped results to the repaired public entry. `SourceConstraintConjunction.edgeView_conjoin` derives the actual constructor product guard law. `PartialReductionCaller` derives exact completed inherited equality descent, smart binder rebuilding, execution-bound stability, and repeated whole-node fixed-point preservation. Primitive interned/path/binder adapters, recursive termination, and operational solver correspondence remain. A checked ambient-name collision in the supplied Z3 adapter prevents unconditional exact verdict transport. |
| Similarity/minimization: `Refinement.Minimize` | Guard classification and finite productivity/below-check. `MinimizeSchedule`: directional similarity queries, dominator resolution, source rewrite schedule, read checks, snapshots and fallbacks. The historical schedule has a checked root-nonemptiness counterexample. The repaired schedule installs root representatives and proves their acceptedness from clear-transition productivity. | `SimilarityWithin` proves exact ordered eligible pairs, inference results, and candidate counts. `MinimizeParentIndex` proves the complete indexed schedule equals the full-table schedule and preserves parent metadata through root insertion. Concrete map/interned conversion and validation correspondence remain. Exact language preservation is not its representative-selection contract; the repaired root invariant is now proved for every completed schedule, with the old failure retained as historical evidence. |
| Integer counting: `Refinement.Lattice` | Concrete linear/formula compilation and exact indicators; normalization and terminating feasibility; all-degree Faulhaber sums; actual piece splitting, repeated elimination, stored levels and cumulative polynomials; derived initial support/metadata; integral nonnegative count; zero count iff no solution; exact integer implication decisions. `LatticeSelect.points_api_exact`: actual cumulative polynomials and stored levels give exact natural counts and the full successful-source decoder bijection. Generator point closure is exact. `SearchCost`: logarithmic cumulative-query count. | `LatticeRetry` proves named failures, bounded reorder retries, exact points and definite verdicts. `LatticeSingleton` proves exact successful one-variable singleton detection. Binding freshening, typed syntax/container/machine-index correspondence and remaining supported-input error adapters remain. |
| Ranked core: `Index`, `Ranked.Internal`, `Ranked.Internal.Decoder` | `DistinctRank` and `System`: exact distinct-term Fin n bijection, requested term probabilities and optimization transport. Mixed-radix laws; exact finite plan decoding and normalization. `SizedRank`: inverse ranks and class positions. `PlanVariants`: nested shared/sized constructors, derived counts/order, valid and invalid ranks. | `DecoderDispatch` derives actual n-ary table ordering, exact branch/local-rank selection, and concatenated-member lookup. `DecoderDispatchCost` proves logarithmic comparison cost from actual balanced compilation. `DecoderMachineBounds` derives safe signed modular arithmetic for cumulative offsets, product-size scans, local narrowing, and fused decoding. Callback validation, physical maps, host conversion, indexed-source correspondence and runtime shared storage remain. |
| Size tables: `Ranked.Internal.Size`, `Gen.Internal.Table`, `Gen.Internal.Recursive`, `Gen.Internal.Recur` | Finite sparse convolution and zero-size coverage. `RecursiveSize`: exact node-count language/count/decoder and bounded probabilities. `MinimumSize`: terminating least-size computation. `TablePosition`: actual bottom-up child/state ranking, derived prefixes/offsets, last-successful selection, exact acceptance/replay. | `RecursiveSource`, `MinimumWitness`, and `PublicRecursion` derive guarded single-knot class records, minimum witnesses, probability recurrence and dispatch. `GroupedMinimum` proves finite-key discovery. `SourcePlanPositions` derives complete finite constructor position dispatch, valid class ranks, safe original outcome selection and retained callback certificates. `SourcePlanPartition` derives both position inverses, unique class membership, a complete finite rank permutation, and exact total size counts. `RecursiveUnambiguous` and `SourceCyclicAutomaton` derive distinct cyclic FTA class ranks and bottom-up inverses from the actual public overlap gate and row prechecks. Concrete containers, nested heterogeneous runtime families and lazy representation remain. |
| Sampling: `Ranked.Internal.Sampler`, `Ranked.QuickCheck`, generator QuickCheck modules | Exact rational laws; executable integer-mass conversion, equal-weight grouping, source cumulative binary search and ticket decoding; weighted/uniform/map/product/rejection constructors; structural offsets, finite product indexes, machine-range preconditions and bounded sampler composition. | `SamplerDispatchCost` derives logarithmic ticket-table comparisons. `SamplerMachineBounds` derives exact group, midpoint, and payload word arithmetic from checked compilation. Concrete Map/array and GHC conversion correspondence, backend laws and retry liveness, recursive sample-index productivity, heterogeneous facade wiring. `SamplerReplay`, `FiniteSource`, and `RecursiveRecord` derive complete finite and bounded plain-recursive records and exact distributions. |
| Shrinking: `Ranked.Internal.Shrink`, inspection functions | `Shrink`: all finite constructors, global least-size member with least-rank tie break, strict rank decrease, non-growing size, exact smaller-size traversal, uniqueness and order. | Concrete cached size-index and callback correspondence; lazy infinite traversal. |
| Static generation: `Gen.Internal.Static`, `Automaton`, `Flat`, `Support`, `Types` | `GeneratorCombinators`: explicit weighted members, indexed counts, product counts and quotient/remainder selection, map/pay/atomic distribution laws, complete inverse queries. `PublicResult`: inspection errors. | `FiniteSource` and `SamplerReplay` derive whole and exact-size decoder/sampler records. `SupportTerms` proves source term callbacks. `SupportGraph` and `SupportJoin` prove singleton, keyed-family, restriction and n-way join languages. `SupportClosing` proves exact finite layer closing through nested choices; `SymbolRelabel` proves cyclic graph relabelling under local guard transport. `SupportAlternatives` and `SupportSpineAlternatives` prove exact closing of grouped roots and correlated function spines. `RecursiveSupportBoundary` proves the repaired private recursive boundary. `StaticCheckedRanks` derives true-flag replay certificates for the finite constructor algebra. `CheckedRankQueries` proves the actual public filter and least-rank query from local callback certificates, completeness, and order. `StaticRankQueryExact` derives finite candidate completeness, strict order, bounds, and exact public inversion. `CompositeCheckedRanks` derives finite chain/join/frequency/enumerated certificates, completeness, order, and bounds. `RecursiveCheckedRanks` derives product/choice/pay certificates and exact all-view bounded/global inversion for a complete guarded unary family. `DatatypeDecoder` derives hash-collision-safe full-term restoration, exact codec composition, and comparison bounds. The constructor-probe modules derive terminating productive witnesses, safe FIFO contexts, and complete accepting-transition coverage. `RecursiveTermAlignment` derives equal counts and exact value/term rank alignment for typed single-knot products, choices, maps, pays, and labels, including every bounded prefix. `RecursiveTermMass` and `RecursiveRankMass` derive the full value, term, and rank probability fields before duplicate values are projected. `RecursiveSourceUnfolding` and `RecursiveSamplerUnfolding` derive the full ordered class and sampler knot equations. The `RecursiveCallback*` modules derive terminating all-view inverse queries, exact class and bounded global ranks, source order, and distinct positions for the single-knot binary-choice body algebra. Local finite callback laws have static and atomic producer proofs. `RecursiveNaryChoice` derives the local arbitrary-branch class selector and complete checked inverse from child producer laws. `RecursiveNaryBody`, `RecursiveNaryMass`, `RecursiveNaryRankMass`, and `RecursiveNarySource` cover arbitrary-branch forward bodies and flat ranked field equations. `StaticSamplingDispatch` and `BucketMergeDispatch` extract all finite flag branches. `RecursiveNaryFields`, `RecursiveNaryInverse`, `RecursiveNaryCandidates`, `RecursiveNaryCausality`, and `RecursiveNaryQuery` derive complete n-ary inverse callbacks, source knot equations, bounded/global ranks, order, and distinctness. `KeyedTermAlignment`, `KeyedTermMass`, and the `KeyedCallback*` modules derive independent keyed value/term fields, full simultaneous source equations, and complete bounded/global inverse queries. `KeyedTermCodes` derives total unique source key positions and exact restricted support. Flat n-ary keyed choices, recursive grouped joins, nested runtime families, inspection callbacks, and imported-record correspondence remain. |
| Grouping and joins: `Gen.Internal.Bucket`, `Grouped`, `Join`, `Chain`, `Query` | `GeneratorCombinators`: executable sorted-key partitions, size ordering, conditioned joins, bucket mass restoration, relation-test hoisting, member inverse queries and branch-weight policy. `SizeMass`: class algebra. `MassRetention`: general observed atomic product probabilities and unchanged recursive policy. | `RecursiveGroupFilter` derives exact recursive key filtering, ordered effects, errors, and unchanged retained records. Map/Seq/order representation, heterogeneous n-way argument wiring, other group effects, and recursive join adapters remain. |
| Symbolic generation: `Gen.Internal.Symbolic` | `Symbolic`: executable distinct-intersection signed map, arbitrary-overlap union count, equality contexts, resolution, substitution, constructor expansion, projection, singleton shortcut and block ranking. `SymbolicDriver`: full bounded mutual count/normalize/expand/select/rank driver and graph/context caches. | `SymbolicCounter` now proves all six counter functions and both caches. `SymbolicIndicators` derives signed graph semantics from compiled guards and guarded rows. `SymbolicMeaning` derives successful acceptedness, rank inverses and injectivity. `SymbolicCounterTotal` derives sufficient execution bounds and total stable results for all six counter functions. `SymbolicComplete` proves total decoding and the full distinct `Fin n` index. `SymbolicStructuralBudget` derives semantic and budget laws from acyclic copied rows. Pure interned readback, allocation rank and old-language stability are proved. `SymbolicAllocatedGraph` closes smart-constructor cleanup and allocation-derived indexing. `SymbolicTotalAPI` adds total inverse/rejection. `SymbolicCacheIndependence` proves worker answer independence and concurrent shared-cache validity. `SymbolicPublicAdapter` proves count-once public callbacks and all rank/empty errors. `SymbolicSelectionCost` bounds outer count requests by output size and constructor vocabulary; `SymbolicUnionCost` bounds exponential overlap preprocessing. `SourceSymbolicIndex` and `SourceSymbolicStableIndex` connect actual successful guard compilation to one fixed exact source index and requested term weights. `FiniteAutomatonDriver` and `SourceFiniteAutomaton` derive the mixed compact/symbolic cache driver, source equality parsing and normalization, overlap gate, structural termination, exact public ranks and empty errors. Concrete runtime correspondence remains. |
| Refinement compilation: `Gen.Refinement.Internal.Compile`, `Witness` | Alias, retained-size, finite closure and per-size mass foundations. `SizeTransport`: paid constructors preserve class/mass alignment. `RecipeCompile`: actual recipe routing, root/spine checks, error precedence, hole consumption, integer closure and source atomic-pair metadata counterexample. | `ObservationMass` and `GuardedSampling` derive complete observation products, guard filtering, counts, replay and conditioned distribution. `IntegerLiteral` derives singleton parsing, counting and decoding for every literal. `IntegerTermCodec` proves whole-term rank/decode inverses from actual filling/extraction. `IntegerLabelCodec` instantiates source labels; `OpenIntegerReaders` derives bare-spine hole counts and coordinate order. `IntegerTermViews` proves all three term-view inverses for each original outcome. `ImportObservations` derives exact observation maps, partition coverage, disjoint groups, and decoder composition. `StaticCandidateRanks` derives finite constructor candidate discovery and exact combined point ranks. `OpenIntegerKeys` proves coordinate renaming, disjoint tuple blocks, joined formulas, and product counts. `StaticCompositeCandidateRanks` covers chain/join callbacks and arbitrary-length choice offsets. `CompiledIntegerSpine` derives actual singleton keyed-join terms, hole counts, and exact ranks from generated recipes. `LatticeDeclaredNames` derives formula scope from successful parsing. `ParentIntegerSettlement` derives finite parent counts and conditioned masses from actual child tables and parent filtering. `IntegerCandidateEnvelope` derives candidate-oracle completeness from actual decoder order. `DefiningTerm` derives exact singleton semantics for accepted measures. `ParentGuardFormula` derives parent guard translation from those target refinements. `OpenChoiceRouting` derives finite point weights, branch retention, and source error precedence. `GroupPositions` derives complete first-position lookups for finite and recursive keys. `OpenGroupComposition` derives repeated-key finite merge, heterogeneous widths, parent-labelled ranks, retained counts and conditioned mass. `OpenGroupedApplication` derives finite multi-group applicative pair enumeration, unique concatenated keys, actual JoinN terms, complete filled ranks, coordinate splits, count/mass products, and parent settlement. `FinalObservationRanks` and `FinalObservationMass` derive final observation regrouping, nested frequency wrappers, all view preimages, rank-aligned mass records, normalized event probabilities, and errors. `FiniteSizeFields`, `FiniteSizeSampling`, `FiniteSizeSeries`, `IntegerSizeClosure`, `OpenGroupedSize`, and `FinalSizeFields` derive finite class positions, actual weight callbacks, sparse mass arithmetic, integer-width shifts, and final merge sampling. General recursive composition, arbitrary imported-record flag dispatch, and runtime record wiring remain. |
| Public APIs: `CFTA`, `Equality`, `Refinement`, `Gen`, `Gen.Equality`, `Gen.Refinement`, `Gen.Do`, `Gen.Label`, `Gen.Sig`, `Gen.Error`, `Inspection`, `Ranked` | All 67 modules and export families mapped in `API-COVERAGE`. `PublicResult`: finite/recursive/opaque distinctions, rank errors and exact decided witness filtering. `System`: constrained grammar, distinct Fin n ranks and requested probabilities composed. | Close wrapper, error and callback correspondence to the handwritten models. Member ranks and distinct-term ranks have different contracts. |

### Arbitrary-branch mutual-family integration

`KeyedNaryAlignment`, `KeyedNaryMass`, and `KeyedNarySource` preserve complete
ordered source records for flat mass-weighted choices in mutual families.
`KeyedNaryFields`, `KeyedNaryInverse`, `KeyedNaryCausality`, and
`KeyedNaryQuery` prove all-view candidate and bounded inverse laws.
`KeyedNaryDispatch` distinguishes a bare singleton merge from raw choice.
`KeyedGuards` and `KeyedNaryGuards` connect original occurrence metadata to
the public size and term-growth checks. All eleven modules, including the
kernel examples, are imported by the aggregate dependency audit.

This closes the flat-choice adapter gap for the typed keyed algebra. Local
finite-leaf contracts, arbitrary runtime builder schemas, concrete key
representations, and Haskell extraction remain explicit boundaries.
See [the family notes](notes-keyed-nary.md) and
[the guard notes](notes-keyed-nary-guards.md).

### Current equality and binder normalization

`ConstrainedRecursionGate` models `meetsConstrainedMu`, including same-path
unfolding of open unconstrained binders. A total worker is checked under an
explicit decreasing unfolding rank; the actual source rank is still open.
`BinderSelfUnion` proves exact least-language preservation of the root
self-reference filter. `EqualityIdentityMemo` verifies identity equality,
structural ordering, and memoized descent/conjunction under cache invariants.
See [the current equality notes](notes-current-recursive-equality.md).

### Recursive joins and current sparse decisions

The `RecursiveJoin*` modules now compose heterogeneous and nested joins
inside full typed mutual-family bodies. They derive independent record
projections, exact ranked probabilities, minimum tables, source equations,
mutual inverse callbacks, and public bounded decoder preimages. Candidate
bounds/order/distinctness include false flags. Public queries preserve
ascending distinct ranks under local finite-leaf callback contracts.
`RecursiveJoinGuards` derives family guards from the original public
occurrence metadata. Full support/inspection and weighted-flag assembly,
missing term fields, and arbitrary runtime schema changes remain open.

The current sparse evaluator differs from the older blanket-ambiguity
policy. `SourceEnclosingRenames` records upstream's precise check.
`SourceSubstitutionPrecedence` adds the proved same-scope repair.
`CurrentGuardPrune` models the evaluator-first candidate loop and proves
exactness for unambiguous specialization cells. General accepted ambiguous
sparse-to-complete transport is still open.
The older `FullGuardPrune`, `BooleanGuardPrune`, and memoized candidate
adapters use a more conservative upfront check. Their preservation results
do not establish that missing current-source transport law.

## Evidence and boundaries

Each completed component must record the relevant Haskell definitions, the
Lean definitions and theorems, required representation invariants, and the
remaining connection to callers. Kernel checking must reject omitted proofs
and nonstandard axioms. Regression artifacts support source correspondence;
they do not replace its proof.

External components require explicit contracts: the Lean kernel, primitive
arithmetic/container behavior, the Haskell runtime and compiler, solver
answers, and random-bit generation. These contracts must not assume an
internal algorithm's desired result. Machine bounds, callback validity,
concurrent cache behavior, and termination must be addressed at their actual
use sites. This list records proof boundaries; it does not declare them
verified or exempt all code that uses an external component.

## Remaining proof obligations

- The Sized algorithmic contract and positive PlanScale are now checked.
  Connect their explicit finite graph, class-table, and evaluator models to
  concrete host containers, lazy heaps, lawful comparisons, machine
  conversions, and IO traces. See `notes-source-sized.md`.
- Finish the changed source interfaces for CPS enumeration, batched suspended
  descent, omitted union-find writes, and reserved empty-domain identity zero.
- Connect the checked lattice retry and equality normalization drivers to
  physical maps, arrays, name conversion and machine indexes.
- Connect proved symbolic allocation, smart constructors and shared-cache
  public callbacks to concrete runtime representations. Total count/select/rank
  and the distinct index are proved.
- Connect finite lexical binder instances and the proved full nested rebuilding
  worker to runtime interning caches, stable identity readback, and host storage in the proved initialized enumeration driver. Finite memo traversal, two-stage interning,
  terminal fast paths, and bounded row-language invariants are now derived. Soundness, completeness, rendering, and
  sufficient stable execution bounds are now proved.
- Connect caller state, binder allocation, and substitution to the checked
  union-find, observation, and finite graph algorithms.
- Prove recursive pruning and remaining heterogeneous recursive compilation
  terminate. Cyclic graph-to-binder construction now has a totality proof
  under complete cycle marking.
- The bounded pruning caller now has preservation and call-limit proofs.
  Derive the remaining individual-call and recursive callback completion
  contracts. PR #109 removes its former unbounded fixed-point loops.
  General unbounded identity convergence remains a separate optimization
  question. The public equality worker performs one pass. The witness in
  [notes-finite-reduction-growth.md](notes-finite-reduction-growth.md) shows
  why finite languages, semantic descent, and the leaf guard bound do not
  prove general convergence. No fixed-schedule acyclic cycle is known here.
- Establish the remaining runtime, external solver, random-source, and codec
  correspondences at the stated boundaries.

The intended pipeline has composition theorems. The current implementation
has operational models, a complete module inventory, focused source checks,
and counterexamples. These are separate deliverables. The unresolved internal
proof obligations above prevent a whole-implementation verification claim.
