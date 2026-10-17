# Proof status at 2026-10-17

Checked at proof checkpoint `c1be0445`. Source main is `c0cc8a05`,
merged into `formalize` at `896b0a1c`. This note reports the current theorem
boundaries. It adds no theorem and no Haskell behavior change.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. The target is
a family of theorems, with this schematic form for each operation P:

`Valid(input) ∧ Supported_P(input) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

The support predicate must describe initial inputs and resource limits.
It must not assume successful completion. The specification must include
the documented errors and validation order where the API returns errors.
There is no completed single whole-library theorem. The largest mathematical
gap is general recursive outer progress and repeated-pass convergence.
Concrete public Haskell correspondence is a separate remaining obligation.

## Strongest current claim in plain technical English

For a validated finite graph, the checked exact-size model returns exactly
the distinct accepted terms of the requested node-count size. It counts
those terms correctly. Rank and unrank follow the specified order and are
inverses. Cyclic graphs are included. The declared ordering and solver
contracts remain explicit assumptions.

The checked recursive native intersection has exact intersection semantics
for closed resident Original operands. Initial resource bounds construct
supported physical executions. The complete finite ordinary constrained
outer pass preserves the full guarded language. That outer-pass domain
excludes Mu, references, and explicit unions in every descendant.

These are separate checked results for the implementation model. They do
not establish that every valid public Haskell call terminates and satisfies
its contract. General outer progress, repeated-pass convergence, retained-Mu
callback alignment, and the remaining concrete adapters are still open.

## Observable contracts

The main observable contracts are:

- Exact listing returns all distinct accepted terms at a node-count size.
  It returns no duplicates. Counting gives the cardinality of that class.
- Rank and unrank follow the specified order and satisfy both inverse laws.
- Each transformation has its own language relation. Exact transformations
  preserve language. Over-approximations prove inclusion. Representative
  selection has a separate restriction contract.
- Generation covers the specified members. Sampling has the specified
  weights and probabilities. Members, accepting runs, and distinct accepted
  terms require separate statements.
- Current Haskell execution agrees with the specified algorithm and errors.
  This includes memo effects, machine bounds, and representation limits.

Exact queries use the explicit graph, including cyclic graphs. The optimized
interned core remains the construction and transformation path. Read
[ADR 0004](../docs/adr/0004-explicit-graph-boundary.md).

## Established results and their limits

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact accepted size classes, finite class evaluation, counts, size-major enumeration, retained row order, and both distinct-term rank/unrank inverses. The finite carrier comes from validated raw graph keys. | Concrete host and solver adapters and complete public pipeline composition. See [Sized contracts](notes-sized-finite-keys.md). |
| Interned construction | Repaired closed syntax has a finite constructor execution. Syntax includes binders and unions. Actual construction and field histories derive physical and semantic entry facts. | Concrete lazy Haskell publication, interning, and runtime correspondence. The word Ordinary in older module names does not by itself exclude binders. |
| Normalized source callbacks | Actual source publication histories derive the unused stored-Mu body-to-ordinary law, including earlier warm winners. Nested raw source calls have equal ordered stripped alternatives under the stated finite coverage, freshness, noDeep, and actual cache-history premises. Actual native steps and traces now produce the causal publication history. Unused native returns preserve the current raw ordinary callback rows. | Recursive row occurrence transport through retained Mu and concrete runtime correspondence. The common heap of closed_compared comes from actual closed source construction. This is not raw record equality or general termination. |
| Stored substitution | Recursive node-row matching constructs both plans with one exact Value. Initial Ready and available data construct both union-normalization/substitution orders with physical empty agreement, equal observations at every depth and fixed view, and exact literal root parts. Actual self filtering preserves those parts from the derived final heap. Initial Ready data now constructs filtered reconstruction and the retained-member schedule with exact literal parts, including the bare-self exception. Actual parent construction preserves this relation, including row survival, full guards, and ordered children. Source-indexed ordinary-node Mu publication callbacks now retain both exact schedules, common-reader growth, and equal ordered child Empty and row-drop tests. Closed and open roots and nested Mu values remain included. | Derive the literal relation for the actual retained-Mu body and ordinary-probe writers, then compose smart cleanup and warm winners. General root self-filter congruence is proved for normal available roots with the same literal atoms and exact rows. See [literal provenance](notes-current-literal-union-provenance.md). |
| Recursive native intersection | Checked execution has exact intersection semantics for closed Original resident operands. Initial numeric bounds construct a physical query, its checked instruction schedule, and allocation bounds. Mu and union operands are included. Persistent native histories now derive actual earlier edge writers, exact captured handles, writer-to-reader heap growth, and indexed full guard origins. Initial numeric query inputs produce completion and the same history with all resource bounds. Actual surviving compileRows rows now retain source row/child indices, full joined guards, and historical child calls at growing heaps. | Compose contextual semantics and generated result-fed callers on the same actual trace. Complete concrete runtime and total memory bounds. |
| Finite ordinary constrained reduction | Initial profiles and constructor headroom derive the original universal raw Reach numeric Plan. The complete modeled outer pass has stable execution, exact full guarded-language preservation, retained stores, and constructor request bounds. | The domain excludes Mu, references, and explicit unions in every descendant. The theorem does not bound total Haskell runtime or memory. |
| General reduction components | Initial resources construct supported readers, Merge, Target, Force, Leaf, editors, class passes, local reduction, parent edges, and edge memo calls. Actual primary certificates now construct complete Required returns with exact language and structural row origins. Initial Ready data and field availability derive exact normalization fixedness through the actual inherited prefix and indexed descent. Actual completed Parent reads now retain native writer history through Scan, Required, class passes, local reduction, and construction, with the existing explicit Parent range plan. Actual edited normalized rows retain indexed source prefixes, full fields, and derived writer histories at the same captured row states. | General recursive outer-node progress and repeated-pass convergence remain open. Component support domains do not establish their composition for every recursive caller. |
| Outer memo owners | Equal physical request keys identify complete ready request arguments. Bounded workers retain evaluating owners on busy faults. Initial edge-idle tables exclude outer edge-busy faults. A constructed copied-child case reaches a ready hit while ancestor node owners remain active. Actual descent of a Ready live nonempty inherited payload strictly lowers path height and changes its identity, including warm hits. An actual empty-own prefix retains normalized inherited values. Actual normalization and combination produce fixed payloads, and indexed descent preserves fixedness. Strict class dependencies remain exact among retained classes of one normalized payload. Initial fields and Ready operands now produce original-constituent containment and dependency preservation through actual accessor, combination, normalization, and retained indexed descent. A mirrored copied-child case reaches a fresh demand before its original sibling, then completes. Another source reaches the exact original node under a different inherited key while its root owner evaluates; the local precheck and both completed calls produce Empty. | General node-busy exclusion still needs a causal progress or owner-disjointness argument for nonempty local classes and all active ancestors. The constructed prefix and descent cases do not prove a general outer parent-and-child execution. See [actual row progress](notes-current-active-row-progress.md). |
| Other library components | Checked language, equality, enumeration, arithmetic, union-find, memo, ranking, generation, and sampling results exist. Some source drivers and restricted adapters are complete. | Their remaining adapters and recursive callers do not yet form a complete current-library implementation theorem. See [API coverage](API-COVERAGE.md). |

The finite ordinary result is in
`SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryRoot.finite`,
`constructed_root`, and `prepared_root`. The caller no longer supplies the
reached numeric Plan. Read [the resource result](notes-current-raw-reach-capacity.md).

The earlier recursive native result is
`SourceCurrentAllocatedNativeColdClosedExact.cold_complete`.
`SourceRecursiveIntersectionRequestProgress.initial_complete` already derives
semantic completion for closed Original inputs. These semantic results
do not require the caller to supply semantic Completes.
`SourceCurrentAllocatedNativeConstructedHistory.query_complete` also derives
entry facts from actual generic construction and a covered field history.
It retains the actual build and WordRanges premises.

`SourceCurrentAllocatedNativeComputedBudget.initial` now constructs the
complete physical query and its resources from initial counters, causal
stored mass, closed Original operands, semantic readiness, idle native
tables, and numeric headroom. It does not require a future Trace,
WordRanges, instruction count, or returned-result law. Read
[computed query budgets](notes-current-computable-query-rank.md).
This receipt still needs contextual language composition on the same trace.
It does not bound all internal constructor work, solver work, or total memory.

The latest Required entry is
`SourceCurrentRequiredPrimaryOrigins.constructed`. Actual construction
derives its readiness, cost, guard, and union-normality facts. An earlier
false primary class and initial operand availability construct a complete
Required return with exact guarded language and indexed original row
origins. It assumes no future Required result. Read
[Required origins](notes-current-required-origins.md).

## Remaining work

1. Derive retained-Mu row and ordered-child provenance from actual causal
   writers. Recursive normalized plan and stored congruence now construct
   both actual calls with one exact result from initial Ready and available
   captures. Their pure structural relation is not yet derived for arbitrary
   retained Mu histories. Prior union normalization now has an actual
   initial-input theorem with physical empty agreement, all finite
   observations, and exact literal reference and Mu atoms and complete rows.
   Actual ordinary parents preserve the observation relation. Root self
   filtering now preserves exact literal parts for normal available roots.
   The initial theorem derives the required parts for the two union orders.
   It does not derive them for arbitrary selected body and ordinary-probe
   writers. Actual ordinary-node publication callbacks now have paired source
   row schedules and derived child Empty and row-drop agreement. Nonempty
   child records, observations, and literal Mu atoms remain unaligned. The new filter-reconstruction producer constructs each filtered
   stored call and its retained-member schedule from initial data. Align
   those schedules for the actual body and ordinary-probe writers. Then
   compose smart cleanup, fixed captures, and earlier warm winners. Retain full guards, exact child
   survival, bare references, and epsilon origins. Derive freshness and
   issued-reference transport from actual execution; four-table Grows does
   not supply the latter. Compose with native callbacks and protected edge
   histories on the same trace. Read
   [literal provenance](notes-current-literal-union-provenance.md).
2. Derive progress for actual outer-node children after parent returns and
   inherited combine/descent. The measure must respect physical memo keys,
   or prove that a fresh request differs from every active owner. Actual
   normalization and combination now produce exact fixed payloads. Actual
   trie descent preserves fixedness. The full accessor/prefix/descent path
   derives it from initial Ready data and field availability. Empty-own
   prefixes retain normalized inherited values; nonempty descent then
   strictly lowers path height and changes its canonical identity. The
   retained class dependencies now remain exact within each normalized
   payload. A copied child can still require fresh work before its original
   sibling is visited. The remaining argument must control nonempty local
   classes and all active ancestors. Persistent native histories supply
   actual earlier full guard writers, exact owner handles, and growth into
   the reader heap, but not a global occurrence rank. A checked source now
   repeats the exact original value under a different inherited key; its
   local precheck and both complete calls produce Empty. This rejects whole
   physical-value descent, not proper row-origin measures. Ordinary height
   and maximum constrained depth do not suffice.
   Then complete nonempty live child walks, ordered rows, ordinary node
   bodies, and the full mutual outer pass. Mu and union roots can be terminal
   while selected paths still enter their contents. Read
   [actual row progress](notes-current-active-row-progress.md).
3. Prove convergence for repeated reduction passes and complete the remaining
   recursive pruning and compilation callers. One exact completed pass does
   not establish a fixed point. Semantic narrowing alone does not bound
   intermediate structural growth.
4. Complete current frontend correspondence. This includes typing and
   refinement derivation, drawn fields, symbolic measures, new errors,
   validation order, and generator-specific order.
5. Complete concrete runtime and external adapters. These include maps and
   arrays, signed indexes and counters, lazy memo publication and forcing,
   process-global state, interning, codecs, solver answers, IO, and random
   draws. Keep explicit primitive and user-code assumptions visible.
6. Compose generated result-fed native queries and complete public pipelines
   through construction, transformations,
   graph conversion, exact queries, generation, and sampling. Abstract
   composition does not discharge a missing implementation adapter.

The older PlainRegion theorem permits opaque Mu and union leaves. It requires
empty physical equality payloads on traversed ordinary edges. It does not
prove general recursive selected narrowing.

## Haskell repairs and evidence

The recursive field-pool defect is repaired by `b9219b9e`, merged in PR 65.
The current derivation rejects a pool for a field of the datatype itself.
The retained Chain example returns `Left (FieldAtomOnDatatype "Next" 0)`.
Standalone holds still treats supplied pools as opaque. The repair rejects
the invalid derivation input; it does not change that standalone evaluator.
Root [FINDINGS](../FINDINGS.md) keeps the repair handoff first. It records
the failure, reproducer, affected paths, commit, validation, and merge status.
It also records the earlier negative-bound and named-measure repairs.
The historical failure reports retain their original bytes and source dates.

The last completed full pinned Audit passes 3148 jobs and 69431 dependency
checks. Only propext, Classical.choice, and Quot.sound occur. All four new
strict logs are empty. Thirteen full public proof checks and the constructed
integrations pass. Actual row prefixes derive the captured native histories.
The retained-Mu independent case does not discharge active children.
The Audit replays one unchanged old unused-variable warning.
The unchanged Haskell source retains its strict Nix all-component build,
798 examples plus golden, Fourmolu, and Cabal-gild validation. These checks
are component evidence. They do not measure whole-library completion.

The latest completed evidence is in
`restart-evidence/20261017-parent-row-lineage/`. It includes strict source,
public signatures, complete proof output, kernel axiom, constructed, and
preservation checks. The output checker rejects proof-printer failures.
Earlier failed attempts and raw logs remain preserved. No new Haskell defect
was established. General recursive progress and full correspondence remain open.
