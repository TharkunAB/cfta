# Proof status at 2026-10-17

Checked at proof checkpoint `7a441d2d`. Source main is `c0cc8a05`,
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
There is no completed single whole-library theorem.

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
| Stored substitution | Independent captures preserve exact execution. Node and union returns retain source fields and ordered child calls. Selected-Mu body and ordinary reconstructions complete in sequence and replay at one final heap. Actual source paths retain writer growth into that heap. Open observations retain references, full guards, and ordered children through actual Mu unfolding. | General two-reconstruction equality and retained-used Mu row congruence remain open. Open observations use one fixed view. Physical equality to the unreconstructed ordinary probe is false. See [retained Mu reconstruction](notes-current-retained-mu-reconstruction.md). |
| Recursive native intersection | Checked execution has exact intersection semantics for closed Original resident operands. Initial numeric bounds construct a physical query, its checked instruction schedule, and allocation bounds. Mu and union operands are included. | Compose contextual semantics and generated result-fed callers on the same actual trace. Complete concrete runtime and total memory bounds. |
| Finite ordinary constrained reduction | Initial profiles and constructor headroom derive the original universal raw Reach numeric Plan. The complete modeled outer pass has stable execution, exact full guarded-language preservation, retained stores, and constructor request bounds. | The domain excludes Mu, references, and explicit unions in every descendant. The theorem does not bound total Haskell runtime or memory. |
| General reduction components | Initial resources construct supported readers, Merge, Target, Force, Leaf, editors, class passes, local reduction, parent edges, and edge memo calls. Actual primary certificates now construct complete Required returns with exact language and structural row origins. | General recursive outer-node progress and repeated-pass convergence remain open. Component support domains do not establish their composition for every recursive caller. |
| Outer memo owners | Equal physical request keys identify complete ready request arguments. Bounded workers retain evaluating owners on busy faults. Initial edge-idle tables exclude outer edge-busy faults. A constructed copied-child case reaches a ready hit while ancestor node owners remain active. | General node-busy exclusion still needs a compatible progress or owner-disjointness argument. The constructed case is not a general host schedule theorem. |
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

1. Prove the retained-Mu source row relation through actual reconstruction
   and epsilon exposure. Both selected reconstruction calls now complete
   and replay at their common final heap. Actual source paths derive the
   selected first writer and raw callback growth into that reader. Open
   observations preserve bare references, full guards, and ordered children.
   General reconstruction equality and the retained-used Mu congruence
   remain open. Finite successes do not discharge those obligations.
   Derive freshness and issued-reference transport from actual execution.
   Four-table Grows does not imply issued-reference extension. Compose the
   recursive row relation with native callbacks and protected edge histories
   on the same trace. Read
   [retained Mu reconstruction](notes-current-retained-mu-reconstruction.md).
2. Derive progress for actual outer-node children after parent returns and
   inherited combine/descent. The measure must respect physical memo keys,
   or prove that a fresh request differs from every active owner. Ordinary
   height and maximum constrained depth do not give that measure. Then
   complete nonempty live child walks, ordered rows, ordinary node bodies,
   and the full mutual outer pass. Mu and union roots can be terminal while
   selected paths still enter their contents.
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

The last completed full pinned Audit passes 3095 jobs and 68057 dependency
checks. Only propext, Classical.choice, and Quot.sound occur. The unchanged
Haskell source has a strict Nix all-component build, 798 examples plus golden,
Fourmolu, and Cabal-gild validation. These checks are component evidence.
They do not provide a meaningful percentage of whole-library completion.
The Lean Audit and new public theorem checks were run for this
checkpoint. The unchanged Haskell source reuses its earlier validation.

The latest completed audit evidence is in
`restart-evidence/20261017-retained-mu-reconstruction/`. It includes strict source,
public signature, kernel axiom, constructed integration, and preservation
checks. Earlier evidence retains selected recursive endpoints,
unequal-depth paths, failed height bounds, and inherited path-depth growth.
Actual union-normality transport now reaches all eight bounded mutual outer workers
on every stopping outcome from the initial invariant alone. It does not
construct successful outer completion. Finite observations do not prove
general progress. No new Haskell defect
was established. Failed attempts and raw logs remain preserved.
