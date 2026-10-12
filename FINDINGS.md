# Current formalization findings

Updated: **2026-10-13 01:19 CEST**.

The formalization is rebased onto `origin/microcfta` at `de910ea`. The
upstream base contains the earlier findings repairs. This continuation found
and repaired three additional defects, described as rows 18 through 20.
All **620 existing Haskell examples** pass after the repairs: 284 core, 194
generator, and 142 refinement examples.

The full Lean development passes **638 jobs and 30,710 theorem dependency
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

## Baseline and required contract

The continuation branch is `formalization/microcfta-resume-20261012`.
Its implementation base is `origin/microcfta` at `de910ea`, including the
merged findings repairs through PR #96. The previous proof branch remains
unchanged. Backup `backup/lean-before-microcfta-20261012-2200` and the retained
stash preserve the pre-rebase work. Nothing from this continuation is pushed.
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

Rows 1–17 describe earlier repairs now merged upstream. Rows 18 through 20 are
local repairs on top of `de910ea`. Each row has a retained source reproduction and a corresponding formal
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
| 18 | In one substitution scope, merging equal actual identities could remove the first identity replacement and expose a later replacement for the same formal. Sparse evaluation returned `Yes`, pruning admitted a rejected term, and compilation produced one invalid tuple. | Return `Unknown` when an uncertain identity replacement has a later duplicate formal. Pruning retains the guard; compilation returns `SolverUnknown`. The existing [guard/pruning reproduction](lean/repro/NestedScopeCapture.hs) and [compiler reproduction](lean/repro/NestedCompileCapture.hs) now check both nested and same-scope cases. `SameScopeIdentityCapture` retains the pre-repair witness; `SourceSubstitutionPrecedence` proves the new check. |
| 19 | A recursive callback could inspect temporary support and select different bodies during count, term, and support rebuilds. The public bounded generator returned four terms that its support rejected. | Keep construction tokens separate from size flags. Reject payload queries until the definition completes. Nested definitions retain enclosing tokens; both recursive and finite return paths remove their own token. `RecursiveConstructionQueries` proves marker provenance, stable rejection, and completed query behavior. The existing recursive-member case in `GenSpec.hs` checks the original callback, fourteen query paths, and nested-family completion. See [the construction-query notes](lean/notes-recursive-construction-queries.md). |
| 20 | Grouped key discovery retained an earlier minimum after a callback changed its base. `minimumSize` returned zero although counts were `[0,1,1,1]` and the smallest member had size one. | Compare the final probe's keys and minima with the accumulated discovery table. Return `InconsistentRecursiveFamily` on disagreement. `GroupedProbeValidation` derives a true body fixed point for every successful check and proves that constructor programs retain their previous least-attained minima. The existing recursive-member test retains the public callback. See [the discovery-validation notes](lean/notes-grouped-probe-validation.md). |

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

- Latest source suites: **620 passing examples**, on `de910ea` plus the local
  repairs. The full run is `/tmp/mcfta-construction-query-full.log`.
  After the grouped-discovery check, all 194 generator and 142 refinement
  examples pass in `/tmp/mcfta-family-discovery-validation.log`. Core is unchanged.
- Repaired nested and same-scope source probes both report `(No,Unknown)`
  for complete/sparse evaluation, `(No,No)` before/after pruning, and
  `Right []` versus compiler `Left SolverUnknown`.
  Log: `/tmp/mcfta-scope-precedence-repaired.log`.
- Latest integrated Lean audit: **638 jobs; 30,710 theorem dependency checks**.
  Only `propext`,
  `Classical.choice`, and `Quot.sound` are allowed.
  Log: `/tmp/mcfta-raw-inventory-complete-worker-audit.log`.
- The retained formula capture, nested compiler capture, recursive equality,
  and open-union reproductions pass on the new base. The independent two-key
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

## Remaining hard proof obligations

1. **General finite-DAG equality fixed-point termination.** Explicit caller
   loops still require a representation-level termination argument. A checked
   six-round example grows nodes and rows while preserving a singleton
   language. Semantic finiteness and decreasing language size are insufficient.
   Complete multi-symbol leaf forests now have a derived pass bound, including
   simultaneous class edits and empty propagation. The source guard inventory
   is generated from the initial atoms. Nested source intersection can return to
   an earlier identity when its operands alternate. This rules out a general
   schedule-independent measure. No cycle of the fixed equality schedule was
   established. Disjoint binary direct-child classes stabilize after one
   changing pass, including nested domains. Projected paths need a separate
   argument; a retained source example needs two changing passes. Projected
   leaf occurrences now have a derived schedule bound, including ancestor
   pruning, duplicate rows, and empty propagation. Physical parent rebuilding
   and finite recursive child edits now derive normalized readback, completion,
   and a common cache for exact replay. Physical leaf intersection and
   projected union readback are proved for canonical admitted guards.
   Source arity checks now derive admission. A separate normalization phase
   proves progress for raw initial guards and constructor rejection. Physical
   raw construction now preserves rejected sentinel allocations and derives
   exact readback and whole-node identity from accepted row sets. Physical
   Cartesian intersection now derives raw readback and strict rank decrease.
   The finite raw inventory retains original syntax and later canonical guards.
   Finite occurrence compilation and actual child workers derive complete
   payload availability and readback. Whole stateful pass composition remains
   in progress.
   See [the growth notes](lean/notes-finite-reduction-growth.md) and
   [projected leaf schedules](lean/notes-equality-leaf-projection.md).
2. **Nested binder identity after normalization erases a fresh outer
   dependency.** Retained dependencies separate pending keys. Original
   independence permits cache reuse. Erasure through an empty child now
   derives exact complete-record reuse under changed outer bindings.
   Arbitrary successful nested syntax executions replay without allocation
   after cache growth. First execution still needs a proof that no closed
   input reads a pending record. A syntax-derived marked fragment now proves
   first-run completion. Binder bodies preserve a nullary root marker;
   nested binders avoid active ancestor markers. Siblings may reuse markers.
   The theorem derives complete coverage and replay without assuming success.
   Separate source-derived classes now cover independent nested callbacks,
   two-level erased outer references, and arbitrary-depth binders that keep
   each enclosing reference through a live root edge. The last class permits
   every binder to use the same symbol. A combined source grammar now places
   these mechanisms inside one pending execution. General mixed dependencies
   remain open. For arbitrary syntax, every hypothetical pending result now
   has a derived earlier reservation with complete probes. Every identity
   and recursive reference in either probe, including stored Mu bodies and
   probes, predates that reservation. Full syntax preserves pending slots and
   dense identity tables. A later resident old identity has the exact complete
   earlier payload. A recursive erased-edge grammar now derives first
   completion at arbitrary depth with nested independent live children.
   General absent-reference replay is the remaining completion step.
   Full nested constructor traces now derive
   coherent caches, complete child provenance, outgoing edge residency,
   cache growth, and issued-reference history. No closed-input collision
   was established.
   See [the nested-construction notes](lean/notes-interned-nested-construction.md)
   and [pending-origin proofs](lean/notes-interned-pending-origins.md).
3. **Remaining recursive runtime records and nested-builder composition.**
   Typed nested-join families, decoder/mass records, inverse callbacks, and
   public occurrence guards are proved. Complete recursive support assembly,
   weighted flags, and absent term fields now compose with those bodies.
   Diagnostic inspection and both sampler branches are now derived from
   local source records. Ordinary application now composes all views under
   the derived plain-input invariant and exact source weight rules.
   Arbitrary opaque inspection descriptors remain.
   The construction-query repair prevents the concrete payload observation
   mismatch. The final family table check rejects stale keys and minima;
   typed constructor programs pass without changed results. Construction
   marker provenance now composes with the complete typed record, including
   its exact public support query. Builders can still run
   under different placeholder contexts; one fixed typed schema does not
   prove that arbitrary Haskell builders preserve their shape and errors.
4. **Concrete runtime and external correspondence.** Physical interning,
   identity allocation lifetimes, containers, machine-word storage,
   concurrency, Haskell lazy productivity, solver IO, random draws, and user
   codecs/callbacks need their stated contracts. Global identity freshness
   requires a bounded allocation lifetime and linearizable draws.

5. **Guard completeness and exact backend verdicts.** The many-to-one
   environment relation is now derived through both executed scope checks.
   Full sparse guard Yes implies complete logical satisfaction. Current
   pruning and successful compiler retention inherit that safety result.
   Sparse No now refutes complete logical satisfaction. Successful pruning
   retains every original backend-confirmed term. A completed candidate pass
   retains every logically valid term; restoring the original guarded edge
   requires a complete backend Yes. Successful compiler classification is
   equivalent to logical validity. Logical planned-read transport no longer
   requires stable backend verdicts for unrestricted ambient values. More
   general sort domains use an explicit compatibility condition for names
   present in only one avoid list. A checked accepted ambiguous example
   returns sparse Yes and complete Unknown with one sound callback. Thus
   soundness does not give exact backend-confirmed language equality.
   The all-Int solver adapter now supplies these soundness premises from
   actual preflight and returned results, conditional on external response
   correctness. Sort lowering uses its induced interpretation. The embedded
   arithmetic core agrees with the independent integer interpretation.
   See [the logical read-transport notes](lean/notes-source-read-logical.md).

These obligations prevent a whole-implementation verification claim. They
are separate from the repaired concrete failures and the proved component
properties. The immediate restart actions and file ownership are in
[HANDOFF.md](HANDOFF.md).
