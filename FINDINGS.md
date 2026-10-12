# Current formalization findings

Updated: **2026-10-12 10:45 CEST**.

The branch repairs **17 recorded source defects**. The latest full Haskell
run passes **618 examples**. The committed Lean development passes **437
build jobs and 24,376 theorem dependency checks**. Additional completed
keyed-n-ary and recursive-join proofs are still uncommitted and outside that
aggregate audit. See [HANDOFF.md](HANDOFF.md) for their exact state.

This is the current report. [lean/FINDINGS.md](lean/FINDINGS.md) records the
initial historical findings against an older revision. Its historical
"proposed repair" and "no production fixes" statements do not describe the
current branch. [lean/SYSTEM.md](lean/SYSTEM.md) contains detailed current
counterexamples, repair arguments, and implementation comparisons.

## Baseline and required contract

The branch is `spike/microcfta-lean-soundness`. The implementation base is
`origin/microcfta` at `bbeb7be`, including merged core-formula work and PRs
#89 and #90. The last proof checkpoint is `bc6a978`. Nothing has been pushed.

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

Each row has a retained source reproduction and a corresponding formal
counterexample, repair theorem, or operational model. Older per-repair test
totals in the linked reports describe their historical checkpoints. The
current combined suite total is 618.

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
| 9 | Sparse nested substitution could discharge a guard that complete evaluation rejected, admitting an invalid term. | Retain the guard during pruning and return `SolverUnknown` during ambiguous compilation. This does not assert an empty language. [Pruning reproduction](lean/repro/NestedScopeCapture.hs), [compiler reproduction](lean/repro/NestedCompileCapture.hs); `PruneAmbiguity`. |
| 10 | Equivalent conjunctions grew from size 9 to 29 to 89 during repeated acyclic equality reduction. | Flatten outer conjunctions, remove `Top`, sort, and deduplicate while preserving scopes. The retained case stabilizes. [Reproduction](lean/repro/PruneConjunction.hs); `GuardConjunction`. |
| 11 | Combining independently interpreted guards could change an operand's meaning and admit a term rejected by an input automaton. | Allocate each outer Boolean operand independently and preserve nonempty substitution scopes. The reproduction now reports `[Yes, No, No]`. [Reproduction](lean/repro/ConjoinScope.hs); `SourceBooleanEntry`. |
| 12 | Recursive equality narrowing repeatedly expanded equivalent domains and exceeded the retained runtime limit. | Stop narrowing across recursive paths or endpoints while retaining the original equality constraint. [Reproduction](lean/repro/RecursiveReduction.hs); `RecursiveReductionBarrier`. General nontermination of the old example was not proved. |
| 13 | Observing an imported explicit union could drop every valid term and report `EmptyGenerator`. | Expose `InternedUnion` through the finite epsilon closure before ordinary observation splitting. [Reproduction](lean/repro/ImportUnion.hs); `ImportObservations`. |
| 14 | Observation filtering could reject valid recursive groups as `UnboundedGenerator` and lose their size indexes. | Filter the ascending key map directly and retain complete recursive records. [Reproduction](lean/repro/RecursiveGroupFilter.hs); `RecursiveGroupFilter`. |
| 15 | `boundDepth` could loop on retained empty binder cycles even though their outer-edge closure was empty. | Use visited `nodeEdges` exposure uniformly before recursing into constructor children. [Reproduction](lean/repro/BoundRetainedBinders.hs); `LexicalBinderClosure`. |
| 16 | A syntactic extraction such as `v == v` could be treated as an exact integer measure and remove valid expressions. | Reject fallback measures that depend on the refined value. Preserve exact singleton extraction priority. [Reproduction](lean/repro/SelfDependentMeasure.hs); `DefiningTerm`, `ParentGuardFormula`. |
| 17 | Recursive open group positioning queried cardinalities, built an empty position map, and raised `Map.!`. | Read the available group keys directly. Unsupported recursive integer closure now returns its existing explicit error. [Reproduction](lean/repro/RecursiveOpenPositions.hs); `GroupPositions`. |

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
an eighteenth independently reproduced public defect. See
[the parent-index notes](lean/notes-minimize-parent-index.md).

Retained size masses also move when constructors pay a size unit. Earlier
integration omitted those shifts in two paths. The source and transport
proofs now preserve the member/mass alignment.

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

Completed work awaiting aggregate integration extends those results to
arbitrary-branch mutual families. The new dispatch proof distinguishes bare
singleton grouped merges from raw singleton choices that add `Choice 0`.
The original typed guard proof distinguishes a user label from a plain pay.
Both add size; only the label supplies the corresponding term-growth guard.
See [the n-ary notes](lean/notes-keyed-nary.md) and
[guard notes](lean/notes-keyed-nary-guards.md).

The new local recursive-join adapter proves the actual `JoinN`, `CenterKeyed`,
and `ArgKeyed` structures for all arities, including zero. It preserves
heterogeneous argument values and their matching term ranks. It also proves
the source prefix-count/argument schedule, exact all-view callbacks, and
bounds/order/distinctness for false and true candidates. `RecursiveJoinMass` also has a separate passing build. The direct
record-to-selector bridge has an unresolved Lean error and is not complete.
Integration into the whole recursive body syntax is still outstanding. The ordinary `Apply`
theorem cannot substitute for that integration. See
[the join notes](lean/notes-recursive-join-fields.md).

## Evidence and its limits

- Latest full source suites: **618 passing examples**, after rebasing onto
  `bbeb7be`. No production source changed afterward.
- Latest committed aggregate Lean audit: **437 jobs; 24,376 theorem dependency
  checks**. Only the standard Lean axioms `propext`, `Classical.choice`, and
  `Quot.sound` are allowed. Uncommitted additions have separate targeted builds.
- Independent source probes covered 5,000 finite grammars; 1,536 mixed
  grouping/recursion descriptions; nine automaton-import variants; 144
  weighted descriptions across nine size bounds; and 2,080 bounded recursive
  intersection comparisons.
- Recent independent exact-rational recurrences checked 132 single-root,
  254 two-key, and 285 delayed-third-branch member inverses, their probability
  tables, and support acceptance.
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
   No general proof or acyclic nontermination counterexample was established.
   See [the growth notes](lean/notes-finite-reduction-growth.md).
2. **Nested binder identity after normalization erases a fresh outer
   dependency.** Retained dependencies separate pending keys. Original
   independence permits cache reuse. Those results do not yet establish the
   complete erased-dependency case. No closed-input collision was established.
   See [the fresh-probe notes](lean/notes-interned-fresh-probe-keys.md).
3. **Complete recursive grouped-join and nested-builder composition.** Local
   join fields are proved. The whole typed body constructor and remaining
   runtime record/inspection paths still need composition. Builders can run
   under different placeholder contexts; one fixed typed schema does not
   prove that arbitrary Haskell builders preserve their shape and errors.
4. **Concrete runtime and external correspondence.** Physical interning,
   identity allocation lifetimes, containers, machine-word storage,
   concurrency, Haskell lazy productivity, solver IO, random draws, and user
   codecs/callbacks need their stated contracts. Global identity freshness
   requires a bounded allocation lifetime and linearizable draws.

These obligations prevent a whole-implementation verification claim. They
are separate from the repaired concrete failures and the proved component
properties. The immediate restart actions and file ownership are in
[HANDOFF.md](HANDOFF.md).
