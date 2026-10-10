# Full formalization coverage

## Objective and completion rule

Formalize the complete microcfta design in Lean. Prove that generation covers
all required terms, that sampling has the specified probabilities, and that
each optimization preserves its stated semantics. Keep the correspondence to
the actual Haskell algorithms explicit. Record implementation errors while
continuing the other proof work. Report the findings at the end.

The goal remains active. Passing builds, theorem counts, and finite examples
do not establish completion. A row is complete only when its executable
algorithm has a checked semantic theorem and its implementation correspondence
is established. A theorem whose main algorithmic obligation is a premise
does not close that obligation. An implementation counterexample prevents a
soundness claim for that path; it does not remove that path from the scope.

Source baseline: `78387bb`, rebased onto `origin/microcfta` at `a232f82`.
Retained test adaptation: `aefb1b6`. All 37 fix/proof patches are retained.
The range diff shows only changed README context. The corrected source changes
only measure documentation. All 581 existing
Haskell examples pass on this implementation, and the recorded counterexamples
still reproduce. Earlier reports retain their original source hashes.
The earlier reports are evidence snapshots, not completion reports.

## Coverage ledger

| Area and source modules | Checked foundation | Remaining work |
| --- | --- | --- |
| Term/path semantics: `Path`, `Internal.Tree`, `Generic`, `Simple` | `Language`: finite runs, bounded enumeration, path lookup, equality sharing. | Concrete path/trie constructors, FTA validation, public wrapper correspondence. |
| Constraints: `Constraint`, `Equality.Constraint`, `Refinement.Guard` | `Guards`: Boolean evaluation and splitting. Concrete trie construction, ordered paths, prefix checks and descent. Canonical connected components and congruence saturation. Unconditional termination, exact semantics, constructive finite models, and rejection iff no model exists. | Source ST-array completion, full suspended-path descent, residual guards and public arity wrappers. |
| Interning and recursion: `Interned.Type`, `Interned.Operations`, `Interned.Cache`, `Interned.Memo`, `Interned` | Synchronous graph intersection in `Language`. `Cache`: fresh identities, first-writer insertion, finite interleavings, memo results, sharding with collisions. | Runtime map/atomic/type-cast correspondence, binder-shape keys, binding/substitution, recursive conversion, union, intersection scheduling, depth bounding, redundant-edge removal. |
| Enumeration: `Enumeration`, `Internal.UnionFind`, `Equality.Operations` | `Language`: reference enumeration and sharing. `UnionFind`: exact terminating state operations. `Fragments`: hole resolution, slot intersection, assimilation, and combined union/assimilation assignment semantics. | Caller/machine/live-slot invariants, concrete suspended paths, expansion scheduling, graph narrowing, full constrained enumeration, recursion markers versus finite denotation. |
| Refinements: `Refinement.Evaluate`, `Expression`, `Verdict`, `LiquidFixpoint`, `Denotation`, `Automaton`, `Template` | Verdict laws, guard classification, first-formal aliases in `Holds`. | Concrete observation construction, substitution, formula interpretation, capture/freshness, API validation, evaluator correspondence and explicit solver contract. |
| Pruning: `Refinement.Prune` | `Observation` and `ObservationGraph`: executable path plans, exact sparse views, graph variants, all-finite-term specialization coverage, homogeneous refinement decisions and successful guard discharge. | Interned representation/memo correspondence, substitution and equality observations, ambiguous-actual fallback, recursive pruning fixed points, termination and remaining errors. |
| Similarity/minimization: `Refinement.Minimize` | Guard classification and finite productivity/below-check in `Minimization` and `Productivity`. | Similarity fixed point, actual graph read analysis, rewrite scheduling, root representative preservation, graph snapshots, complete postconditions. Known counterexamples remain recorded. |
| Integer counting: `Refinement.Lattice` | Concrete linear/formula compilation and exact indicators; normalization and terminating feasibility; all-degree Faulhaber sums; actual piece splitting, repeated elimination, stored levels and cumulative polynomials; derived initial support/metadata; integral nonnegative count; zero count iff no solution; exact integer implication decisions. `LatticeRank`: binary search and rank/select from section counts. | Final cumulative-search/section-table connection, variable-order retries, binding freshening, typed syntax/container/machine-index correspondence and full supported-input error mapping. |
| Ranked core: `Index`, `Ranked.Internal`, `Ranked.Internal.Decoder` | Mixed-radix laws; exact finite plan decoding and normalization. `SizedRank`: inverse ranks and class positions. `PlanVariants`: nested shared/sized constructors, derived counts/order, valid and invalid ranks. | Callback validation, n-ary dispatch, machine-index conversion, indexed-source correspondence and runtime shared storage. |
| Size tables: `Ranked.Internal.Size`, `Gen.Internal.Table`, `Gen.Internal.Recursive`, `Gen.Internal.Recur` | Finite sparse convolution and zero-size coverage. `RecursiveSize`: exact node-count language/count/decoder and bounded probabilities. `MinimumSize`: terminating least-size computation. `TablePosition`: actual bottom-up child/state ranking, derived prefixes/offsets, last-successful selection, exact acceptance/replay. | Concrete graph/Map/Seq adapters, guarded generator recursion, lazy-series productivity, multiple recursive generator occurrences and weighted tables. |
| Sampling: `Ranked.Internal.Sampler`, `Ranked.QuickCheck`, generator QuickCheck modules | Exact rational laws; executable integer-mass conversion, equal-weight grouping, source cumulative binary search and ticket decoding; weighted/uniform/map/product/rejection constructors; structural offsets, finite product indexes, machine-range preconditions and bounded sampler composition. | Concrete Map/array and GHC conversion correspondence, backend laws and retry liveness, recursive sample-index productivity, facade wiring to live size indexes and retained masses on every generator constructor. |
| Shrinking: `Ranked.Internal.Shrink`, inspection functions | Size-retention preservation of the strict-smaller relation. | Complete shrink traversal, validity, rank completeness, ordering, bounds and callback correspondence. |
| Static generation: `Gen.Internal.Static`, `Automaton`, `Flat`, `Support`, `Types` | Finite plan and size/mass laws. | Constructor invariants, language/value/rank/weight correspondence, atomic boundaries, imports, size reshaping and errors. |
| Grouping and joins: `Gen.Internal.Bucket`, `Grouped`, `Join`, `Chain`, `Query` | Concrete finite partition; conditional group and product distributions. | Actual key maps, accepted join groups, n-way joins, group pruning, recursive joins, retained size masses and public weighting policies. |
| Symbolic generation: `Gen.Internal.Symbolic` | Signed-indicator and intersection foundations. | Distinct-intersection union counting, equality classes, indicator compilation, constrained product counting, selection and inverse ranking, count caches. |
| Refinement compilation: `Gen.Refinement.Internal.Compile`, `Witness` | Alias, retained-size, finite closure and per-size mass foundations. | Full recipe compiler, observations, recursive guards, variable closure, hole filling, result refinements, witnesses, solver failure behavior and end-to-end distribution. |
| Public APIs: `CFTA`, `Equality`, `Refinement`, `Gen`, `Gen.Equality`, `Gen.Refinement`, `Gen.Do`, `Gen.Label`, `Gen.Sig`, `Gen.Error`, `Inspection`, `Ranked` | Partial correspondence documented in module notes. | Trace every export to checked semantics; close any wrapper, error or callback obligation; compose the end-to-end theorems. |

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

## Current work

- Connect concrete cumulative polynomial counts to the checked ranker.
- Verify complete shrink traversal and inspection.
- Connect equality completion to the source ST union-find loop.
- Connect union-find and observation results to suspended constraints,
  enumeration state, substitution and recursive pruning.
- Establish the remaining concrete representation and runtime correspondences.

After these prerequisites, continue through the ledger and compose the
end-to-end generation, probability and optimization results. Keep unresolved
findings in the reports. Do not close the goal while required rows remain.
