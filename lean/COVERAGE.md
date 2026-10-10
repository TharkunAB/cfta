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

Source baseline: `adb1f012b336ba0d1673f8fd7f310ad75bdfaf04`.
The earlier reports are evidence snapshots, not completion reports.

## Coverage ledger

| Area and source modules | Checked foundation | Remaining work |
| --- | --- | --- |
| Term/path semantics: `Path`, `Internal.Tree`, `Generic`, `Simple` | `Language`: finite runs, bounded enumeration, path lookup, equality sharing. | Concrete path/trie constructors, FTA validation, public wrapper correspondence. |
| Constraints: `Constraint`, `Equality.Constraint`, `Refinement.Guard` | `Guards`: Boolean evaluation and splitting. `Language`: path equality. | Concrete normalization, trie merging, contradictory constraints, residual guards, arity checks. |
| Interning and recursion: `Interned.Type`, `Interned.Operations`, `Interned.Cache`, `Interned.Memo`, `Interned` | Synchronous graph intersection in `Language`. | Identity invariants, fresh allocation, hash collisions, concurrent insertion, memoization, binding/substitution, recursive conversion, union, intersection scheduling, depth bounding, redundant-edge removal. |
| Enumeration: `Enumeration`, `Internal.UnionFind`, `Equality.Operations` | Reference enumeration and immediate-child sharing in `Language`. | Persistent union-find, suspended path constraints, expansion scheduling, assimilation, graph narrowing, full constrained enumeration, recursion markers versus finite denotation. |
| Refinements: `Refinement.Evaluate`, `Expression`, `Verdict`, `LiquidFixpoint`, `Denotation`, `Automaton`, `Template` | Verdict laws, guard classification, first-formal aliases in `Holds`. | Concrete observation construction, substitution, formula interpretation, capture/freshness, API validation, evaluator correspondence and explicit solver contract. |
| Pruning: `Refinement.Prune` | Abstract partition/discharge laws in `Guards`; concrete first-key list partition in `Sized`. | Path plans, variants, observation homogeneity, specialization coverage, recursive pruning, termination and error behavior. |
| Similarity/minimization: `Refinement.Minimize` | Guard classification and finite productivity/below-check in `Minimization` and `Productivity`. | Similarity fixed point, actual graph read analysis, rewrite scheduling, root representative preservation, graph snapshots, complete postconditions. Known counterexamples remain recorded. |
| Integer counting: `Refinement.Lattice` | Signed indicators, selected linear arithmetic, projection and interval summation in `Lattice`. | Concrete linear parser, map normalization, feasibility elimination, polynomial algebra, Bernoulli/Faulhaber construction, elimination levels, integrality, count/rank/select, entailment and supported-input errors. |
| Ranked core: `Index`, `Ranked.Internal`, `Ranked.Internal.Decoder` | Mixed-radix laws; exact finite plan decoding and normalization in `Decoder`. | Full plan constructors, callback validation, n-ary dispatch, `PlanSized`, reverse rank, machine-index conversion, indexed-source correspondence. |
| Size tables: `Ranked.Internal.Size`, `Gen.Internal.Table`, `Gen.Internal.Recursive`, `Gen.Internal.Recur` | Finite sparse convolution, zero-size split coverage, size retention. | Exact node-count recursive language/count/decoder, least sizes, guarded recursion, lazy-series productivity, rank/size inverse operations, multiple recursive occurrences. |
| Sampling: `Ranked.Internal.Sampler`, `Ranked.QuickCheck`, generator QuickCheck modules | Finite exact rational distributions, tickets, products, conditioning, grouping and per-size weight formulas. | Concrete sampler construction, binary search, integer mass conversion, rejection termination, backend laws, bounded sampling and retained masses on every constructor. |
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

- Prove the exact node-count table recurrence and its recursive term coverage.
- Derive observation-path coverage and homogeneity from executable construction.
- Prove cumulative-count binary search and lexicographic rank/select.
- Prove persistent union-find lookup, path compression and class merging.

After these prerequisites, continue through the ledger and compose the
end-to-end generation, probability and optimization results. Keep unresolved
findings in the reports. Do not close the goal while required rows remain.
