# Symbolic counter and rank driver

`MicroCFTA/SymbolicDriver.lean` ports the operational core of
`microcfta-generator/src/Data/CFTA/Gen/Internal/Symbolic.hs`. It complements
the general semantic proofs in `Symbolic.lean`.

## Executable scope

The model implements the complete mutual counting driver:

- `countNode` uses the graph-identity cache.
- `countUnion` uses the proved distinct-intersection coefficient fold.
- `countEdge` builds independent child domains and signed path obligations.
- `solve` checks empty domains, normalizes a context, and consults its cache.
- `solveStep` resolves existence and equality targets or multiplies independent counts.
- `unify` merges domains, rejects occurrences, expands constructor equalities,
  and decomposes equal constructors into child equalities.
- `expandVariable` substitutes a selected constructor and introduces fresh domains.

Normalization follows bindings, removes known constructor prefixes, renames
live domains, retains self-equality existence, orders equality operands, and
sorts and deduplicates pending obligations. Free domains remain in the key.
`keyEq_correct` proves that the executable cache comparison identifies exactly
equal normalized contexts. It cannot merge different keys by accident.

The model also implements `constructorsAt`, `selectAt`, constructor block
skipping, left-to-right child conditioning, the singleton decoder, `rankAt`,
and child ranking. Constructor order uses arity, the user key, then the symbol.
The singleton paths evaluate from a cache snapshot and discard their extra
counts, as the source does. The public `unrank` wrapper rejects negative and
out-of-range ranks before selection.

## Checked source-driver examples

These examples run the operational functions. They do not replace the result
with a reference `Fin n` index.

| Case | Checked result |
| --- | --- |
| Equal children, each with two leaves | Count 2; ranks 0 and 1 decode to the two equal pairs; both inverse ranks are correct. |
| Disjoint equal-child domains | Count 0. |
| Rejected mixed pair | Inverse rank is `none`. |
| Colliding user constructor keys | Both distinct terms remain selectable in symbol order. |
| Negated equality | Signed count 2; ranks decode to the two unequal pairs. |
| Overlapping alternatives | Count 3 distinct terms from 4 accepting runs. |
| Nested equality below optional wrappers | Expansion rejects missing positions and retains both valid equal terms. |
| Insufficient execution bound | A separate `fuelExhausted` error, not count zero. |

`equality_example_count_and_decoder` combines the actual count, decoder, and
inverse results for every rank in the two-term example. The nested and overlap
fixtures exercise counting only. Their unused selection callbacks do not
constitute additional selection claims.

All example proofs use kernel-checked computation. The generic fragment,
target, obligation, and cache-key equality proofs use structural induction.
No proof uses native evaluation or an added axiom.

## Representation boundaries

Node identifiers and the graph operations `intersect`, `condition`, and
`project` are explicit interfaces. The source obtains these operations from
its interned graph implementation. The pair example supplies a concrete
finite graph family closed under its intersections, conditions, and
projections. `Symbolic.lean` separately proves the semantic intersection,
projection, and constructor-partition requirements.

Each edge supplies the signed equality indicators that the source obtains
from `Constraint.indicators`. The model does not admit a missing indicator
interpretation. The source treats that case as an internal error. A valid
indicator list must evaluate to zero or one on each term.

Edge intersection multiplies the supplied indicator polynomials. The source
can simplify or canonicalize a conjunction before interpreting it. The model
can therefore retain more equivalent intermediate keys. It also retains
structurally empty intersections until their contribution is counted as zero.
The signed-map preservation proofs justify these algebraic choices, but no
verified Haskell translation establishes their full implementation connection.

Finite lists represent maps and sets. The source uses ordered maps and a
shared `IORef`. This model preserves the pure count-state flow. It does not
model concurrent cache updates, memory layout, or balanced-tree cost.

The source does not take an execution bound. The model bounds recursion,
substitution following, and renaming. Failure of a bound is explicit. No
universal sufficient bound is proved for all acyclic inputs. No polynomial
time or space claim is made for arbitrary overlapping constraints.

## What remains unproved

The port is executable and source-specific. It is not yet a proof that every
source execution produces a bijective term ranker. Remaining global proofs
must establish all of the following together:

1. Preservation of domain, binding, occurs-check, and fresh-name invariants.
2. Assignment-count preservation through every normalization and expansion.
3. Termination on every supported finite graph.
4. Correct count reuse across every normalized context and graph identity.
5. Exact source graph conditioning and projection at every selected prefix.
6. The general count/selection/inverse theorem for all supported input graphs.
7. Correspondence between these pure definitions and the Haskell implementation.

The independent exact-language index in `DistinctRank.lean` states the desired
bijection for all valid finite inputs. The source-driver examples here check
that this concrete symbolic algorithm meets it on the listed cases. Those are
different proof claims and remain separate.
