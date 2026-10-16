# Hereditary guard foundation validation

Date: 2026-10-16 22:54 CEST.

Frozen sources:

- `SourceCurrentAllocatedFiniteOrdinaryGuardLimits.lean`: 217 lines, SHA256 `7f31d709bba0cc2eb6a530d56c4bb1252cb849942619e813aacba430e7137774`.
- `SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.lean`: 265 lines, SHA256 `a458f6c4c19ef8ca359c524186980445d1c3119f77e16b958f2d8e66b152240f`.

## Numeric foundation

`GuardLimits.Le` compares the stored occurrence count, stored depth, guard-stage count, and exposed Same depth independently.
`join` takes the componentwise maximum.
`step G` is `join G (GuardEnvelope.conjoinLimits G G)`.
Thus the common native step covers both retained input guards and the actual raw conjunction envelope.

The module proves weakening for raw `GuardEnvelope.Bounds`, monotonicity of join, conjunction, native step, and effective-own budgets, and Top bounds at every vector.
Its finite-word proof includes both alphabet-cardinality monotonicity from the frozen constraint module and new word-depth monotonicity.
The actual staged positive budget is monotone in its raw path depth as well as its already proved stage count.
These facts do not assume an actual normalized output or a desired budget conclusion.

`of_constraint` computes an initial vector from the literal stored class lists, their raw path depths, the raw guard's actual stage count, and Same paths in its outer atoms.
`of_constraint_bounds` proves that vector directly.
It needs no cache, normalization, accessor, solver, or output-law premise.
The result is a syntactic envelope; physical normal-form validity remains separate.

## Hereditary predicates

The predicates remain generic in Symbol and Formula.
Their raw edge constraint is `SourceSymbolicIndex.Constraint Formula`.

- Empty nodes have no raw edge guard obligation.
- Ordinary nodes retain the profile of every literal ordered row.
- Each edge retains `GuardEnvelope.Bounds G edge.entry.key.constraint` and the complete profile of every ordered child.
- Mu, bare references, and explicit unions are outside the predicate.

The module provides pure constructor facts, pointwise membership construction, exact own-field and child readback, whole-profile weakening, and finite ordinary domain derivation.
Its computed node, row, edge, and forest limits join EVERY literal original occurrence.
The self-profile theorems need only the corresponding finite ordinary domain fact.
They do not take a hereditary guard bound as an input.

Actual heap constructor results, coherent warm cache hits, checked native execution, Merge execution, and causal stored-result certificates belong to separate producer modules.
The pure fixture in the integration source is not an allocated/coherent heap fixture.
No arbitrary completed result is treated as an initial original record.

## Validation

- GuardLimits direct check 1 failed in local induction elaboration, unavailable max helper names, a conjunction type annotation, and unfolding the Top field. Its exact source and diagnostics remain available.
- GuardLimits direct check 2 passed with `linter.all=true`, terminal exit 0, no diagnostics. Root canonical `guard-limits-build-1.log` passed with 1077 jobs.
- GuardProfiles direct check 1 passed with `linter.all=true`, terminal exit 0, no diagnostics. Owned process 73165 was polled to terminal exit 0. Root canonical `guard-profiles-build-1.log` passed with 1079 jobs.
- Final canonical imported public checks each passed: 25 GuardLimits declaration axiom/signature pairs and 37 GuardProfiles pairs.
- Final canonical imported integration check 3 passed: 6 theorem axiom/signature pairs.
- Both public sources and the final integration source set `linter.all true`, `pp.explicit true`, `pp.proofs true`, `pp.universes true`, `pp.deepTerms true`, `pp.maxSteps 1000000`, and `pp.fullNames true`.
- Final source and imported probe logs contain no warning, error, `sorryAx`, or omitted-term marker. Axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`.
- Canonical logs retain only the historical unused-input dependency warning. This owner ran no canonical Lake process.

Kernel draft 1 exposed an unnecessary explicit decidable-equality hypothesis and an omitted nodeEdges unfolding in a concrete membership proof.
Draft 2 preserved a documentation placement parser failure.
Draft 3 fixes only those probe issues and passes.
All failed drafts and logs remain available and are not counted as passes.

The six integration theorems derive effective conjunction bounds from computed initial vectors, retain effective budgets through a joined native step, read a second-level raw descendant guard from a computed original forest envelope, construct a literal conjunction edge within the native step, cover the exact Top/Empty sentinel shape at any vector, and cover a concrete guard with stored equalities, large natural indices, Same, Or, and Not.

## Preserved boundaries

The stored path count includes raw occurrences, not only classes.
The finite alphabet argument does not bound index magnitude or infer an arity range.
The preserved formal paths use natural indices; signed Haskell conversion remains unproved here.
This component gives no instruction count, general recursive progress, whole-root capacity plan, or whole-library Haskell correspondence theorem.
The full library remains the objective.

No older source, Haskell, Audit, root document, or previous evidence changed. This owner ran no Git or Lake command. Final owned text has one final newline and no blank line at EOF. No compiled artifact is stored in the evidence directory.
