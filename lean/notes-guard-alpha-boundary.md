# Solver uncertainty and fresh-name spelling

`GuardAlphaBoundary.lean` gives a checked counterexample to exact operational
guard homogeneity under a merely sound incomplete solver. The callback
returns Yes only when the consequent is Top and a declaration uses
`__microcfta_actual_0`. It returns Unknown otherwise. `solver_sound` proves
this callback sound for every formula interpretation and every declared
environment domain. The callback is a pure function, so repeated identical
queries are stable.

The guard substitutes two leaf actuals with the same constructor name into
different formals, then asks one refinement-only position to satisfy Top.
The actuals have different annotations, so their structural identities are
known. Both actual-ambiguity sets are empty. One term's last leaf is named
`ordinary`; the other is named `__microcfta_actual_0`. Their source grouping
signatures are identical because that position needs only its refinement.

The complete avoid lists nevertheless contain those literal constructor
names. The first term allocates actual names 0 and 1. The second allocates
names 1 and 2. The callback returns Yes for the first query and Unknown for
the second. Kernel checks prove this for the actual sparse evaluator and the
public complete-term evaluator. `lean/repro/GuardAlphaBoundary.hs` confirms
the same `(Yes,Unknown)` pair with the current Haskell public evaluator.

This is not evidence that pruning accepts a mathematically invalid liquid
term. Both requirements are valid Top entailments. It is also not a defect
claim of an unsound result from the supplied Z3 implementation. The counterexample separates two
specifications: preservation of mathematical liquid meaning and exact
preservation of the public evaluator's confirmed Yes/Unknown behavior.
Soundness alone cannot establish the latter across fresh-name changes.

The same repro also uses the supplied `withZ3` backend with the unused ambient
declaration `__microcfta_actual_0 : Int`. It prints `(Unknown,Yes)`. The first
query allocates that name. `freshDeclaration` rejects a generated name which
already exists in the backend's ambient declaration set, so the query returns
Unknown. The second term makes the guard allocator skip that name, and Z3
proves the Top query. The guard allocator's avoid set does not include unused
ambient backend declarations. This is a conservative completeness boundary.
It does not admit an invalid term. Exact operational name invariance needs an
ambient-declaration compatibility condition as well as solver stability.

`SourceAliasTransport.lean` states the distinction precisely.
`decideWith_alias_sound` transports the actual source No-to-Unknown decision
through name identification. It needs per-query soundness and preservation
of admitted sort domains. A known identity also needs environment lifting
for the query's free names to transport a refutation. Unknown identities
require no such lifting because the source suppresses that refutation.

`RenamingStable` is an additional solver contract for exact operational
agreement. It preserves the whole verdict under a lossless, domain-preserving
name replacement. `known_renaming_exact` proves exact source query agreement
under that contract. This contract is not assumed for the mathematical
soundness theorem. It is stronger than stability on repeated identical
queries and is not inferred from solver soundness.

`SourceScopeQueries`, `SourceSortedQueries`, and `SourceHoldsQueries` now
construct the required maps and domain evidence for read-equivalent sparse
cells, including conflicting names and complete nested queries. The
sparse-to-complete identity quotient remains a separate transport problem.
The proved mathematical equivalence does not imply exact operational
verdict agreement for the backend behavior shown here.

Validation: `lake build MicroCFTA.SourceAliasTransport` succeeds with the
pinned toolchain. All counterexamples use kernel reduction. The source repro
runs under `nix-shell` with `cabal exec -- runghc -package=microcfta`; it printed
`(Yes,Unknown)` and `(Unknown,Yes)`. Fourmolu formatted the repro. No production
code changed.
