# Complete Holds query formulas and declarations

`SourceContractNames.lean` proves that the concrete source prefixes for
actual names and positional contract names are disjoint. It extends the
finite live-name set, injectivity proof, and constructed reverse environment
to every contract variable. The caller does not supply a freshness premise.

`SourceContractSemantics.contract_ext` covers the complete source contract
formula. The proof retains every value-substituted positional refinement.
It also retains the equality aliases for repeated target paths, including
the source first-occurrence lookup. Repeated paths do not lose their aliases.

`SourceHoldsQueries.contract_related` connects successful source observation
lists to that formula proof and to the full nested substitution stack.
`antecedent_related` adds all ambient actual assumptions.
`domain_exact` identifies the domain predicate with the actual appended and
deduplicated declaration list. `domain_related` preserves both positional
value-sort declarations and the source actual declarations.

`query_iff` proves mathematical entailment equivalence of complete Holds
queries across read-equivalent source cells, with arbitrary nested scopes
and conflicting actual names. Both environment maps are constructed from the
source tables. The requirement's free-name premise follows from the outer
guard's requirement list; negation preserves those free names.

The complete ambient solver context and exact incomplete-solver verdicts
remain external conditions. The theorem does not assert that every
mathematically equivalent query receives the same Yes/Unknown response.
The sparse-to-complete identity quotient is also separate: a complete term
can merge actual classes that a sparse observation leaves undecided.

Validation: `lake build MicroCFTA.SourceHoldsQueries` succeeds with the pinned
Lean toolchain. No production source changed.
