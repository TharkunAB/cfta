# Derived semantic name bounds

`SourceSemanticNames.lean` derives the finite name set for source scope
transport. It includes observed refinement free names, literal requirement
free names, and constructor names at symbol-sensitive positions. It excludes
constructor names read only for their refinements.

`ambient_reads` proves exact equality of that list across equal guard reads.
`ambient_used` proves that each source allocator avoids every name in it.
The live set adds the first pass's executed actual-value stream. The second
stream avoids every live name that the spelling map does not map. Thus
`live_injective` derives the scope theorem's injectivity premise from the
actual source map. `ambient_fixed` derives its fixed-name premise.

`allocated_fresh` and `declaration_fresh` prove that neither allocation nor
per-path lookup introduces values outside that actual stream. `resolve_live`
then proves source record closure: the formal name and logical actual name
are live, and the spelling map fixes the formal. `resolveMany_live` proves
the same condition for every entry of every successful source scope. It
does not require unique formal names.

These results discharge the name-bound premises of SourceScopeEnvironment
for ordinary source-resolved scopes. Composition still needs a paired stack
of successful resolutions and the full query's ambient assumptions. Holds
also introduces its contract-formal names and aliases, which require their
own bound. Sorted solver declaration domains and the non-injective ambiguous
actual quotient remain separate obligations.

Validation: `lake build MicroCFTA.SourceSemanticNames` succeeds with the
pinned toolchain. There are no proof placeholders or new axioms.
