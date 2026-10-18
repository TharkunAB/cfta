# Actual publication alias and callback-name transport

The new module is `SourceCurrentUsedBinderAliasTransport`.
Its final source SHA256 is `192ccb08a7322c3619781b3886ce491f0a4b72b2914e14d108212d9c29171d2e`.

`Scope` includes live symbolic free-name support and a literal Depth anchor.
`Aliases` preserves equality tests on that scope.
It permits aliases between varying labels and fixed captured names.
It does not follow from arbitrary `StoredProbeCompatibility.Compatible`.
The earlier unrestricted alias counterexample remains valid.

`extend` requires the exact new-local versus old-scope alias equivalence.
`extend_depth` derives this equivalence from the Depth anchor.
It does not require captured Depth names to be fresh.
`extend_fresh` derives it when both new local names are fresh.

`publication` applies the extension to one actual source publication.
Both sides use the same captured values.
The actual Depth callback proves ordinary-name freshness.
The actual missing-key reservation proves interned-name freshness.
The theorem adds no alias, BinderFree, unused-local, Cap, or closure premise.
Captured values can contain arbitrary nested Mu records.

`publication_raw` decomposes both actual raw source calls and both filters.
It retains their literal input states, result states, and growth to afterBody.
The raw free-name sets agree under the paired own names.
All other surviving free names remain literal.

`publication_own` derives filtered own-free membership equivalence.
It combines actual deep observations, actual capture freshness, local normality,
and actual bare-self parity. It covers the used-local branch.
`publication_filtered` derives the full bidirectional free-name correspondence.
It does not equate complete records or their reconstruction results.

`retained` recovers the actual first writer of a selected stored Mu.
It retains the exact key and complete candidate equality.
It retains the missing slot immediately before the first write.
It retains the initial writer prefix and all three callback histories.
It applies the alias and filtered-name proofs to that recovered writer.
It does not replace the stored winner with a later losing candidate.
It does not infer physical growth from arbitrary History.retain nodes.

The integration checks use only source-built contexts, Ready states, and histories.
One source contains a nested used binder under a full guarded node and a root union.
It invokes the retained-writer theorem and checks an exact warm ignored callback.
A second closed source reaches a publication with two captured Depth aliases.
It checks actual stored membership and unchanged Depth names on both callbacks.

The general used-binder output induction remains open.
Free-name correspondence does not imply RootMatch of complete callback values.
The missing step must track full rows, ordered children, literal root alternatives,
and nested selected Mu payloads through actual earlier first-writer chronology.
This component supplies actual input alias facts for that step.
It makes no whole-library completion or Haskell defect claim.
