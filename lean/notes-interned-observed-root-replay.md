# Observed replay through root union normalization

`InternedRootAlternativeLists` proves that removal of a selected bare
reference commutes with source flattening and ordered identity removal.
The result preserves list order and complete retained values.

`InternedObservedRootAlternatives` extends the existing absence observation
with reflection of paired bare local references. `union_self_iff` derives
that reflection through the actual union constructor. `deleting_observed`
derives exact output equality for two deleting root filters from clear
retained alternatives. It does not assume equality of the retained lists.

`InternedNormalizedUnionReplay.filtered_as_request` includes every source
union branch except singleton self. The equation retains the original
union request and its cache effects. It executes the stripped canonical
request at the actual intermediate state. Flat and nonempty source members
derive the required normalization equations.

`InternedObservedUnionReplay.filtered_same` combines these laws with
`InternedUnionAlternativeClear`. Paired observations on the original
flattened alternatives and absence of forbidden boundaries in the first
filtered output imply exact complete output equality. The theorem covers
ordinary node merging, duplicate removal, singleton collapse, and both
self-filter decisions. It uses a common extension of the actual histories.
It does not assume callback keys are equal.

`InternedBoundaryFreeAge.free_source` places each actual free name at a
literal boundary or in the free set of an available boundary Mu payload.
`build_free_below` uses actual nested execution and old-record provenance
to show that old boundary identities imply old issued free names.
`build_filtered_free_below` and `callback_free_below` retain that conclusion
through the actual root filter, including new ordinary cache records.
The cutoff is the counter before the stated source call. No age condition
is required for ordinary node or edge identities.

These theorems discharge local cases of the general relational argument.
The full nested constructor induction must still derive the paired root
observations through dynamic Mu requests and smart cleanup. In particular,
the first-run closed-Syntax no-pending theorem is not proved here. The
source may return an old unused body that differs from both normalized
probes; `InternedOldBodyProbeAliases` remains the checked counterexample
to that proof shortcut.

Validation uses the pinned Lean 4.34.1 toolchain. The focused module build
and isolated theorem dependency audit check these statements. No new
Haskell test or source change is part of this group.
