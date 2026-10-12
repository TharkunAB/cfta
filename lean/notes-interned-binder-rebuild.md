# Binder reconstruction after closed substitution

`InternedBinderRebuild` follows the local binder branch of
`Interned.Type.substitutionPlan`. That branch restricts the external map to
the binder's free references, overrides the old reference with the new local
reference, constructs a binder, and applies `createMu` cleanup. The earlier
closed-node shortcut returns the original binder unchanged.

`localBindings` and `rebuildAt` execute those map and constructor operations
over the existing finite lexical shape. They preserve the complete edge
payload and the ordered child forest. `rebuildAt_exact` derives the exact
lexical substitution language. Its proof uses the actual environment
restriction, the local reference override, the least binder language, and
the two proved cleanup cases. It does not take an alpha-equivalence or
language-preservation equation as a premise.

The external replacements are closed ancestor instances. This is the
`ClosedEnvironment` property already derived by `LexicalBinderClosure`.
A new identity must be absent from free and nested bound references of the
body. `freshName` computes such an identity from a finite syntax bound, and
`freshName_absent` proves the required conditions. This is a finite witness
for the adapter. It is not the source's counter algorithm. The source counter
and its machine lifetime remain in `InternedIdentityWords`.

`rebuild` combines that reconstruction with the actual closed shortcut.
`rebuild_exact` requires no separate freshness premise because it uses the
computed name. `reused_identity_exact` also permits the old identity when
no nested binder owns it. It proves that old-identity and fresh-identity
reconstruction have the same language. It does not assert that their
interned identities are equal.

`localBindings_resolved` derives that only the new local reference can remain
free in the body when the external environment resolves the original free
references. `rebuild_closed` proves that the constructed result is closed,
including after cleanup. `rebuild_exposed` then applies the actual finite
visited worker from `LexicalBinderClosure` and `LexicalExposureLanguage`.
It derives exactly the substituted lexical language from the emitted rows.
`rebuild_no_unexpected_reference` excludes a raw reference at every later
lexical request. `rebuild_bounded` retains exactly that language through
each constructor-height bound.

## Remaining representation boundary

This is one prepared binder step with closed external values. The source
plan also rebuilds nested binders while it applies the body plan. The module
does not yet prove that complete recursive plan by induction over runtime
payloads. It also does not identify lexical syntax with runtime node IDs.

The source's two-probe interning key, canonical cache hits, cached metadata,
edge sorting, and child cleanup retain their existing representation
obligations. In particular, the finite lexical inventory still needs a
stable structural readback from actual runtime identities. Equality of
languages alone does not establish that readback or bound runtime identity
allocation. The new theorem removes the need to assume language preservation
for this local alpha-renaming and cleanup step; it does not close the full
`LexicalBoundedBuilder.RowsCorrespond` interface.

Validation on 2026-10-12: the pinned Lean toolchain builds
`MicroCFTA.InternedBinderRebuild` and its dependencies (75 jobs). All 13 theorem
audits use only standard Lean axioms. No axioms, incomplete proofs, or
Haskell changes were added.
