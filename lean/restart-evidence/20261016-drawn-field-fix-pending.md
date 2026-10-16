# Pending source refresh after the literal Scan checkpoint

At 2026-10-16 13:43 CEST, remote readback confirmed formalize at
`9a3e102a3a3d1b7e8212b540c61ebeccc4f8ffc3`. Main had advanced from audited
`5399d3104687343ec8d26f7eaf7a3b008276560f` to
`c0cc8a0582cd6b01c344ec15f949ecb46a72dc0e`. The bounded fetch completed
with exit zero. The new source is fetched, not merged or locally validated.
The full objective remains active. This checkpoint is progress.

## Delta

- PR #64: `4d261d9c`, merged at `ae708b2c`, adds drawn value fields to
  typing rules. New public entries include `drawn`, `typingLTA`, and
  `typingLTAFrom`. Plain builders report `DrawnField`. Pool states and
  `deriveLTAOnPools` connect drawn generators to refinement derivation.
  The documented ranks follow the refinement generators; they need not
  equal `fromTypingRules` ranks.
- PR #65: repair `b9219b9e`, merged at `c0cc8a05`, rejects field atoms for
  fields of the datatype being derived. The invariant applies at each node.
  The regression expects `Left (FieldAtomOnDatatype "Next" 0)` for a
  Chain child pool. Root FINDINGS.md records the failure, repair paths,
  regression, and pending validation in its first repair registry.

The combined delta changes seven paths, with 307 additions and 28 deletions:

1. `cfta-generator/CHANGELOG.md`
2. `cfta-generator/common/Data/CFTA/Gen/TypedArithmeticLanguage.hs`
3. `cfta-generator/src/Data/CFTA/Gen/Refinement/Derive.hs`
4. `cfta-generator/src/Data/CFTA/Gen/Refinement/Derive/Internal.hs`
5. `cfta-generator/src/Data/CFTA/Gen/Typing.hs`
6. `cfta-generator/test/Data/CFTA/Gen/Refinement/DeriveSpec.hs`
7. `cfta-generator/test/Data/CFTA/Gen/Refinement/TypedLanguageSpec.hs`

Source inspection confirms the explicit rejection and added regression.
No new-source build, test, reproducer, format, metadata, or Lean adapter
check has run. The existing Audit of 2456 jobs and 58268 dependency checks,
strict Nix build, and 793 examples plus golden cover source `5399d310`.
Do not attribute those checks to `c0cc8a05`.

## Resume

Preserve every proof, counterexample, marked draft, evidence file, stash,
and other worktree. Snapshot hashes and create a backup before merging.
Keep the optimized interned core. Inspect and merge this exact source delta.
Run the required strict Nix build, all suites, formatter, and package checks.
Rerun the preserved Chain counterexample and confirm the new explicit error.
Keep its historical source and logs unchanged. Update root FINDINGS.md with
the local merge and validation. Add the new error and typing interfaces to
the source-correspondence obligations. Do not assume their semantics from
the earlier typing model or equate their rank orders.

Then resume `20261016-typing-do-seeded-worker/local-worker-next.md`:
retain original records in an additive literal Scan wrapper, compose local
precheck, required children, class editing, parent construction, and the
mutual outer caller. Keep general constrained termination, host execution,
frontend, solver, Sized, and full-library obligations explicit. Push only
verified formalize checkpoints. Do not mark the full goal complete here.
