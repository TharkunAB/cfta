# Original checked entry from causal allocation history

Validated at 2026-10-16 06:41 CEST.

The new module `SourceCurrentAllocatedNativeOriginalHistory.lean` has 151 lines. Its frozen SHA256 is `e15c43f3681aefaf0fce08d8ee8c579f537606a1002ae5361feeb0b8a8ff14d1`.

`History.cached` derives normalization for every listed literal from the actual constructor events. Interleaving preserves that fact. It needs no cache-validity premise. `History.cached_inventory` transfers normalization through original guard coverage. `History.syntax_valid` derives the original constructor's syntax predicate, including all nested children and binder bodies.

`History.fields` combines those normalized literals with their retained actual allocation origins. Actual annotation construction retains both properties at every physical edge key. Existing read-only lookup then derives `FieldAvailable` in `MemoAllocation.initial final`. No successful final load or future field property is a premise.

`constructed width history initialValid expression covered value heap built` returns, in order:

1. `Good` for the literal cold native state with empty domain/native tables and equality operations initialized from the history's final interner.
2. `SemanticReady heap`.
3. `Available heap value`.
4. `value.free = []`.
5. `Original value`.

Actual closed construction derives heap facts, semantic readiness, availability, and cached free-list closedness. `closed_original` derives Original from the same coherent heap. Initial physical cache validity and operation validity follow from those derived facts and the causal history. No initial `Good`, `SemanticReady`, independent per-literal Cached/allowed predicate, field load, output syntax, or model law is supplied.

Focused command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeOriginalHistory
```

Result: terminal 0, 1235 jobs. Only the older unused `inputs` warning occurs. The new module has no warning. The raw log is `history-build-20261016.log`.

Standalone command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-original-entry/history-public-probes-20261016.lean
```

Result: terminal 0, no warnings. Five public axiom reports and five signatures pass. Only standard `propext`, `Classical.choice`, and `Quot.sound` foundations occur. All nine kernel examples pass. They cover empty history, actual constructor normalization, interleaving, covered syntax, same-cache ready field readback, actual empty and missing-variable branches, actual allocation plus finite recursive construction for both binder modes, and derivation of Original for arbitrary selected closed resident operands.

The causal allocation history, validity of its initial equality cache, original literal coverage, and actual completed fresh ordinary build remain explicit. The history records prior operations. The theorem does not establish an eager Haskell allocation schedule, runtime object identity, publication, or machine bounds.

Only the new proof module and new evidence files were written. Frozen old proofs, Audit, docs, Haskell, Git, and board state were not changed. The following composition review is separate source-read evidence in `history-root-review.md`.
