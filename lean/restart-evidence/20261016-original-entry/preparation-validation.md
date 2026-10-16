# Original field preparation validation

Timestamp: 2026-10-16 06:42 CEST.

Owned source: `lean/MicroCFTA/SourceEqualityOriginalAllocationPreparation.lean`.
SHA256: `008c7078519b784c196aa241608e2eec4eb883b7648943fde0b89cd560d78727`.
The source is frozen at 125 lines.

Focused command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceEqualityOriginalAllocationPreparation
```

Result: terminal exit 0, 1214 jobs. No new warnings. The build replayed the existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion.lean:24`.

Probe command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-original-entry/preparation-probe.lean
```

Result: terminal exit 0. Seven public declaration axiom checks, seven signatures, three kernel examples, and three executable evaluations passed. The declarations use at most `propext`, `Classical.choice`, and `Quot.sound`.

`prepare` executes each actual `ConstraintAllocation.construct` in list order. It passes the returned cache into the next constructor. A failure skips the suffix and retains the exact reached cache. `prepare_complete` derives actual completion, one causal `History`, final `Cache.Valid`, atomic `Cache.Steps`, original origins, and ordered final field readback receipts. `Receipt.retained` retains every earlier canonical entry. `Receipt.load` derives each successful read-only field load from the same final cache.

Executable observations:

- A duplicate empty field after a prior distinct field returns identities `[some 1, some 1]` with final supply 2. The caller's identity 0 remains allocated.
- A valid empty field followed by a malformed field returns the literal trie error with final supply 1. The suffix field is not allocated.
- Contradiction after a prior distinct field returns `[none]` with final supply 1.

The input normalization premise is explicit: every listed guard has `Cached original.equalities`. The program does not normalize arbitrary raw classes. The literal serial schedule does not establish GHC field demand order, global runtime publication, or native container equivalence. No prior proof file, Audit, documentation, Haskell source, or Git state was changed by this task.
