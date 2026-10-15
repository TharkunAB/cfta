# Delayed worklist traces and inventories from actual entries

Captured task operations now instantiate the local physical laws. Read
[the current proof and source limits](notes-source-emptiness-tasks.md).
The next targets below retain their historical checkpoint scope.

Source main remains `a22b2ad46ffcad57a77b64447c18da7b0850f52f`.
Starting checkpoint: `c0ae83a2`. New proof checkpoint: `2a1e918e`.
Read [the preceding table proofs](notes-emptiness-table-source.md) for the
finite fixed point, source exposure, projection, and native class folds.

## Reached delayed traces

`DelayedEmptinessExplore.Entry Task Value` stores the exact admitted key,
original forced value, and ordered delayed task rows. `Trace` retains each
actual force and exposure with its returned heap. Each reached head task is
forced before the empty, budget, seen-key, and closure tests. An admitted
value is then exposed. Its row tasks precede the old pending tasks.

The trace proves these properties:

- Existing lookups retain the same complete entry and delayed rows.
- Fresh admissions preserve unique keys.
- The returned table has an admission prefix with length at most the budget.
- Every initially queued task has an actual force receipt before completion.
- Every new stored entry has its actual force and exposure receipts. Its
  encoded item has the stored key and a true closed flag.
- Every task in a new stored row has an actual force receipt before completion.
- Zero budget leaves the table unchanged. It still permits effects from
  forcing all queued tasks.

These are properties of reached finite traces. The proof does not require
arbitrary force or exposure calls to complete. It does not derive their
completion, native heap validity, source task sharing, or semantic row laws.
Task receipt witnesses retain the actual call states. They do not supply a
final-heap task decoder or identify two separate force occurrences.

## Inventory from the literal stored entries

`SourceEmptinessInventory.Records heap entries` requires each actual entry
value to be available and closed in that heap, with its exact untagged key.
`inventory` certifies the values in the same list through `List.attach`.
It retains their exact order. It does not take an arbitrary inventory.

Literal table-key equality derives complete inventory coverage. The finite
search returns an original entry value with its exact key. Common-heap
coherence then derives the existing physical `Readback` law. No separate
inventory, coverage, or answer-function premise is required.

For a delayed table, use its literal entry projection:

```lean
finalEntries.map (fun entry => (entry.key, entry.value))
```

This projection does not force task rows. The actual native trace must still
derive `Records` in one common final heap. Its completed row readout must
retain exactly those entry keys. The key helper still uses `Int.ofNat`.
Machine-Int allocation capacity and identity reuse remain separate targets.

## Next source connection

Instantiate `Task`, `Force`, and `Expose` with actual captured class tasks.
Exposure must retain original children before suspended class intersections.
Each class task must retain its captured original forest. Its first force
must run the proved native fold at the reached state and retain the result.
Later reads must use that same result. Do not precompute all class folds
before child traversal.

Derive availability, closure, normalized stored fields, and old-record
retention through those actual operations. Use these facts to derive final
`Records`. Use force receipts to read completed task rows from the final
state. Then connect the actual table supply and certified primitive laws to
the proved table soundness for each source oracle call.

Transfer the scoped native fold leaves to the newer checked constraint
allocation state. Keep word-range checks and general native completion as
separate obligations. Compose both gate modes and all three memo families
through the current lazy refused-class scan, selected fallback, and caller.
Whole current reduction and general recursive completion remain unproved.

The full library scope remains open. This includes source/runtime
correspondence, derived-refinement interfaces, named measures, getAllAtPath,
decision-model, parser/decoder bridges, recursive generator composition, and
extraction. Keep exact Sized classes per node count, finite class execution,
canonical sequence, distinct size order, and both signed inverse directions
as separate contracts.

## Validation and preservation

Both new modules build without warnings. The full pinned Lean audit passes
2,008 jobs and 51,372 theorem dependency checks. Only propext,
Classical.choice, and Quot.sound occur. The prior unused-input warning in
`InternedFreshOrdinaryClosedCompletion` remains. Logs:

- `/tmp/mcfta-delayed-emptiness-audit-20261015.log`
- `/tmp/mcfta-delayed-emptiness-explore-axioms-20261015.log`
- `/tmp/mcfta-source-emptiness-inventory-axioms-20261015.lean`

All prior Lean definitions remain unchanged except two additive Audit
imports. All Haskell package trees match `c0ae83a2`. The prior Nix tests,
formatting, metadata checks, and separate Sized probes were not repeated.
All prior proofs, counterexamples, marked drafts, external drafts, stashes,
and other worktrees remain.
