# Checked state retention through current conjunction memo calls

Timestamp: 2026-10-16 06:54 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedConjunctionMemo.lean`.
SHA256: `cba26b96b0bb99358f828dc62cb1175dff76af067acf46199670dfc9386c9c60`.
The 124-line source is frozen. Current Haskell main remains `8f85ddb6`.

Focused command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedConjunctionMemo
```

Result: terminal exit 0, 1143 jobs. The existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion.lean:24` replayed. There are no new warnings. The first attempt exposed a reserved `scoped` binder. The binder was renamed to `scopes` before the final green build.

Probe command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-conjunction-scan/memo-probe.lean
```

Result: terminal exit 0, no warnings. Ten public declaration axiom checks and ten signatures passed. Four kernel integration examples passed. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Scope retention, idle retention, and exact whole-state retention for an unchanged physical result are axiom-free.

## Public endpoints

The namespace is `SourceCurrentAllocatedConjunctionMemo`.

- `ready` derives current conjunction readiness from initial checked `Good`, `SemanticReady`, and `CostHeap`.
- `advance_good` uses actual conjunction `Effects`, machine extension, final constructor facts, and unchanged domain storage to derive final checked `Good`.
- `advance_contextual`, `advance_scoped`, and `advance_idle` retain the actual unchanged native cells. The contextual interpretation stays fixed. These statements do not require a new output law.
- `advance_self` identifies the entire checked state when the physical result is unchanged.
- `Receipt before after` supplies `effects`, `good`, `semantic`, `idle`, `extension`, and literal `tables` equalities. The returned checked state is exactly `SourceCurrentAllocatedQueryMemo.advancePhysical before after`. Cost retention is `receipt.effects.ready.costs`. Equality-cache growth is `receipt.effects.grows`.
- `lift_effects` constructs this receipt from actual physical effects and initial checked validity and idleness.
- `call_effects` applies actual current `ConjunctionMemo.Call.verified`, then derives the checked receipt and final fourth-memo `Correct`, `AnswerSound`, and `Extends`.
- `finite` derives the actual current hit or miss directly from the initial invariants and query availability. It needs no preceding native query, supplied completed decision, final invariant, old eager `Produced`, or result-language callback.

The finite endpoint arguments are `formulas solver budget memo query before good semantic costs idle available correct`. Its result is `exists answer after saved`, followed by actual `SourceCurrentConjunctionMemo.Call budget memo query (physical before) answer after saved`, `Receipt before after`, final fourth-memo correctness, conservative answer soundness, and old-entry retention.

## Kernel checks and scope

The first example composes an actual call with fixed contextual and scope cache invariants. It derives all returned invariants and query availability at the exact advanced heap. The second derives finite completion from an empty fourth memo without a prior query. It retains final physical validity, cost heap, domain cache, memo correctness, and true-answer exclusion. The third derives an exact unchanged checked state for an actual completed hit. The fourth transfers actual constructor-only effects while preserving both completed-cell law families.

Initial `Good`, semantic readiness, cost heap, idleness, query availability, and valid warm fourth-memo contents remain explicit. A cold fourth memo discharges the last condition. Fixed contextual and scope cache invariants are retained when supplied initially; they are not inferred from physical validity alone.

The constructor heap and actual equality-operation state come from the current conjunction graph. Native node and edge table records and the whole domain cache are retained literally. No global source table is reset. The module does not connect a full current Scan, construct a native query, extend a fixed model to generated operands, or establish GHC lazy forcing, pending publication, concrete containers, allocation order, or concurrency correspondence. No earlier source file, Audit, documentation, Haskell source, or Git state was changed.
