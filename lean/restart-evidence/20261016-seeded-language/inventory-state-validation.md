# Actual inventory state validation

Date: 2026-10-16 07:58 CEST.

Owned source: `lean/MicroCFTA/SourceCurrentAllocatedNativeInventoryState.lean`.

Source SHA256: `4944b25b19d4a897a49faedff94205058d4fbcf0e0fecafbcc40bb3d026998fc`.

The focused canonical build passed with exit status 0 and 1189 jobs. It reported only the existing `InternedFreshOrdinaryClosedCompletion` unused-input warning. The canonical build slot was released to the root immediately after completion.

The pinned direct public probe passed with exit status 0 and no warnings. It checks four public theorem axiom sets and seven full public signatures. Four named integration kernels also have axiom reports and full signatures. The resulting eight axiom sets use only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` occurs.

Commands:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeInventoryState
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-seeded-language/inventory-state-publicprobes.lean
```

## Public interface

`Inventory` stores the actual source heap, its Facts, the finite root list, Original proofs, root availability, and closedness. `Inventory.inputs inventory holds` computes `InventoryModels.finiteInput` from those stored fields.

`At formulas solver inventory state` stores Contextual, all-phase Covered, source heap growth, and issued identity extension. It does not contain a future result, a query completion callback, or a future model law.

`At.advanceNative current machine extension` retains the computed model and native cell invariants through an actual machine extension. `At.advance current afterPhysical extension` proves the same result for literal `AllocatedQueryMemo.advancePhysical`, including its returned operation state.

`initial inventory formulas solver width machine operations growth history` derives At for empty native tables. It allows arbitrary operations. It does not assert Good or physical field readiness for those operations.

`query_complete inventory formulas solver state good current scopedCache semantic idle left right leftAvailable rightAvailable leftClosed rightClosed ranges` returns:

```
exists next fuel value after,
  next.source = state.native.machine.heap and
  next.roots = inventory.roots ++ [left, right] and
  CoveredQuery.Receipt next.source formulas solver (next.inputs holds)
    fuel left right state value after and
  At formulas solver next after
```

The new Inventory is an actual data value. Its physical source is the pre-query heap. Its root proofs and availability come from `CoveredQuery.generated_complete`. Its final At comes from that same query receipt.

## Kernel integrations

1. `cold_initial` uses the literal native initial state over the inventory heap, empty domains, and arbitrary equality operations. It supplies no contextual result law or request coverage.
2. `physical_advance` uses the requested implicit At parameters. It checks both native tables are unchanged and the checked operation state is exactly the returned physical equality state.
3. `query_exact` derives literal checked done, resident closed output, exact original left/right intersection language, the actual next Inventory, final At, and both weaker returned-cache invariants.
4. `two_queries` uses the first generated output in the second query. The first receipt supplies Good, scope, semantic readiness, idle state, output availability and closedness. Its At supplies the new model and all-phase causal coverage. The second request adds only its reached WordRanges. Both inventory source/root equations and both literal done observations are retained. The final result has the original left/right intersection language.

## Scope

Good, Scoped, SemanticReady, Idle, current operand availability and closedness, and reached WordRanges remain separate query premises. Initial warm At is explicit, or is derived for empty tables by `initial`. No desired output language, final model-validity premise, future cell coverage, or completed child callback is supplied to the query wrapper. The module does not prove the whole seeded fold, source runtime correspondence, or solver IO semantics. The root composes the seeded fold separately.

Only the one new proof source and new evidence files were written. No old proof, Audit, documentation, Git, or Haskell file was edited.
