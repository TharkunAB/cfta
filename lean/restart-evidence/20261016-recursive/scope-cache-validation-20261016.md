# Syntactic returned-cache scope validation

Validated at 2026-10-16 06:09 CEST.

The new module is `MicroCFTA.SourceCurrentAllocatedNativeScopeCache`. It has 208 lines. Its frozen SHA256 is `8feccd12a39470a81738e635283e6dd9b31f716590db40894f6f5db089c78a00`.

## Result

`NodeLaw request result` is `SourceRecursiveIntersectionResultScope.Scope request.domain.key.seen result`. `EdgeLaw` uses the corresponding ordered-child `EdgeScope`. `Scoped` requires these laws only for returned node and edge cells. The definitions are generic in Symbol and Guard. They have no language model or guard interpretation parameter.

The module proves empty initialization, arbitrary machine advance, actual lookup and demand preservation, and finish preservation for the exact evaluating request. A finish takes an independently proved local syntactic scope. It does not take a parent language law or completed parent execution.

Warm ready-hit adapters combine the separate physical cache invariant with `Scoped`. Physical key checks identify the exact original request. The adapters return its scope, final `Scoped`, the unchanged demanded state, and result availability or edge residency. Start adapters return exact request identity, physical validity, `Scoped`, and the literal evaluating cell.

## Checks

Focused command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeScopeCache
```

Result: terminal 0, 1063 jobs. The only warning is the older unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion`. No warning comes from the new module. The focused build log is `scope-cache-build-20261016.log`.

Standalone probe command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-recursive/scope-cache-public-probes-20261016.lean
```

Result: terminal 0, no warnings. All 12 public theorem axiom reports and 12 signatures pass. The axiom sets use only `propext` and `Quot.sound`; two theorems use no axioms. All 12 kernel examples pass.

The examples check empty scope, machine independence, node and edge publication, demand after publication, empty-domain node and edge closedness, exact finish from a closed local result, repeated-pair membership, exclusion of ordinary references, and closedness after an actual warm ready hit.

## Scope

This module supplies cache lifecycle support. It does not derive the local result scope of a recursive body or construct a completed query. A warm cache must satisfy the independent physical and syntactic invariants. Admission from actual histories belongs to the interpreter composition. Machine-key range checks remain explicit in hit and start adapters. The module does not claim runtime or GHC publication correspondence.

Only the new module and new evidence files were written. Every older proof file remains unchanged by this task. No Haskell, Audit, documentation, or Git mutation was performed. No owned process remains.
