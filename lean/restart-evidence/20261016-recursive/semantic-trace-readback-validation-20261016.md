# Actual physical child trace readback

Date: 2026-10-16 05:53 CEST.
Read-only validation HEAD: `4d74d00c5bf99e3f06447d5b68ecbed72ff2d8e9`.
Source: `lean/MicroCFTA/SourceCurrentAllocatedNativeSemanticTraceReadback.lean`.
SHA256: `ee32a30dc63699b7d4c6a4937d3a827828d871c50154bee22023da53b4636dc9`.
Length: 267 lines.

## Derived result

- `inputs_before_bind`, `code_fields_before_bind`, and `fields_before_bind` recover the earlier instruction checks from an appended control.
- `after_step` derives the exact physical remainder after the actual yielded first step. `current_inputs` derives its current physical check.
- `bind_inverse` derives both actual physical traces from a completed appended physical trace. It determines the child result, full intermediate state, and exact sum of their step counts. No future child result or completed walk is a premise.
- `effects` derives reached `Good`, machine `Extension`, heap `Keeps`, operation growth, and continuation fields from initial `Good`, initial fields, and the actual physical trace.
- `bind_readback` combines the split and physical effects and retains the actual prefix and continuation `WordRanges`. Each resulting physical pure-return trace also supplies its own `Trace.plan`.
- `walk_readback` derives an indexed raw ordered walk containing the actual physical child traces and results. `Walk.trace` composes it back to the literal source code. `cons_readback` derives the first actual result and tail with all intermediate physical invariants, tail fields, and both word plans.
- `work_readback` derives a terminal work instruction's literal result and full returned state. `walk_work_readback` combines actual child walk readback with the terminal constructor and its actual `WorkInputs` check.

The helpers are generic over result types. They preserve the entire checked native and operation state, not only the constructor heap.

## Scope

These are physical trace inversion and prefix effects. They do not assert a parent language law or assume a supplied whole semantic walk. The module takes no semantic callback. The joint semantic induction must apply its smaller-request hypothesis to the derived actual child traces and thread its contextual cache invariant in source order. The separate request-result component derives each actual returned node's availability or edge's residency.

The generic terminal `WorkInputs` receipt is exactly the check recorded by the trace. It must not be enlarged to an unstated property of every original argument. In particular, node normalization can reduce the emitted work to a pure empty result. That generic work check alone does not establish residency of every discarded original row.

Initial `Good`, initial field checks, and actual-prefix `WordRanges` remain explicit where used. The module derives intermediate invariants. It does not derive machine word bounds, recursive child completion, contextual result laws, or the global checked query theorem. It does not replace checked execution with an older eager interpreter.

## Validation

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeSemanticTraceReadback
```

PASS exit 0, 1103 jobs. The only warning is the existing unused `inputs` binding in `InternedFreshOrdinaryClosedCompletion`. This new module has no warning. Log: `semantic-trace-readback-build-20261016.log`.

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-recursive/semantic-trace-readback-public-probes-20261016.lean
```

PASS exit 0, no warning. All 13 public theorem axiom reports, 13 public signatures, and 10 kernel checks pass. The maximum axiom set is `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom or `sorryAx` occurs. The source has no `sorry`, `admit`, or `axiom` declaration.

Kernel checks cover zero-step bind splitting, actual read result splitting with a distinct continuation type, terminal pure work, empty prefix effects, empty and singleton raw walks, exact read-step removal, same-cache field inversion, earlier optional-binder availability checks, and derived nonempty tail invariants and ranges.

## Preservation

Only this new module and owned evidence files were written. No frozen proof, sibling source, Haskell, Audit, repository documentation, or Git state was mutated by this task. The source snapshot and updated owned SHA256 manifest are in this directory. No owned process remains.
