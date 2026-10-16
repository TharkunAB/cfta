# Checked original reference meaning

Date: 2026-10-16 05:31 CEST.
Read-only validation HEAD: `554a116f5b0a488c234aa161c801b2178f6a146d`.
Source: `lean/MicroCFTA/SourceCurrentAllocatedNativeReferenceMeaning.lean`.
SHA256: `6ebc24a3e9dd2b72b081f7559d1fda9a106900ea19199989ad2e0458e59fa621`.
Length: 213 lines.

## Derived result

- `bindings_available` derives the actual available Mu payload family from `OriginalBindings`. `bound_original` uses actual resident reference injectivity to derive original scope for the exact selected available binder.
- `bound_record` combines typed source keys, original available bindings, and source name membership. `SourceRecursiveIntersectionSchedule.lookup_record` derives the actual Mu payload and its identity. The result includes original scope, source availability, concrete source key lookup, semantic domain lookup, physical domain lookup, and raw physical readback. No desired lookup result is a premise.
- `left_inputs` and `right_inputs` derive each resolved child's model validity with `InputMeaning.reference_valid`. The exact bound Mu and its source reference have the same independent language and the same finite rank. No additional whole-inventory validity law is needed.
- `left_law` and `right_law` transport the local law for the resolved child to the reference parent. The right law retains the original operand order.
- `reference_trace` derives exactly one actual source read before the exact child trace. Current availability and coherent readback derive the read result. The read leaves the entire reached native and operation state unchanged. `left_node_trace` and `right_node_trace` expose these traces for the actual selected `compileNode` branches.
- `left_body` and `right_body` derive exact `execute (fuel + 2)` completion, the parent contextual node law, heap retention, and output availability. They derive the original bound and current read from source bindings and actual source-to-prefix heap retention. The returned full state is exactly the child's returned state.

The original input model remains fixed at `view source holds`. Later heap growth does not change that model.

## Scope

The exact reached resolved child still supplies its local `NodeLaw`, actual checked `Steps`, heap retention, and available output. These are recursive induction hypotheses. No same-parent law, old eager interpreter, desired successful reference result, or future global finish plan is supplied.

Typed and original source bindings, source availability of the selected Mu, source name membership, and its exact identity remain explicit physical scope facts. The resolver derives such a selected Mu from those bindings. The source-to-prefix `Keeps` premise is a current prefix invariant. It derives current readiness and current availability for the actual read.

The selected branch premises remain explicit for the `compileNode` traces. A missing source binder remains the literal diagnostic; this module does not turn that branch into a completed query. The module does not prove recursive child completion, the global checked node theorem, contextual Mu body induction, cache finish validity, or whole-source correctness. It makes no new cost, annotation, equality-cache validity, or contextual-cache preservation claim beyond the stated conclusions.

## Validation

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeReferenceMeaning
```

PASS exit 0, 1078 jobs. The only warning is the existing unused `inputs` binding in `InternedFreshOrdinaryClosedCompletion`. This new module has no warning. Log: `reference-meaning-build-20261016.log`.

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-recursive/reference-meaning-public-probes-20261016.lean
```

PASS exit 0, no warning. All 12 public theorem axiom reports, 12 public signatures, and 10 kernel checks pass. The maximum axiom set is `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom or `sorryAx` occurs. The source has no `sorry`, `admit`, or `axiom` declaration.

Kernel checks cover independent language identity, exact rank identity, derived bound validity, empty binding scope, actual typed binder resolution, the literal missing-binder diagnostic, exact left and right read states, and both directions of local contextual-law transport.

## Preservation

Only this new proof module and owned evidence files were written. Every frozen proof source, Haskell file, Audit file, repository documentation file, and sibling file was left unchanged by this task. No Git mutation was made. The source snapshot and updated owned SHA256 manifest are in this directory. No owned process remains.
