# Checked edge body contextual meaning

Date: 2026-10-16 05:16 CEST.
Read-only validation HEAD: `7dccd588ddd60bf4daabd6e2b11bcd09050f3579`.
Source: `lean/MicroCFTA/SourceCurrentAllocatedNativeEdgeMeaning.lean`.
SHA256: `4282fec1140955ad038cbf01d0b44dfed7e22bdcc4b93e553fd74cd160cf0c48`.
Length: 332 lines.

## Derived result

The module uses the fixed independent `InputMeaning`, `RankedInput`, and contextual `NodeLaw` and `EdgeLaw` interfaces.

- `joined_symbols` derives matching symbols from membership in the actual parent `SourceRecursiveIntersectionKernel.pairs` join. `zip_inputs` derives the original child input scope from the parent edge scope.
- `edge_law` derives both contextual directions from ordered local child node laws, the actual result fields, equal original row lengths, matching symbols, and guard conjunction.
- The indexed `Walk` records only the actual reached zipped child `Steps`, that child's heap retention and available output, and that child's contextual node law. `Walk.actual` erases these certificates to the existing actual child execution. `Walk.effects` derives final available results and heap retention. `children_trace` then performs exactly one final edge construction.
- `accepted_body` combines the actual checked field loads and ready allocation branch, the actual ordered child walk, and the actual constructor. The checked allocation readback theorem derives the source conjunction. The PCS guard theorem derives its Boolean conjunction law. The result includes the exact `execute (fuel + 3)` state, contextual `EdgeLaw`, heap retention, and edge residency.
- `mismatch_body` derives the exact three-step sentinel execution and contextual law without a field-load or child-call premise. The returned operations are exactly `emptyField before.operations`.
- `rejected_body` derives source rejection from the actual current-cache loads and checked allocation. It proves that no common bounded original row term exists. It then derives the exact three-step sentinel execution and contextual law without child calls. The returned operations retain the actual checked allocation result and subsequent empty-field allocation.

## Scope

The accepted branch still takes local recursive child node laws and physical effects for the exact reached child requests. These are recursive induction hypotheses, not a same-parent edge law or a supplied future final invariant. The module does not derive the global recursive checked node theorem, contextual Mu body law, cache finish validity, general finite query completion, or whole-source correctness.

Accepted standalone requests need matching symbols. The checked edge body does not compare symbols itself. The actual parent row join supplies this premise, as proved by `joined_symbols`. One kernel check refutes an unrestricted standalone edge law for different symbols and empty child lists. This is a scope check, not a source defect.

The result uses the actual checked execution. It does not substitute the old eager edge execution, assume an output equality with that execution, or demand rejected children. The theorem returns heap retention and edge residency. It does not assert new cost, annotation, semantic-heap, operation-validity, or final contextual-cache invariants beyond its stated conclusions. Other components must derive those properties.

## Validation

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeEdgeMeaning
```

PASS exit 0, 1075 jobs. The only warning is the existing unused `inputs` binding in `InternedFreshOrdinaryClosedCompletion`. This new module has no warning. Log: `edge-meaning-build-20261016.log`.

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-recursive/edge-meaning-public-probes-20261016.lean
```

PASS exit 0, no warning. All 13 public theorem axiom reports, 13 public signatures, and 10 kernel checks pass. The maximum axiom set is `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom or `sorryAx` occurs. The source has no `sorry`, `admit`, or `axiom` declaration.

The kernel checks cover matching symbols from the actual join, unequal arities, literal checked contradiction, direct contradictory-field load, exact three-step mismatch state, rejected leaf meaning, empty actual child effects, an accepted leaf without recursive child assumptions, the different-symbol boundary, and a singleton actual child walk with exactly one local node law.

## Preservation

Only this new proof module and owned evidence files were written. All older proof sources, Haskell files, Audit, repository documentation, Git state, and sibling files were left unchanged. The source snapshot and updated owned SHA256 manifest are in this directory. No owned process remains.
