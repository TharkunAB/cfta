# Static contextual reference certificates

Date: 2026-10-16 05:57 CEST.
Read-only validation HEAD: `4d74d00c5bf99e3f06447d5b68ecbed72ff2d8e9`.
Source: `lean/MicroCFTA/SourceCurrentAllocatedNativeContextualReferenceCertificates.lean`.
SHA256: `ed497b69c8839d6c6d2de6a8eb02ac39616c14d97d617a08fea2e1cc733b87e3`.
Length: 105 lines.

## Derived result

`resolve` derives the literal current Mu read, original scope, source availability, and exact binder identity from `OriginalBindings`, current coherent facts, and actual source growth and history. The caller does not provide a desired binder or successful read result.

`left_code` and `right_code` derive the static `Certified` predicate for actual `compileReference`. The exact resolved child request consumes its own local `NodeLaw` through `Certified.node`. The existing reference meaning lemmas derive the parent law because original reference and Mu inputs share the same language and rank identity. They also derive child model validity from the parent reference validity. The right certificate retains operand order.

`left_reference` and `right_reference` derive the certificates for actual selected `compileNode` branches. All models remain fixed at the original `view source holds`. These certificates have no trace, completed child, returned value, supplied Mu payload, or parent language-law premise.

## Scope

This is a local static continuation certificate. Its interpretation must derive the exact child law from a smaller-request induction and actual execution. It is not that interpretation or general recursive completion. Initial original binding scope, current physical validity, source heap growth, and source issued-history retention remain explicit.

When the source name is absent, the actual code is the literal missing-binder failure. `Certified.fail` is true and supplies no successful result. One kernel check uses an impossible result condition to make this boundary explicit. No successful execution or source lookup is inferred from that certificate.

No extra bound model-validity or whole-input inventory premise is introduced. No old eager interpreter or checked/old-output equality is used. No source word bounds, contextual cache preservation, finish validity, or whole-query theorem is claimed here.

## Validation

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeContextualReferenceCertificates
```

PASS exit 0, 1107 jobs. The only warning is the existing unused `inputs` binding in `InternedFreshOrdinaryClosedCompletion`. This new module has no warning. Log: `contextual-reference-certificates-build-20261016.log`.

```text
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-recursive/contextual-reference-certificates-public-probes-20261016.lean
```

PASS exit 0, no warning. All 5 public theorem axiom reports, 5 public signatures, and 6 kernel checks pass. The maximum axiom set is `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom or `sorryAx` occurs. The source has no `sorry`, `admit`, or `axiom` declaration.

Kernel checks cover empty original binding scope, literal missing-binder compilation, failure certification without a possible result, both reference certificates without child completion at the original heap, and exact original Mu readback after growth.

## Preservation

Only this new module and owned evidence files were written. No frozen proof, sibling source, Haskell, Audit, repository documentation, or Git state was mutated by this task. The source snapshot and updated owned SHA256 manifest are in this directory. No owned process remains.
