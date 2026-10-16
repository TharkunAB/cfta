# Combined recursive prefix code

Checked on 2026-10-17 at 01:07 CEST.

`SourceCurrentAllocatedRecursivePrefixCode.lean` has 210 lines. Its final SHA256
is `9c867dcaef58dc0ee95db4af1b5c2e3e21c37e68ea5a7e5243b621722372c08d`.

`Certified` combines the existing `Safe`, current `CodeProgress.Operands`, and
`RecursiveDomainCode.Certified` predicates. All three use the same literal code,
current machine, and physical post. Only original operand scope uses the fixed
source heap. Newly entered domains need no representation in an initial machine.

`node_certified` and actual `body_certified` combine the existing compiler proofs.
No node or edge dispatcher is copied. The latter certifies the exact code and
machine of the supplied checked body yield. It has no semantic completion or
symbol-equality premise.

`work_next` and `optionalBinder_next` derive validity and extension from physical
safety. They derive semantic readiness from the actual primitive and current
operands. Only then do they extract the domain continuation certificate.
`enter_next` uses the literal domain constructor return. `read_next` uses the
literal current-heap read. Node and edge continuation helpers take physical
returned facts, which the later raw-prefix induction must prove for the actual
smaller body trace.

The component does not infer semantic readiness from arbitrary heap extension.
`Safe` and `Operands` exclude driver finish instructions. Protected finish
handling remains a separate part of the raw-prefix proof. `current_inputs` takes
only the current instruction's word fact; the component does not assume or prove
`WordRanges`, future enter admission, or a physical trace.

Validation:

- `recursive-prefix-code2-direct-2.log`: pinned direct Lean with all linters,
  exit 0, no diagnostics.
- `recursive-prefix-code2-canonical.log`: owned copy of root's completed focused
  canonical build. Exit 0, 1119 jobs. Only the historical unused `inputs` warning
  appears in the dependency `InternedFreshOrdinaryClosedCompletion.lean`.
- `recursive-prefix-code2-public-1.log`: 17 imported public declaration pairs,
  with explicit full signatures and printed axioms. Exit 0, no diagnostics.
- `recursive-prefix-code2-kernels-3.log`: three imported integration pairs,
  exit 0, no diagnostics. The kernels construct the combined certificate from
  legitimate initial facts before using any continuation helper.

The first kernel follows actual Mu dispatch and entry to a ready body request in
its newly returned domain. The second constructs an actual edge Work return and
derives residency, validity, semantic readiness, extension, and exact domain-cache
identity. The third uses only a literal primitive optional-binder return to derive
its own physical post. It supplies no enclosing query completion or future result.
Failed draft and earlier warning logs remain with matching source snapshots.
