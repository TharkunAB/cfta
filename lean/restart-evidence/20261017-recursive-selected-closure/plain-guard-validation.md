# Local plain guard closure

Checked at 2026-10-17T01:25:59.367829+02:00. The production source has 182 lines and SHA256
`1a99fe3e08787e586964f6127b06cba20d7b756210c5d781a543247ccbb7a99a`.

`plain_fields` derives empty stored classes and an empty outer guard atom list
from the literal `SourceMemoGate.plain` test and active physical classes. The
proof uses the existing equality normalizer laws at a nullary Unit term. A
nontrivial class cannot hold at that term. The proof then derives an empty
positive extraction and an empty atom list. It assumes no solver or guard
meaning callback. Canonical conjunction of both such guards is literal Top.

`ready_active` derives active readback from the actual allocated field's Ready
invariant. `conjoin_result_plain` applies the existing allocated conjunction
correctness theorem to the exact successful candidate. `ready_plain` applies
current intersection-prefix correctness to the exact ready branch. The loaded
wrapper derives readiness and exact original readback from both current field
loads. These laws use only the two queried guards. They require no condition on
unrelated heap records and no unconditional law for arbitrary guard conjunction.
`top_plain` covers the literal sentinel guard.

Validation:

- Direct source check with all linters: `plain-guard-direct-2.log`, exit 0,
  no diagnostics. The first failed source and its log remain unchanged.
- Canonical foundation batch: `plain-guard-canonical.log`, exit 0, 1098 jobs.
  The only warning is the historical unused variable in the dependency
  `InternedFreshOrdinaryClosedCompletion.lean`.
- Imported public checks: seven axiom and full-signature pairs in
  `plain-guard-public-1.log`, exit 0. Explicit proofs, universes, and deep terms
  are enabled. The output budget is 10000000 steps.
- Imported integration checks: three pairs in `plain-guard-kernels-3.log`,
  exit 0. Both final probe logs have no warning, error, sorryAx, or truncation.
- The first kernel starts from current original field loads and initial plain
  guards. It constructs its own ready intersection result. It derives the
  result's Ready, plain, valid operation state, and actual operation growth.
- The second constructs both original fields from initial valid operations.
  It constructs two serial conjunctions at their actual returned operation
  states. It derives both returned plain tests and final validity. No supplied
  result, intermediate readiness, or future law appears in its initial facts.
- The third uses an actual mismatched checked body. It derives the literal
  sentinel branch and its empty-field allocation, validity, growth, and Top
  plain test without any field-load premise.

The first kernel attempt failed because an isolated import overlay lacked a
transitive dependency. The next attempt found a namespace error and one unused
simp argument in the kernel source. Their logs and matching sources are retained.
These failures did not change production source.

This component proves local guard closure. It does not prove recursive query
annotation preservation, selected endpoint preservation, termination, WordRanges,
runtime correspondence, or whole-library completion. The current native caller
must still prove its local operand and dereference annotation invariants.
