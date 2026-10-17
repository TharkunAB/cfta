# Actual cap publication bridge

Status: PASS for the bounded component. The general mixed native producer remains open.

The production source is `lean/MicroCFTA/SourceCurrentConstrainedCapNativeTraceGlue.lean`.
Its final SHA-256 is `dea58636e2751d34a3b7a073be8d923ee89f794ce144d771a507a5fad347813c`.
It has 188 lines and 11 public declarations. No older production file changes are part of this component.

## Exact scope

`Stored` at line 29 combines the actual constructor `MuStored` with conditional native cell laws for every possible source heap. `initial_stored` derives these laws from the empty actual tables. The native laws remain conditional on each complete request's bindings and both operand caps at every common depth.

`work_stored`, `enter_stored`, and `body_stored` at lines 42, 50, and 59 retain these stores at the literal returned states. Work uses the existing primitive `WorkSafe` theorem. Enter changes only the domain cache. The checked edge-body prefix changes operations and retains its full native state. These helpers do not infer a missing mixed optional-binder result.

`Receipt` at line 76 retains the existing physical prefix receipt unchanged. That receipt includes its exact trace, full returned state, current physical facts, heap and operation growth, input checks, field checks, and physical postcondition. The new fields add only the causal stores and an internal local postcondition. This is a smaller-body induction interface. It is not a theorem that arbitrary completed traces have the local cap postcondition.

`join` at line 91 reuses the existing physical receipt composition. `finish_node` and `finish_edge` at lines 100 and 132 use the exact completed body trace and the existing protected-owner theorem. They derive the evaluating cell at the body return, execute one literal finish step, install that body's universal law at that exact owner, and retain the exact returned-cell equation. The resulting count is the actual body count plus one. No successful future query or whole future trace occurs in the premises.

`next_node` and `next_edge` at lines 164 and 176 instantiate the frozen cap-code continuation with the actual returned machine, physical extension, residency, constructor store, and local request law. These are continuation consumers. They do not supply the missing compiler producer.

## Validation

The strict absolute-path production check is `native-cap-glue-direct-3.log`. It exited zero and has zero bytes. All linters were enabled. Earlier syntax and inference failures remain in direct attempts 1 and 2 with exact source snapshots.

The canonical build is `native-trace-glue-build.log`. It completed 1157 jobs with exit zero. Its only warning comes from the older `InternedFreshOrdinaryClosedCompletion.lean` dependency. The new production target has no warning.

The imported public probe has 11 axiom/full-signature pairs in `native-cap-glue-public-1.log`. Explicit names, proofs, universes, deep terms, and ten million printing steps were enabled. No error, warning, or `sorryAx` occurs.

The final imported kernel file has three axiom/full-signature pairs in `native-cap-glue-kernels-3.log`:

- `self_publication` constructs the self body from its actual source branch. It derives the universal body law and actual physical zero-step receipt. It then constructs the exact one-step publication and returned-owner cell.
- `constructor_then_publication` constructs an actual `makeNode []` Work prefix. It retains the same evaluating cell through that heap change and composes the actual self-body publication. The exact trace has two steps and the exact computed intermediate and final checked states.
- `published_cap_continuation` feeds the same produced publication into the frozen cap-code request certificate. It derives availability, the chosen finite cap, and the strong stores at that same final machine.

These kernels start from legitimate `Current`, causal stores, and an actual evaluating owner. They construct their bodies and finish traces. They do not claim an initial cold query constructor. The earlier kernel attempt 2 has an unused-instance warning. Attempt 3 removes that warning through natural instance scope. All attempts remain preserved.

## Remaining producer obligation

The next joint actual interpreter must derive each smaller body's universal conditional law together with its causal store, then pass that result to these finish helpers. A result cap at one chosen depth or one chosen source is insufficient for the universal returned-cell law.

The frozen `NativeCode.Certified` is a local continuation certificate. Its effect and recursive-return clauses receive constructor representation. It does not derive primitive `WorkSafe`, request operands' caps, or a mixed optional-binder output from physical validity alone. The current hereditary optional-binder producer requires an annotated body. A positive cap alone does not provide that annotation.

The actual mixed binder branch still needs the local occurrence argument at the normalized candidate and the corresponding causal warm Mu law. In particular, a candidate's cleanup property cannot certify an earlier keep-first winner. The weighted occurrence component does not by itself prove transport through old-pair substitution or arbitrary warm Mu records. The guard-only `MuStored` law does not imply these additional occurrence facts for nonplain probes.

This component adds no general mixed native closure, query completion, selected recursive progress, or whole-library completion claim. It changes no Haskell source or runtime behavior.
