# Actual checked source-code physical progress prerequisite

Frozen 2026-10-16 04:51 CEST at observed HEAD `4ada401dbc449775b8e6b37e2a091e0e3318f3c8`.

New module: `MicroCFTA.SourceCurrentAllocatedNativeCodeProgress`.
Source: `lean/MicroCFTA/SourceCurrentAllocatedNativeCodeProgress.lean`.
Lines: 468.
SHA256: `35f942dcd7caa97253a5d3d29cf26f5a5042044cde40c853497357c4b31c0d6f`.

## Result and initial premises

This file proves physical input certificates for every compiled source node
branch and for the actual checked edge continuation. It proves an actual
finite checked edge prefix from initial loaded resident fields. It does not
claim general finite checked recursive completion.

`Operands` follows the existing Code. It records actual WorkInputs, domain
entry operands, available optional-binder inputs, and original NodeReady or
EdgeReady request inputs. Its continuations accept every physically valid
resident result after actual machine extension. It does not assume that a
recursive callback terminates. It excludes driver finish instructions.

`compileNode_operands request machine valid ready` derives this certificate
from the original current physical inputs. The proof covers empty, reset,
self, swap, repeated pair, Mu, union, bound-reference read, and ordinary row
branches. It retains actual stored input order and source domain entry.

`children_certified request combined machine valid ready` derives Safe and
Operands for the actual accepted checked code using its allocated combined
constraint. `sentinel_certified` derives the same for the source sentinel.
`body_certified` follows the literal yielded branch of checked body; it does
not compare it with the old eager edge compiler.

`body_prefix source facts holds request scope complete before valid ready
operations heap` derives an actual yielded code and actual returned equality
cache. It returns operation Valid, operation Grows, same-cache resident Fields,
static CodeFields, Safe, Operands, and strict Below at the independent parent
requiredFuel bound. Its heap premise is INITIAL Fields, not a future field
invariant. Mismatch/rejection returns sentinel code with no child request.
Acceptance uses original child zip order only after the allocation decision.

`node_certified` combines physical operands, structural Safe, structural Below,
and static fields for actual compileNode. `initial_certified` derives its
independent schedule Completes witness and requiredFuel bound from initial
Kernel.Valid, Original closed operands, and their availability. Neither
endpoint needs a completed native callback or future result law.

`current_heap_inputs` derives the actual current primitive heap checks.
`current_inputs` derives the existing stronger current native input predicate
from Operands, Below, and the current Words certificate. Original NodeScope
inside Below supplies complete root codecs. Thus conditional node word checks
are sufficient at these original request sites.

## Reusable old facts and excluded old execution facts

The old Safe/Below definitions, compileNode_safe, compileNode_below, and the
source requiredFuel schedule are structural. They inspect exact primitive
results and physical continuations. This file reuses those facts. It does not
reuse old native Evaluation, old eager Produced, BodiesBelow, or code_terminal.
The old native Valid contains eager completed-body provenance. The old finish
and warm native progress proofs use that provenance or old body Evaluation.
They cannot establish the new checked result receipts by substitution.

## Corrected key-domain boundary

An earlier informal example used Empty as an unencodable input. That example
was wrong: `IntersectionFlatMemoKey.input .empty = some .empty`. The final
kernel probes preserve the corrected facts.

An unresolved `.reference (.intersection 0 1)` has requestKey none. It cannot
satisfy unconditional KeySafe. Paired with Empty, the literal checked node call
still completes after two instructions, with both states unchanged. The older
unconditional InputsThrough plan cannot certify this arbitrary placeholder
call. This is a real limitation of that plan outside the original-input domain.

It is NOT an obstruction for the intended NodeBelow/Original domain. Original
excludes unresolved placeholders. Original.codec gives a some key, and the
new current_inputs proof derives unconditional KeySafe from conditional Words.
No whole-completion impossibility follows from the placeholder example.

## Exact next completion hook

A paired requiredFuel induction must derive actual checked node and edge body
completion and their physical result/extension facts at the returned caches.
It can use these derived operands and bounds for each source code branch.
It must preserve the checked field heap and semantic/cost readiness through
those actual recursive effects. It must derive each completion-cell receipt
and retain the original running handle through nested calls. Driver finish
instructions need those derived body receipts; Operands excludes such frames.

The contextual Mu result law and fixed-input contextual memo laws remain
separate semantic steps. The new ContextCache and MuMeaning work can supply
that part once its laws are proved for the actual completed bodies. No public
theorem in this file assumes NodeProduced, EdgeProduced, a future state, or a
completed recursive execution. The current Words/range boundary stays explicit.
No theorem here claims idle preservation, full checked completion, source GHC
publication equivalence, or runtime scheduling correspondence.

## Validation

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeCodeProgress
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-recursive/allocated-native-code-progress-probe.lean
```

Focused build terminal 0, 1078 jobs. The only replayed warning is the existing
unused `inputs` binder in InternedFreshOrdinaryClosedCompletion.lean:24.
The new module has no warnings. All nine public axiom/signature probes and
eight kernel examples pass. Axioms are limited to propext, Classical.choice,
and Quot.sound. The probes test complete Empty keys, placeholder bypass,
placeholder KeySafe impossibility, actual two-step checked completion,
old-plan rejection of that placeholder, Original exclusion, the new original
conditional-word adapter, and sentinel current operand derivation.

The execution environment refreshed while the old build handle 34230 was
running. That handle no longer existed, and old /tmp files were unavailable.
The repository source, toolchain, and oleans remained available. The focused
build and probes above were rerun. This directory retains the reachable new
source snapshot, final logs, standalone probe source, and this premise audit.
No old proof file, Audit, Haskell source, documentation file, or Git state was
edited by this task.
