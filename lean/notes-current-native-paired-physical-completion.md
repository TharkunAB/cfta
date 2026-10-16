# Paired physical completion and remaining contextual induction

Source main stays `8f85ddb6`. The seven-module checkpoint is published at
`554a116f`. The native and Haskell source bodies are unchanged by this update.
The full-library goal remains active.

## Constructed actual checked returns

SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace stores each actual
yielded instruction, complete checked state, and current physical Inputs.
Trace.bind and Trace.trans preserve exact execution. Trace.plan derives the
reached physical plan through the final pure return. Receipt adds returned Good,
machine Extension, heap Keeps, operation-cache Grows, and the structural result
postcondition. Receipt.done derives actual finite interpreter completion.

The private node and edge dispatch proofs use strictly smaller body hypotheses.
They retain the selected evaluating handle through the actual checked child
trace. The finish instruction checks only that handle and current result
residency. The same trace restores enclosing ActiveAbove after the finish.
Structural Code induction handles work, entry, reads, optional binders, and
both request families. A strong induction on independent requiredFuel then
discharges both private body hypotheses internally.

Public node_complete, edge_complete, and request_complete derive actual
physical returns. They do not assume body completion, final validity, or a
future InputsThrough plan. The independent pure schedule Completes and
scope certificates remain explicit in these general endpoints.

initial_complete derives the independent schedule completion and source scope
from closed Original available roots. From initial Good and Idle, it returns
an actual checked receipt and final Idle. WordRanges remains explicit. It
requires valid packed keys at every actual yielded prefix, not a successful
future result. Generic code_complete also takes structural Safe, Operands,
and Below; the source endpoints derive those certificates.

This is a completion theorem for the checked interpreter model under those
contracts. It is not a theorem of unrestricted Haskell evaluation. Runtime
capacity, complete initial allocation/annotation history, unsafe IO, forcing,
GHC publication, and concurrency correspondence remain explicit boundaries.

## Actual reference and Mu branch meaning

SourceCurrentAllocatedNativeReferenceMeaning derives the original bound Mu
from typed available source bindings and coherent identity readback. Reference
validity derives the bound input's validity in the same fixed model. Literal
readback precedes the exact child request, with no operation-cache effect.
Left and right branch laws retain source operand order and the child's state.

SourceCurrentAllocatedNativeMuBodyMeaning combines the actual entered child
Trace with its local contextual NodeLaw and physical effects. The trace derives
physical heap checks. Initial SemanticReady then derives the child's guarded
and budget probe-language heaps. Available child output derives successful
optionalBinder construction, and the rank-sum Mu law derives the parent law.
All three selected Mu branches return actual compileNode completion at child
fuel plus three, with Keeps, Available, and SemanticReady at the literal state.
No final semantic heap or same-parent law is supplied.

## Remaining semantic and library obligations

The physical completion proof does not derive NodeLaw or EdgeLaw. Combine its
actual recursive returns with the local branch laws in a joint contextual
semantic induction. Preserve Contextual across the actual child calls and
install each locally derived law at its actual evaluating finish handle.
Derive warm-cache admission and root exactness without assuming its root
FinishThrough law. Keep original input models independent of desired output.

Then compose complete original allocation histories, the current class Scan,
and the constrained outer caller. Every other public API and distinct Sized
contract remains in scope. Runtime, frontend, graph import, synthesis, and
canonical-order adapters retain their recorded boundaries.

## Validation

The full pinned audit passes 2275 jobs and 55741 theorem dependency checks.
Only standard Lean foundations and the old unused-input warning occur.
The three new focused modules and public probes have separate saved logs.
Haskell validation is reused from the unchanged source: strict Nix build,
777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild.
No local test file or Haskell implementation changes in this update.

Evidence and frozen copies remain repository-local. The baseline preservation
checks and earlier missing external-draft-byte limit remain unchanged.
