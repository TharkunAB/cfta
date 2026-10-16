# Read-only review of causal admission execution and certificates

Date: 2026-10-16 07:35 CEST.

Reviewed the final root AdmissionExecution and AdmissionCode modules.
No source was edited and no proof was duplicated. Root reported canonical
GREEN1087. No material proof or scope defect was found.

AdmissionExecution checks only actual reached publication instructions.
RequestCovered is NodeCovered for node instructions, EdgeCovered for edge
instructions, and True elsewhere. The checked edge-body prefix leaves the
native state unchanged. Work, enter, and optional binders retain cells while
changing their machine. Actual lookup and demand thread their full native
results. Finish preserves original request admission independently of its
candidate result. No operation manufactures a completed result law.

RequestsThrough follows the actual checked step. Its zero-fuel case is True;
this is correct because no instruction executes. It needs no suffix check
after a terminal outcome. execute_covered follows all five actual outcomes.
done_admitted rewrites that derived invariant at the actual returned whole
state. It assumes no final coverage, cell receipt, or desired result law.
Its reached RequestCovered plan remains an explicit internal obligation.

AdmissionCode.Certified is a local source certificate, not an execution or
completion theorem. Node/edge certificates require original source scope and
request coverage before publication. Their continuations quantify only
physical returned-value facts, not child NodeLaw/EdgeLaw or parent semantics.
Work and optional binder certificates use the literal primitive return plus
physical validity, Extension, and SemanticReady. Those facts must be derived
by any later interpreter. Read uses the exact physical read. Enter uses the
actual returned domain entry. Finish requires only the next admission
certificate. This is sufficient for the admission property and does not
silently prove physical or semantic correctness of arbitrary finishes.

certified_bind composes actual machines and Extension in source order.
walk_certified threads the remaining known inputs and prior outputs through
those actual extensions. Its calls premise is a local static certificate,
not a successful future call or desired final walk.

## Recommended finite-trace bridge

Use an actual physical Trace and actual source branch certificate. Split
binds with SemanticTraceReadback.bind_inverse. Derive each intermediate
Good, Extension, and SemanticReady from reached physical checks. For node
and edge requests, use actual lookup/demand and physical exact-key readback
to identify the selected original request. Apply source certificates to that
exact compileNode or checked edge body. Split the actual shorter child trace,
derive returned residency with RequestResults, and resume the original local
continuation. This can derive a RequestsThrough plan for the same completed
trace without assuming callback completion, final coverage, or child language.

The admission trace simulation and all actual branch certificates still need
to be composed. A source-wide body certificate assumption must not be called
a proved complete query until its concrete branches are discharged. This
review does not assert those pending components or runtime correspondence.

Reviewed hashes:

```
ffb8b0ccae2b40438d3fc154f2d0b8f4f489cca2374b26dd5c623d9e87c89e75  lean/MicroCFTA/SourceCurrentAllocatedNativeAdmissionExecution.lean
97c0df6c92663c5aee01a8ca3b384640cdef31ce3146c7ae182d5fc0cc7c0e19  lean/MicroCFTA/SourceCurrentAllocatedNativeAdmissionCode.lean
```
