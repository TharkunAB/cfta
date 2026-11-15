# Physical prefix inputs for the global from-empty query invariant

Status: SOURCE AUDIT plus ONE UNCOMPILED bounded helper. No global cache-law
proof or new semantic history structure is claimed.

The current Root target uses the existing Returned predicate for both families.
The node clause is the strengthened closed exact-self clause:

```
request.right=request.left -> request.left.free=[] -> value=request.left
```

The edge clause is:

```
request.left.children.length != request.right.children.length ->
row.children=[empty]
```

These are fixed laws. The original full source/finite-witness objective is
unchanged. This target is a cache-history component and does not supply a model.

## Exact existing API boundaries

PhysicalExecution.execute_invariants (lines249-274) requires BOTH weak Physical
and SourceEqualityRequiredCache.Ready. Ready contains SemanticHeap, Covered [],
and an open-depth Heap property (RequiredCache lines19-22). It must not become
a new premise of the weak global query target. Its Physical conclusion alone
does not remove those input requirements.

PhysicalExecution.step_valid (lines115-143) takes only weak Physical and the
CURRENT actual Inputs. It handles every observation tag. step_extension
(lines146-193) supplies the current machine extension from the same checks.
Budget induction on these two existing laws derives weak Physical and extension
for every execute endpoint without RequiredCache.Ready. The yielded case uses
the actual InputsThrough tail; done, failed, constraintError and blocked use
that last actual step's state. No future state invariant is needed.

InputsThrough (lines216-221) is the original budget plan. Its ZERO case still
contains current Inputs. At a yielded step, its positive case supplies the
same plan at one smaller budget and the actual yielded state. At other tags,
there is no resumed tail.

SemanticTraceReadback.inputs_before_bind (lines26-32) removes a captured
continuation at the CURRENT check only. It does not expose an InputsThrough
budget law. Its bind_inverse requires a completed physical Trace; it cannot
be used to invent a complete future child for a blocked/unfinished budget.

TracePrefixBind.bind_prefix_cases does cover incomplete physical prefixes.
It distinguishes unfinished inner control from an actual inner return and
later continuation. It preserves exact step count and complete states. It
still does not derive a plan past the observed prefix endpoint.

PhysicalTraceCompletion.Trace.plan supplies a completed trace's plan at count+1.
That API must not replace the ORIGINAL supplied-budget plan for incomplete runs.
In particular, count+1 can destroy the strict parent-fuel comparison.

## New bounded missing producer

`prefix_inputs_before_bind` takes ONLY:

- original weak Physical before;
- InputsThrough at the ORIGINAL supplied budget and initial control;
- actual Steps used from that same initial/before to control.bind next/after;
- the past arithmetic fact used<=budget.

It derives the physical checked prefix, weak Physical after, actual machine
Extension before->after, and BOTH bound and unbound InputsThrough plans at
EXACTLY budget-used. No completed future Trace, query readiness, operation
validity, heap-readiness, result law or model is an input.

The two small private proofs select the original plan's real yielded checks
and project the remaining bound plan before bind at the same budget. The
projection handles pure, yielded, failed, constraintError and blocked inner
steps. It does not execute a captured continuation speculatively.

Existing checked_trace_extension then supplies the reached physical state.
At a child `.node` or `.edge`, current Inputs from its remaining plan supply
ready operands and actual key safety. At an optional/work/finish instruction,
they supply the corresponding current operands/running-cell checks.

## Original-budget arithmetic

Let original query fuel be F=r+1. Its actual lookup/demand dispatch consumes
one yielded instruction before any evaluated compiler body. The body budget
is r, so r<F. This is the strict induction descent, including the zero-prefix
first child of compileRows or a compiled union walk.

For a body child reached after k yielded instructions with k<=r, the original
remaining budget is r-k. It satisfies r-k<=r<F. It need not be strictly less
than r: k can be ZERO. Do not require a fake positive-prefix count from the
first child, and do not spend an extra pure-return observation instruction.
The new helper projects InputsThrough at this EXACT r-k.

If an inner child returns at t yielded steps with t<=r-k, bind continuation
starts at that SAME reached state after t instructions. Code.pure.bind next
is next. The remaining continuation budget is r-k-t. When t=r-k, the frontier
is a zero-budget yielded continuation. Its current Inputs still come from the
original plan. This includes the state immediately after a finish writes a
returned cell but before its final pure return is observed.

For the strengthened induction, use BOTH original-budget endpoint preservation
and pure-trace result law for trace counts <=that budget. Turning a trace at
count=r into execute(count+1) just to invoke an IH would consume F, losing
strict descent. This is why a query-done theorem alone is insufficient for the
global post-finish/pre-pure endpoint. An auxiliary deterministic body comparison
may use done_stable as a local equality proof; it must not enlarge the IH budget.

At every terminal non-yielded observation, execute F returns that exact step
state. Generic resume/bind splitting must retain it, including the blocked
control and any actual native/operation effects. It cannot assume more budget
will complete that path.

## Empty base and semantic scope

The actual initialization is SourceRecursiveIntersectionThunks.initial with
BOTH memo families FlatMemoThunk.empty. That state empties table AND cells and
sets next=0. ContextCache.returned_empty applies for any fixed law. Empty key
tables alone do not suffice: FlatMemoThunk.Valid links table->cell only and can
permit orphan returned cells. Root confirmed the intended actual initialization.

ContextCache.returned_lookup/returned_demand preserve existing clauses.
returned_finish requires the local law for its CAPTURED original request and
actual payload. That law must come from the genuine compiler producer and its
past body return. The new resource helper supplies no semantic clause. A generic
arbitrary hand-written finishEdge could store a resident non-sentinel row for
a mismatched request while satisfying current physical checks. The global law
must stay on actual query compiler/driver paths and their captured frames.

The same reasoning covers the strengthened node self clause: a reset child
can use the whole r body budget, and its exact pure result is needed without
spending a further observation step. Root owns node/row/union case assembly.
The original from-empty/all-outcome theorem, real caller resource derivation,
and full same-root finite joint accepted completion remain open here.

## Validation and ownership

One public resource helper, no new law datatype/framework. Original full/coupled
header is copied unchanged. No live source, compiler, Git, board, Haskell, or
/tmp operation was used. Root must strict-check the frozen source with its
import-free probes. This helper receives no credit before that check.
Stop after this bounded packet as requested.
