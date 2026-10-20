# Minimum unbound native owner contracts

Status: source-based proof design. The owner theorem remains unproved.
This review adds zero Lean jobs and zero proof pairs. It independently
reviews one existing checked helper. No production source is changed.

## Core receipt

Make the owner receipt polymorphic in the outer result type A. Keep these
fields in one existential, all tied to the given optional prefix:

- An actual query prefix to `.node queried callerNext` at queryBefore.
- Literal lookup and demand equations selecting handle, chosen, running,
  and captured. The selected suspended and evaluating cells contain that
  SAME captured request. Keep compilerBefore = (running, operations).
- The captured decision is bothMu, leftMu, or rightMu. Its two identity
  equations give first/second and the exact ordered pair function.
- The actual enter step, its physical Inputs, its exact entered domain,
  and childBefore formed by the actual native advance.
- An UNBOUND child Trace from requestNode of the captured original bodies
  to pure siteBody at the SAME siteBefore as the given optional site.
- `siteNext = fun result => finishNode handle result (callerNext result)`.
- `siteFuel = queryFuel + 2 + childFuel`: query expansion and enter each
  cost one step. A pure boundary costs zero steps.

Do not add a caller-supplied owner, successful owner return, writer History,
source ancestry, or desired relation between outputs. Exact lookup and
actual demand derive the captured cells. The crossed enter's physical
Inputs derive Domain and captured operand availability. This is a receipt
for an executed instruction, not a future completion assertion.

A Trace ending at an optional instruction does NOT contain the physical
Inputs of that final instruction. Trace.cons checks instructions that it
crosses; Trace.refl has no such check. Keep final optional Inputs and body
availability supplied by the existing selected-cell locator separate.
They are not needed to recover the syntactic owner from its prefix alone.
Likewise, demand gives the evaluating cell at compilerBefore. Retention of
that cell at siteBefore is a separate running-cell theorem with Shape or
an appropriate stronger invariant; do not include it without proof.

## Compiler classifier: own Mu or an actual unfinished recursive call

For an unbound compileNode prefix to optional(pair, body, siteNext), return
one of three source-derived cases. This can remain private.

1. Own Mu. Retain the actual decision and identities. The crossed enter
   gives the exact childBefore. A completed unbound body request returns
   body at the SAME siteBefore. Here siteNext = pure, and compilerFuel is
   one plus childFuel. Crossing this optional instruction cannot reach a
   later optional in this unbound compiler: it yields pure or blocks.
2. Nested node request. Retain preFuel, callFuel, requested, continuation K,
   entry, and innerNext. Derive actual Trace preFuel from the compiler to
   `(requestNode requested).bind K` at entry, and actual UNBOUND Trace
   callFuel from that request to optional(pair, body, innerNext) at the
   same siteBefore. Retain `preFuel + callFuel = compilerFuel` and
   `siteNext = fun value => (innerNext value).bind K`.
3. Nested edge request. Use the same data and equations, with an actual
   requestEdge and its edge-valued continuation. Keep node/edge result
   types distinct; do not identify their controls by a phantom equality.

The nested callFuel need only satisfy callFuel <= compilerFuel. The enclosing
request has ALREADY consumed its expansion step, so callFuel is strictly
less than the enclosing request-prefix fuel. Strong induction therefore
applies to the actual unbound request, including reset/swap branches where
the compiler adds no intermediate instruction. A theorem requiring strict
callFuel < compilerFuel would be unnecessarily strong and can fail there.

For union and ordinary rows, the existing indexed walk prefix splitter
retains the original selected member/pair index and actual earlier calls.
Use its unfinished arm and the optional-prefix helper. Its completed arm
leaves makeUnion or makeNode followed by pure, which cannot reach optional.
The reference branch retains its actual read and successful bound payload.
Missing payload/name branches fail and cannot be crossed by a yielded Trace.
Empty, self, repeated, and unsupported branches cannot expose an optional.
No semantic output relation is needed in these constructor cases.

## Checked edge body classifier

For a Trace from `.edgeBody captured pure` to the selected optional, derive
an accepted checked-body step followed by an actual unfinished node request
in the ORIGINAL zip of captured left/right children. Retain its exact
index, actual earlier Walk, ordered results, full remaining continuation,
and the same siteBefore. The body step contributes one instruction.

Keep both actual load results, the actual allocation result ready combined,
and the exact operations state at child entry. The accepted continuation
uses `readback combined`, not an assumed eager conjoin value. Replacing it
by compileEdge requires the separate children_eq_compileEdge premises.
The physical body itself permits missing fields and errors; the existence
of the given yielded Trace excludes those outcomes locally. No global
Fields, semantic branch equation, or parent success premise is needed.

Mismatch and rejection lead to sentinel work followed by pure. A completed
accepted Walk leads to makeEdge work followed by pure. These suffixes cannot
reach an optional instruction. Blocked and error outcomes cannot be crossed
by a yielded prefix. Thus there is no own-Mu case in checked edgeBody.

## Lifting and exact prefix composition

Use Trace.bind to lift a recovered query prefix through K. If the original
query continuation is callerNext, it becomes

    fun value => (callerNext value).bind K

The SAME owner finish continuation becomes

    fun result => finishNode handle result ((callerNext result).bind K)

This follows by Code.bind on finishNode and Code.bind_assoc. Use function
extensionality only to prove this displayed equation. Do not infer bind
injectivity or identify arbitrary continuations from selected returned
values. Preserve the entire Code function in the receipt.

Compose the actual compiler prefix and selected callback prefix using
Trace.bind and Trace.trans at their EXACT middle Checked state, including
operation caches. Lift the indexed Walk's earlier calls in their original
order. Fuel addition follows Trace.trans; append no artificial pure step.
The unbound child-return Trace in an owner receipt is unchanged by an outer
lift. Its result, siteBefore, entered domain, and captured request stay the
same. Do not choose a new query or owner after lifting.

## Query versus capture and direct calls

Core recovery can retain queried and captured separately without initial
cache validity. PhysicalCache.node_started identifies them only with Valid
at queryBefore, NodeReady and KeySafe, and the actual lookup/demand equations.
The physical query Inputs provide the latter checks. Initial Valid must
first be transported to that exact queryBefore if this corollary is needed.
Matching a truncated key, pair, body or result is not enough.

A direct own-Mu case is impossible. Direct lookup has requestKey = none and
captured = queried. A successful Mu compiler has both actual identities;
case analysis on values gives both source input codecs. sourceKey_complete
then gives a Some key. No machine bound, cache-validity, or original-source
premise is needed for that contradiction.

The old proposed plan was overly broad when it said direct non-Mu calls
can contain a deeper Mu owner. The checked private unkeyed_control in
NativeRowKeyable restricts a key-none request to empty, swap, or unsupported;
unkeyed_swap preserves key absence. A focused finite prefix induction can
therefore exclude ANY optional site from an unbound key-none request.
That prefix exclusion is not yet a public theorem. Do not call the private
constants by generated names. It is safe to retain the generic direct arm
in the current query classifier and eliminate own-Mu locally. This is a
proof-design simplification, not a runtime or Lean defect.

## Source anchors

- SourceRecursiveIntersectionCompile.lean:28: exact enter/body/optional Mu code.
- SourceRecursiveIntersectionCompile.lean:59: all actual node branch shapes.
- SourceEqualityNativeDemand.lean:65: actual checked edge-body decisions.
- SourceEqualityNativeCheckedCode.lean:24: ordered accepted child continuation.
- SourceEqualityNativeDemandContinuation.lean:16,30: bind and associativity.
- SourceCurrentAllocatedNativePhysicalTraceCompletion.lean:31,68: physical
  checks and exact Trace.bind; Trace.trans composes at the same Checked state.
- SourceCurrentAllocatedNativePhysicalExecution.lean:47: instruction Inputs.
- SourceCurrentNativeWalkPrefix.lean:22: indexed actual unfinished call.
- SourceCurrentAllocatedNativePhysicalCache.lean:280: captured/query equality.
- SourceRecursiveIntersectionNativeShape.lean:108: same captured cell statuses.
- IntersectionFlatMemoKeyDomain.lean:159: complete identities give Some key.
- SourceCurrentNativeRowKeyable.lean:42,66: key-none branch/swap restrictions.

No source-size, semantic output, whole-owner completion, original binding
ancestry, or global native termination result is established by this design.
