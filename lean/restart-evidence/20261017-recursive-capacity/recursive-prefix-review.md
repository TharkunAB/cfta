# Current recursive word-prefix boundary

Reviewed on 2026-10-17 at 00:51 CEST. This note covers the checked
`SourceEqualityNativeDemand.Steps` relation. It does not transfer execution from
the older `SourceRecursiveIntersectionNative` interpreter.

## Closed local component

`SourceCurrentAllocatedRecursiveDomainCode.lean:24` defines `Closed source
inventory`. It requires the empty key and exact extension by actual original
available operands. `source_closed:37` derives it for the computed source
inventory. `Certified:47` keeps one fixed source HEAP for operand scope and a
separate current machine for domain representation and physical effects.

`node_certified:310` proves every actual node compiler branch. Its arguments are
`source inventory facts closed request scope member state valid semantic ready
growth history`. `body_certified:421` proves the code emitted by the supplied
actual checked body yield. It takes `source inventory facts request scope member
before after code valid semantic ready yielded`. It has no symbol-equality,
word-range, semantic completion, or desired result premise.

`enter_member:77` projects the exact key passed to `IntersectionEmptyDomain.make`.
It matches `NativeDomainTrace.CodeEntered:24` literally. The new module's final
source hash is `a87444fcab499c4c549a6c280d992797f82880ff100204e37b444f7862cea6c6`.
Its separate component manifest records all public and integration checks.

## Required prefix invariant

For a fixed source heap, initial domain cache, and finite key inventory, retain
these facts at the exact current checked state:

1. `PhysicalCompletion.Good`, `SemanticReady`, heap `Grows source current`, and
   issued-node history `Extends source.nodes.issued current.nodes.issued`.
2. An actual `DomainAllocation.Trace inventory initialDomains current.domains`.
   This is allocation history already executed. It is not a future-prefix plan.
3. The new local source certificate at the current machine. For an `edgeBody`
   control, use original `EdgeScope`, inventory membership, and the physical
   continuation post, as in `AdmissionTrace.ControlCertified:43`.
4. Physical body safety and current work operands, with annotation fields. Use
   `compileNode_safe`, `CodeProgress.compileNode_operands:224`,
   `CodeProgress.body_certified:327`, and `FieldClosure.body_fields:62`.
   Driver finish frames need the actual enclosing owner and body post. A flat
   `Safe` or `Operands` assertion at every current control does not cover them.

Do not require a domain to be represented in the original machine. Enter can
allocate it later. `FiniteOrdinaryWordExecution.Origins:30` stores `NodeReady`
and `EdgeReady` in one fixed machine. That design is valid for its empty-domain
fragment. It cannot be reused unchanged for a recursive entered domain.
Current `PhysicalCache.Valid:34` already stores current readiness and checked
keys for every cell phase. It avoids this fixed-domain restriction.

At each step, use the invariant in this order:

1. The current source request scope bounds operand words with the INITIAL node
   and edge supplies. `SourceInventory.node_key_safe:133` and
   `edge_key_safe:150` take only the current domain-ID bound in addition.
2. Obtain that bound from the allocation history so far, initial cache validity,
   and `initialDomains.next + inventory.length < 2^(bits+1)`.
   `DomainAllocation.Trace.identity_lt:107` applies to the current represented
   domain. It does not require later cache-counter bounds.
3. Combine current words with current physical operands to derive
   `PhysicalExecution.Inputs`. Apply `PhysicalCompletion.step_invariants:129`,
   `SemanticHeap.step_semantic:58`, and field closure at this single step.
4. At enter, extract exact key membership with `enter_member`. Use
   `NativeDomainTrace.yielded:123` and `DomainAllocation.Trace.trans:49` to append
   this ONE actual allocation step. Retain history for every other instruction.
5. Update the local certificate at the actual next state. Expand node and edge
   bodies using the closed local compiler theorems. No result law supplies
   request scope or domain membership.

`NativeDomainTrace.trace:152` currently takes `Prefixes:132`. This is useful
AFTER the new induction derives prefix admission. Supplying `Prefixes` as an
initial premise would leave the new initial-only word theorem unfinished.
Use `yielded` incrementally inside that proof instead.

## Exact recursive instructions and captured requests

`RequestScope.NodeScope.mu:85` derives original stored body scope.
`SourceInventory.extend_mem:84` derives supported names and canonical seen pairs
from the actual source identities. `Domain.extend_seen:96` states that each new
seen pair is the inserted pair or an older member. `Environment.enter_seen:104`
adds that pair before any child query. The new compiler certificate records the
literal extended key. No `Words` theorem supplies seen-pair membership.

`RequestScope.OriginalBindings.read:144` reads the exact original Mu from the
CURRENT grown heap. Its premises are current heap facts, source growth, and
issued history. The read uses stored probes; it does not unfold with allocation.
`RecursiveDomainCode.reference_certified:289` uses that exact result.

`optionalBinder` can allocate constructor records and probes. The continuation
uses its actual `.done value after` and derived validity, extension, and semantic
readiness. A pending outcome has no yielded successor. New constructed results
stay in reconstruction continuations; they are not source operands of another
compiled recursive request. Their identities therefore need no new original-key
budget. Their physical effects and availability still need proof.

For warm calls, use `PhysicalCache.node_request_exact:173` /
`edge_request_exact:189` or the supplied lookup-demand wrappers
`node_started:280` / `edge_started:295`. They recover the COMPLETE actual owner
from current physical validity, readiness, and the newly derived current key
bound. `node_ready:236` / `edge_ready:258` supply physical hit results.
Initial unrelated warm entries need no fixed-source scope certificate. Exact
key/readback equality transports the current request's scope to its winner.

## Finish-frame obstacle and smallest next module

`PhysicalTraceCompletion.Trace:31` stores `PhysicalExecution.Inputs:47`.
Node and edge inputs already contain word checks. Thus a supplied physical trace,
`Trace.plan`, or `AdmissionTrace.Trace.covered` cannot bootstrap `WordRanges`.
The raw `Steps` relation at `NativeDemandTrace:18` has no such premise.

A finish instruction's physical input is its exact evaluating owner plus the
candidate's availability or residency. The new local certificate intentionally
ignores that driver frame. `Safe` and `CodeProgress.Operands` reject finish
instructions. An ordinary first-order step induction with only these local
predicates therefore lacks the finish input.

Split an arbitrary raw prefix around each compiled body and its appended
continuation. If the prefix remains inside a nonpure body, invoke the smaller
prefix induction there. If the body has actually returned, derive its physical
post from the smaller raw trace. Then prove the exact owner survived and consume
its literal finish step. The supplied trace determines the intermediate result;
there is no assumed body completion.

The reusable owner theorem is already raw:
`SourceEqualityNativeDemandRunning.trace_retains:41` takes actual `Steps`,
`Clean`, and structural `Shape`. It requires no word checks or physical trace.
Its `node_body_cell:216` and `edge_body_cell:227` are completed-run wrappers.
Use `compileNode_bodyCode` / `body_clean`, `PhysicalCache.Valid.shape:45`, and the
raw `trace_retains` directly for the smaller completed body.

The checked `steps_bind_inverse` in `NativeDemandTraceSplit:41` handles ONLY a
completed appended trace. Root has now closed the arbitrary-prefix gap in the
NEW `SourceEqualityNativeDemandPrefixSplit.steps_bind_cases:16`. It retains
exact checked controls and complete states. Its `Steps.length_le_complete:60`
compares a supplied completed trace with a prefix of the same initial call.
It does not assume that arbitrary prefixes complete.

The smallest remaining production component is the simultaneous raw-prefix
induction above and its `WordRanges` projection. It must not
use `CodeBounds.NodeBelow/EdgeBelow` as an unexplained scope certificate: those
predicates also contain semantic `Completes` and a strict successful bound.

## Quantitative scope

Use width `bits+2`. Initial source nodes require `< 2^bits`, including the tag-3
all-ones sentinel restriction for original references. Initial source edges
require `≤ 2^(bits+2)`. The domain budget is strict after the reserved-zero shift.
`DomainAllocation.Trace.identity_lt` accounts for that shift exactly.

The coarse inventory has length `2^(N+N*N)` where `N=source.nodes.next`. It is an
initial-only bound, but it can exceed practical machine capacity for small warm
heaps. `Closed source inventory` permits a smaller justified carrier later.
Neither local compiler closure nor this proposed prefix proof bounds constructor
allocation, recursive total work, outer selected narrowing, runtime completion,
or the full library. The current checkpoint has not derived full `WordRanges`.

## Final helper validation and next theorem shape

The new checked splitter has source SHA256
`7f0b5c9038018041f4cc760d7213883df779cc7a90f130bde7c16cc089cf113e`.
Its direct strict check is clean. Root's final canonical Audit completed with
2700 jobs and 61554 dependency checks. The review pins an owned copy of that log.
The separate Code component keeps the exact preceding 2699-job log and both
manifest-history artifacts. No production source changed after its final hash.

A practical next theorem starts from a clean body, its physical `Safe` and
`Operands` proofs, new `Certified`, annotation fields, initial `Good` and
`SemanticReady`, fixed-source growth/history, and actual domain history so far.
It takes an ARBITRARY raw `Steps fuel control before next after`. It should
return current physical validity, semantic readiness, extension and fields,
actual domain history, the next local source certificate, and `Words next`.
When `next` is a pure value, the certificate gives that body's physical post.
The induction must also discharge the literal protected finish step after each
actual nested return. It can use strong induction on the supplied prefix length.
It requires no semantic `Completes` for that purpose.

At a top-level `requestNode emptyDomain left right`, initial scope, empty
membership, physical request safety, and trivial continuation fields provide
the start. Original available input keys, strict domain-inventory headroom, and
initial physical/semantic readiness remain explicit. `WordRanges` then follows
by quantifying the proved raw-prefix theorem. A `Prefixes`, `InputsThrough`, or
physical `Trace` argument must not reappear in that initial public endpoint.
