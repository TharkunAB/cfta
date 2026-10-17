# Actual native operation invariant production

## Contract and proof

SourceCurrentNativeOperationInvariants proves invariant preservation through
actual completed checked native execution. Cells retains physical machine
validity, bounded native handles, table-to-cell links, resident captured
operands, and resident returned records. Its key relation is True. It does
not require a word range or identify an aliased requester with its stored
captured request. Good adds constructor heap Ready, full equality-operation
memo Valid, and allocated field availability for every stored edge guard.
Constructor heap Ready still contains its existing semantic and depth facts.
There is no new native semantic result law in Good.

Good.of_checked forgets the stronger key law of the old physical Good.
initial constructs Good at empty native tables from initial heap, domain,
operation and field facts. The proof uses fresh native handles through the
existing FlatMemoThunk allocation laws. It does not infer fresh handle
safety from key injectivity.

The main induction uses the actual number of raw yielded Steps to a pure
return. It decomposes actual nested body and continuation executions.
A warm hit obtains physical result availability from the stored cell.
An evaluated cell compiles its actual captured request. The node code
obtains Safe and Operands from that request's current physical readiness.
The edge-body proof constructs the actual allocated prefix and derives
Safe, Operands and emitted field facts from its literal branch. The body
induction derives its returned record before the finish updates the cell.
No desired body result, future invariant, or finish safety is assumed.

Actual work, environment entry, reads, and optional Mu reconstruction retain
all state components. The optional Mu branch uses current body availability
and constructor facts. It uses the existing actual reconstruction producer.
Nested binders, unions, reference reads, empty and ordinary branches remain
in scope. Closed operands, finite Cap, NoDeep and whole-forest closure are
not additional premises.

The generic code theorem takes initial Safe, Operands and code-field facts.
These are structural continuation certificates. node and edge derive those
certificates internally from their initial NodeReady or EdgeReady. These
public endpoints require only initial Good, current operands and the actual
completed literal execution. They derive final Good, machine Extension,
Keeps, operation Grows and returned physical availability or residency.
There is no InputsThrough, per-prefix Ready or Valid, Graph, or Ranges input.
node_dispatch follows the actual node return with indexed descent. It lifts
an initially Ready combined value, derives a new Ready descended value,
and derives full operation Valid at that actual next state.

## Constructed checks

The source builds an ordinary row with an ordinary child and a productive
Mu child from empty. Its stored field contains [[0,0],[0,1]]. Its actual
field construction and empty-field allocation derive initial Good.
A literal cold edge call completes. It creates a nonempty completed
combination-cache cell. An exact warm call retains the entire returned
state. The first witness invokes edge on both actual calls.

The second witness uses that actual first return. A warm node call returns
the Mu child. node_dispatch then derives the actual inherited descent.
The constraint counter strictly increases. Full operation Valid, new Ready
and exact original field load hold at that final state. No future graph,
reached resource bound, or future invariant is a fixture premise. The
private witnesses have exact public aliases to keep full proof printing
finite. The statements are unchanged by this packaging.

## Validation and boundaries

The selected production check is actual-invariants-direct-1. Its raw log has
zero bytes. Canonical1 passes 1779 jobs. Its only warning replays the older
InternedFreshOrdinaryClosedCompletion unused variable. All earlier partial
proof attempts remain as immutable executed source/log pairs.

The selected constructed strict check is kernels3, with zero log bytes.
Kernels1 failed on the proof declaration's missing type and an unreduced
Option contradiction. Kernels2 exited zero but reported a 282-byte defProp
warning. Kernels-public1 therefore remains unselected. The final proof has
an explicit theorem signature. No linter is disabled.

Public1 checks all 17 public declarations: eight handwritten heads, two
constructors, and seven fields. Kernels-public2 checks two constructed
witnesses. Both groups use all eight explicit print settings, full proof
printing, and standard axiom reports. The verifier rejects omissions and
printer failures. Each worker records effective 4 GiB maximum/high memory
limits and zero swap. The full raw failed and successful outputs remain.

This is a completed-execution invariant producer. It does not construct
unbounded native termination. It does not establish a native semantic key
law without word checks. It does not yet compose through complete Parent,
Local, or outer mutual worker execution. All-active node-key exclusion and
a well-founded bound on fresh requests remain separate open obligations.
The work changes no Haskell source and makes no new runtime correspondence
claim. The independent positive-origin review is a separate read-only note.
