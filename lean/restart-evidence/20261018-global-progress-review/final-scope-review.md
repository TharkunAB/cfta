# Independent review of native guard returns and closed alphabets

Reviewed at 2026-10-18 03:37 CEST. This is a read-only source and evidence
review. No Lean build was repeated. No production file was changed.
No material defect was found in the final source statements or proofs.

## Two different heap predicates

`SourceCurrentNativeGuardHeapReturns` is final SHA256
`77f472becb858c0211f59de50e9311e445220aa1b454b40031128d0e7b67c8bf`.
Its `Heap` abbreviation denotes `SourceCurrentConstrainedCapGuardHeap.Heap`.
For each stored Mu, this predicate equates the finite guard-depth profiles
of its literal body and ordinary probe. The supplied guard predicate is
arbitrary. The predicate does not assert that every resident edge satisfies
it, that a returned profile is zero, or that two values are equal.
See `SourceCurrentConstrainedCapGuardHeap.lean:20-29` and the profile
observer in `SourceCurrentConstrainedCapGuardDepth.lean:40-63`.

`SourceCurrentNativeClosedGuardAlphabet` is final SHA256
`14c66906ae2e40bcf4d2efc44d2c19814e2135201e7801661e7278856d94e75a`.
Its `Heap` abbreviation instead denotes `SourceEqualityAnnotationHeap.Heap`.
That predicate checks the full raw guard of every physical edge record.
It is not the Mu body/probe invariant. Neither new module converts one
predicate into the other.

## Actual completed-call guard preservation

`GuardHeapReturns.code`, lines 339-347, takes an actual successful literal
`execute` equation. It also takes initial physical Good, the initial causal
Heap, and the program's Safe, Operands and allocated CodeFields conditions.
Those generic code conditions are real premises. The node and edge wrappers,
lines 349-367, derive them for actual source request code. The wrappers need
initial Good and ready operands, rather than a supplied reached-input plan
or a completed trace. Successful completion remains a premise.

Initial Good includes physical native operands/results, constructor Ready,
operation Valid, allocated row fields, SemanticReady and the Mu cost heap.
It does not assert a native result language or word-range correctness for
all memo keys. The physical Cells definition uses a trivial key relation.
This distinction is visible in `SourceCurrentNativeOperationHeap.lean:122-136`
and `SourceCurrentNativeOperationInvariants.lean:27-34`.

The proof performs strong induction on actual yielded steps. Direct and
memoized node requests use their actual captured requests. Ready hits keep
the constructor heap. Evaluation derives the captured operand readiness
from the current physical cell. Bind decomposition identifies the actual
body and finish traces. The protected finish changes no constructor heap.
The corresponding edge proof uses its actual checked edge-body expansion.
Work and optional-binder cases reuse existing causal-heap producers. The
optional pending branch cannot produce the assumed successful code return.
Intermediate Good, availability and field growth come from actual physical
return theorems. No desired candidate profile equality is assumed as a new
callback result law. The final private comment no longer claims a word-range
property that the weaker Cells invariant does not contain.

The public result is completed-call preservation. It is not an initial
completion producer, an all-failure theorem, a result annotation theorem,
or a general used-binder value-congruence theorem.

## Fixed finite raw guard carrier

`Closed` contains source Top and closes the alphabet under the literal full
source conjunction. `step_subset` and `retained` use exactly those facts.
`retained`, lines 37-63, takes an actual checked physical Trace, initial
physical Good, allocated control fields, initial raw annotation Heap and
static guard Fields. Its trace constructors carry actual step inputs.
The induction derives later Good, allocated fields, annotated heaps and
continuation fields from those inputs. It needs no instruction-count ceiling.
It does not construct the trace or prove that a query terminates.

The raw finite product inventory is not assumed closed. `originalAlphabet`
filters that inventory by actual guard derivability. Cached initial equality
literals make membership equivalent to `Derived`. Top and conjunction then
prove closure of the filtered list. `original_heap` and `original_retained`
retain the initial causal annotation premise explicitly. The list is
noncomputable because its filter uses classical derivability membership.
The theorem establishes a finite carrier; it does not provide an executable
membership procedure or a numeric execution budget.

This carrier bounds complete stored own fields. It does not bound descended
inherited payloads, physical node identities, requests, or execution length.
No proper initial-source row occurrence or all-active-owner exclusion follows.

## Source-built checks and selected evidence

`native-guards-kernels-1` builds two distinct closed productive raw Mu inputs.
Both have leaf and pair rows; one also has an extra row. All source guards
are Top. Initial semantic, cost, physical and operation facts come from the
actual source build and field allocation. For every guard predicate, source
construction derives the initial causal Heap. The cold native request
returns a Mu and publishes native node cells. The exact warm request returns
the same value without increasing the node-cell count. The fixture applies
the new node endpoint to both actual calls. It has no supplied future return
or returned-heap premise. It tests causal profile retention, not mixed
positive-field origin transport or full body/probe value equality.

`closed-alphabet-kernels-4` builds two original ordinary leaf rows with
syntactically distinct residual guards. Their allocated equality fields are
empty. An actual two-instruction checked edge-body trace constructs the
literal joined guard. The result is resident, differs from both original
full guards, and belongs to the same finite original alphabet. The final
raw annotation Heap and continuation Fields are derived by `original_retained`.
This exercises full-guard closure and actual row allocation. It is not a
complete memoized query or an inherited-path bound.

Selected production strict logs `native-guards-direct-3` and
`closed-alphabet-direct-2` contain exactly zero bytes. The canonical receipts
are `native-guards-canonical-2` and `closed-alphabet-canonical-1`.
Constructed strict logs `native-guards-kernels-1` and
`closed-alphabet-kernels-4` also contain exactly zero bytes.
The existing full probes are `native-guards-public-1` (3 public pairs),
`closed-alphabet-public-1` (8 public pairs), and the corresponding
`kernels-public-1` groups (one constructed pair each). A read-only check of
all four groups confirms all eight explicit options, full signatures and
proofs, standard axioms only, and no printer omissions or diagnostics.
All selected executions record effective 4 GiB maximum/high and zero swap.
Earlier failed attempts stay in their original root evidence package.

The remaining global progress gaps are unchanged. Actual row provenance
must still supply a suitable occurrence order and compatibility with every
active physical owner. A separate argument must bound fresh requests.
Neither finite guard closure nor causal guard-profile preservation proves
these facts, general outer termination, repeated-pass convergence, or Haskell
runtime correspondence.
