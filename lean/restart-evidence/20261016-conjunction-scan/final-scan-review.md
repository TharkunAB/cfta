# Final allocated Seeded and current Scan completion review

Read-only review, 2026-10-16 06:59 CEST. No source was edited. No build or
duplicate public probe ran. The root reports canonical completion build
1186, terminal exit 0. This note is an independent source review, not an
additional build result. No material defect was found in the physical
finite-completion scope.

## Real checked states and source fold

`SourceCurrentAllocatedSeededQuery.Operand` (44–49) stores the actual
Forest projection and advances only the returned constructor heap. Its
equality state and all native tables remain those of the literal input.
`Fold` (52–60) orders head projection, tail Fold, then actual checked
empty-domain `requestNode value tail` at the tail's returned full state.
The native trace is the physical Trace. It has no NodeProduced or language
premise. `Seeded` (63–68) rotates `seed::rest` to `rest++[seed]`, matching
the source `foldr intersect seed rest` at Equality/Operations.hs:228–230.
For three paths the inner native call uses p2 and p0; the outer call uses
p1 and that returned tail. No left fold or eager projection pass is
substituted.

`Operand.unique`, `Fold.unique`, and `Seeded.unique` retain literal
values and full checked states. Their proofs use actual projection
uniqueness and checked execution stability, not a language equivalence or
heap-effect approximation. `Seeded.effects` constructs its own finite
receipt and aligns it with the supplied actual raw graph by that exact
uniqueness. It does not require a supplied final invariant.

## Range plans and generated operands

`FoldRanges` (71–80) contains only a tail range plan after an actual head
projection and WordRanges after actual head/tail prefixes. Those graph
receipts occur as antecedents. They assert no completed tail exists, no
final readiness, no output semantics, and no successful parent body.
The induction in `fold_complete` first constructs the actual projection,
then constructs the tail from the recursively supplied range plan. It
uses the resulting actual tail receipt to select the current native
WordRanges. Thus the range-plan use is not circular.

The key generated-operand bridge is at lines 196–204. The head projection
is transported through the actual tail's Keeps. Both operands have
already proved `free=[]` and availability in the actual later heap.
`closed_original` derives their Original payload syntax from that later
heap's coherence. These are facts about the two INPUT operands of this
leaf. They are obtained before its result exists.

`ScopeCompletion.initial_complete` then derives the independent request
schedule at this same current heap. It receives and preserves the same
actual warm state. It initializes no table and uses no fixed semantic
model. It returns its own physical trace, closed available result, Good,
Scoped, SemanticReady, and Idle. The result can therefore serve as an
input to the next outer leaf by the same argument. This does not assert
that arbitrary generated open values have Original payload syntax.

`NativeTraceEffects.effects` (29–60) derives the trace's physical plan,
then actual physical, semantic, cost, loaded-field, and operation-cache
effects. It takes no final CostHeap, final Good, or result language law.
The native request continuation's static field check is trivial at the
root; generated guarded fields follow the actual checked allocation
proofs. There is no universal conjoin-field premise.

## False secondary anchor

`false_class_complete` (251–281) obtains PathSupport at the ACTUAL returned
secondary anchor from class_support. GateReady there follows from the
initial SemanticReady and CostHeap plus actual gate preservation. Proper
paths remain explicit. The original forest needs only availability; its
unrelated children may stay open.

The secondary gate's loaded-field effects retain the same operation cache.
Its returned heap is passed to actual Seeded. Extension and Effects then
compose that one gate with the subsequent projections and native traces.
Using the gate receipt in multiple proofs does not add another gate or
unfold operation. It supplies no synthetic source call at the anchor.

## Final finite Scan

`SourceCurrentConjunctionClassScanCompletion.finite` (50–126) inducts on
the strict original class suffix. Every state and memo argument to the
tail is an actual returned component. Primary false selects. Secondary
true skips. Secondary false constructs the allocated Seeded from its
range checks and the gate-derived anchor. The current conjunction Memo
then runs at that Seeded's exact physical result. Its Effects restore
the checked state with the returned equality-operation cache and the
same native cell tables and domain cache.

Initial fourth-memo Correct is transported through the primary gate and
the secondary-plus-Seeded effects. The actual new Memo call derives final
Correct, AnswerSound, and Extends. A false answer passes its exact saved
table into the suffix. A true answer returns immediately and requests
no suffix range plan. The no-query branches retain the memo unchanged.
Earlier selected occurrences are retained only in the reached prefix on
rejection. No completed full partition is assumed before the refused any.

The theorem assumes only initial Ready, original Values, proper paths,
initial fourth-memo Correct, and the range-only plan. No future query,
parent result law, final field heap, final memo invariant, or completed
Scan is supplied. Initial Ready includes the physical Good, semantic and
stored-cost heap invariants, Scoped native cells, and Idle. Those are
legitimate warm input invariants; cold derivation is a separate adapter.

## Exact scope

This proves finite completed resident-model Scan execution with physical
heap and equality-state effects, retained loaded fields, closed query
results, native cell scope/idle preservation, and a correct conservative
fourth memo. It does NOT prove Seeded retains the original class's common
accepted subtree. That semantic bridge for dynamically generated operands
and warm native cells remains separate. Physical Original derivation is
not semantic model-extension transport.

The result also does not compose all three global gate/query memo call
traces, establish GHC demand/publication or concurrency, justify concrete
container/key representation or unlimited machine capacity, or complete
the constrained outer caller. Source budget instantiation is 1000; the
generic Nat budget parameter is a logical component. The module comments
state these physical-versus-semantic and runtime boundaries.

Reviewed SHA256 values:

```
55e0434ab1dd7d232ad4546cd22aa5d8caa5dd91ef9651d7e7f5db4c8fb807bc  SourceCurrentAllocatedSeededQuery.lean
b5fe7c3c9cb143f63f4294c7696a18478846a35d12c5058eabf6d13e10d9f427  SourceCurrentConjunctionClassScanCompletion.lean
46edf035a9e6890053ccd6caee25052ca293e42277e10bbba75529f84fdd5cd1  SourceCurrentConjunctionClassScan.lean
4168b87e3db60925ea6ccb04ab0068939ed72b53634d0757b79e5fc13cfd35df  SourceCurrentAllocatedNativeTraceEffects.lean
```
