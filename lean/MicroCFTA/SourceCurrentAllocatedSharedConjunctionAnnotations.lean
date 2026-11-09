import MicroCFTA.SourceCurrentAllocatedSharedConjunctionOutcome
import MicroCFTA.SourceCurrentConjunctionSharedWorkerAnnotations

/-!
# Full shared caller outcomes with physical annotations

The same actual call supplies the full Post, ordered global memo receipts,
and the physical annotation predicate. Failure retains the original fourth
memo, diagnostic, and private snapshot. No future state or successful run is
an input. Checked caller selection and native bounds remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedConjunctionAnnotations
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionSharedWorkerOutcomeMemos (CallReads returnedMemo)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap
local notation "call" => SourceCurrentConjunctionSharedWorker.call
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Current caller invariants and annotations derive both at every actual outcome. -/
theorem verified {inventory : Inventory} (annotation : Guard → Prop) (p h budget : Nat)
    (before : Caller width) (query : Node) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query)
    (known : AnnotationHeap annotation before.checked.native.machine.heap) :
    let outcome := call p h budget before.fourth query (physical before.checked)
    ∃ final, CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before
          (advancePhysical before.checked outcome.state.storage.requirements.physical)
          (returnedMemo before.fourth outcome) before.merge) final ∧
      AnnotationHeap annotation outcome.state.storage.requirements.physical.heap ∧
      Available outcome.state.storage.requirements.physical.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      (match outcome with
       | .failed _ _ => True
       | .done result _ => SourceCurrentEmptinessMemo.AnswerSound formulas solver query result.1) := by
  dsimp only
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  have annotations := SourceCurrentConjunctionSharedWorkerAnnotations.call_heap annotation
    p h budget before.fourth query (physical before.checked) ready known available
  obtain ⟨final, reads, post, resident, retained, same, answer⟩ :=
    SourceCurrentAllocatedSharedConjunctionOutcome.verified formulas solver p h budget before query memos initial available
  exact ⟨final, reads, post, annotations, resident, retained, same, answer⟩

/-- An actual fault retains its exact heap annotations and full caller Post. -/
theorem failed {inventory : Inventory} (annotation : Guard → Prop)
    {p h budget : Nat} {before : Caller width} {query : Node} {memos : Memos} {after : WorkState}
    {fault : SourceCurrentConjunctionSharedWorker.Fault Symbol FullSyntax.Formula}
    (actual : call p h budget before.fourth query (physical before.checked) = .failed fault after)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query)
    (known : AnnotationHeap annotation before.checked.native.machine.heap) :
    ∃ final, CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before
          (advancePhysical before.checked after.storage.requirements.physical) before.fourth before.merge) final ∧
      AnnotationHeap annotation after.storage.requirements.physical.heap ∧
      Available after.storage.requirements.physical.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have complete := verified formulas solver annotation p h budget before query memos initial available known
  dsimp only at complete
  rw [actual] at complete
  obtain ⟨final, reads, post, annotations, resident, retained, same, _⟩ := complete
  exact ⟨final, reads, post, annotations, resident, retained, same⟩

end MicroCFTA.SourceCurrentAllocatedSharedConjunctionAnnotations
