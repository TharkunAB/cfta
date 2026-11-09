import MicroCFTA.SourceCurrentAllocatedSharedConjunctionAnnotations
import MicroCFTA.SourceCurrentConjunctionSharedWorkerGuardArity

/-!
# Full shared caller outcomes with annotations, causal guards and arity

One actual call and one returned global bundle supply the full Post and
three distinct physical invariants. Every fault retains its exact private
snapshot and original fourth memo. All premises concern the current state.
Checked caller selection and sufficient proof bounds remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedConjunctionGuardArity
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

/-- Current caller invariants and annotations derive the full contract at every actual outcome. -/
theorem verified {inventory : Inventory} (annotation causal : Guard → Prop) (p h budget : Nat)
    (before : Caller width) (query : Node) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query)
    (known : AnnotationHeap annotation before.checked.native.machine.heap)
    (guarded : SourceCurrentConstrainedCapGuardHeap.Heap causal before.checked.native.machine.heap)
    (arity : SourcePruningEnumerationArityOrigins.Heap before.checked.native.machine.heap) :
    let outcome := call p h budget before.fourth query (physical before.checked)
    ∃ final, CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before
          (advancePhysical before.checked outcome.state.storage.requirements.physical)
          (returnedMemo before.fourth outcome) before.merge) final ∧
      AnnotationHeap annotation outcome.state.storage.requirements.physical.heap ∧
      SourceCurrentConstrainedCapGuardHeap.Heap causal outcome.state.storage.requirements.physical.heap ∧
      SourcePruningEnumerationArityOrigins.Heap outcome.state.storage.requirements.physical.heap ∧
      Available outcome.state.storage.requirements.physical.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      (match outcome with
       | .failed _ _ => True
       | .done result _ => SourceCurrentEmptinessMemo.AnswerSound formulas solver query result.1) := by
  dsimp only
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  have causalKept := SourceCurrentConjunctionSharedWorkerGuardArity.call_guard_heap causal
    p h budget before.fourth query (physical before.checked) ready guarded available
  have arityKept := SourceCurrentConjunctionSharedWorkerGuardArity.call_arity_heap
    p h budget before.fourth query (physical before.checked) ready arity available
  obtain ⟨final, reads, post, annotations, resident, retained, same, answer⟩ :=
    SourceCurrentAllocatedSharedConjunctionAnnotations.verified formulas solver annotation
      p h budget before query memos initial available known
  exact ⟨final, reads, post, annotations, causalKept, arityKept, resident, retained, same, answer⟩

/-- An actual fault retains all three exact heap invariants and the full Post. -/
theorem failed {inventory : Inventory} (annotation causal : Guard → Prop)
    {p h budget : Nat} {before : Caller width} {query : Node} {memos : Memos} {after : WorkState}
    {fault : SourceCurrentConjunctionSharedWorker.Fault Symbol FullSyntax.Formula}
    (actual : call p h budget before.fourth query (physical before.checked) = .failed fault after)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query)
    (known : AnnotationHeap annotation before.checked.native.machine.heap)
    (guarded : SourceCurrentConstrainedCapGuardHeap.Heap causal before.checked.native.machine.heap)
    (arity : SourcePruningEnumerationArityOrigins.Heap before.checked.native.machine.heap) :
    ∃ final, CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before
          (advancePhysical before.checked after.storage.requirements.physical) before.fourth before.merge) final ∧
      AnnotationHeap annotation after.storage.requirements.physical.heap ∧
      SourceCurrentConstrainedCapGuardHeap.Heap causal after.storage.requirements.physical.heap ∧
      SourcePruningEnumerationArityOrigins.Heap after.storage.requirements.physical.heap ∧
      Available after.storage.requirements.physical.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  have complete := verified formulas solver annotation causal p h budget before query memos initial available known guarded arity
  dsimp only at complete
  rw [actual] at complete
  obtain ⟨final, reads, post, annotations, causalKept, arityKept, resident, retained, same, _⟩ := complete
  exact ⟨final, reads, post, annotations, causalKept, arityKept, resident, retained, same⟩

end MicroCFTA.SourceCurrentAllocatedSharedConjunctionGuardArity
