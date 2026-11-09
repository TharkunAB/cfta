import MicroCFTA.SourceCurrentConjunctionSharedWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionGuardArity

/-!
# Complete shared calls with the full current caller contract

Current caller facts derive sufficient observation bounds. One actual call
at those bounds supplies the returned global bundle, full Post and three
distinct heap invariants. Every larger pair of bounds returns the identical
answer, fourth memo and private worklist state. The read receipt belongs
only to the derived base bounds. This theorem gives no computed resource
forecast and does not change checked caller selection.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedConjunctionCompletion
open Cache
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConjunctionSharedWorkerOutcomeMemos (CallReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap
local notation "call" => SourceCurrentConjunctionSharedWorker.call
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Current inputs derive one complete call, its full Post, and exact replay at all larger bounds. -/
theorem finite {inventory : Inventory} (annotation causal : Guard → Prop) (budget : Nat)
    (before : Caller width) (query : Node) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query)
    (known : AnnotationHeap annotation before.checked.native.machine.heap)
    (guarded : SourceCurrentConstrainedCapGuardHeap.Heap causal before.checked.native.machine.heap)
    (arity : SourcePruningEnumerationArityOrigins.Heap before.checked.native.machine.heap) :
    ∃ (p h : Nat) (answer : Bool) (saved : Memo) (after : WorkState) (final : Memos),
      call p h budget before.fourth query (physical before.checked) = .done (answer, saved) after ∧
      CallReads p h budget before.fourth query (physical before.checked) memos final ∧
      Post formulas solver inventory before
        (SourceCurrentAllocatedPartialState.advance before
          (advancePhysical before.checked after.storage.requirements.physical) saved before.merge) final ∧
      AnnotationHeap annotation after.storage.requirements.physical.heap ∧
      SourceCurrentConstrainedCapGuardHeap.Heap causal after.storage.requirements.physical.heap ∧
      SourcePruningEnumerationArityOrigins.Heap after.storage.requirements.physical.heap ∧
      SourceCurrentEmptinessMemo.AnswerSound formulas solver query answer ∧
      Available after.storage.requirements.physical.heap query ∧
      Extends memos.unfolding final.unfolding ∧ final.query = memos.query ∧
      (∀ P H, p ≤ P → h ≤ H →
        call P H budget before.fourth query (physical before.checked) = .done (answer, saved) after) := by
  have ready := SourceCurrentAllocatedConjunctionMemo.ready before.checked initial.ready.good
    initial.ready.semantic initial.ready.costs
  obtain ⟨p, h, answer, saved, after, stable⟩ :=
    SourceCurrentConjunctionSharedWorkerCompletion.call_initial budget before.fourth query
      (physical before.checked) ready available
  have actual := stable p h (Nat.le_refl _) (Nat.le_refl _)
  have checked := SourceCurrentAllocatedSharedConjunctionGuardArity.verified formulas solver
    annotation causal p h budget before query memos initial available known guarded arity
  dsimp only at checked
  rw [actual] at checked
  dsimp only [SourceCurrentConjunctionSharedWorker.Outcome.state,
    SourceCurrentConjunctionSharedWorkerOutcomeMemos.returnedMemo] at checked
  obtain ⟨final, reads, post, annotations, causalKept, arityKept, resident, retained, same, sound⟩ := checked
  exact ⟨p, h, answer, saved, after, final, actual, reads, post, annotations, causalKept, arityKept,
    sound, resident, retained, same, stable⟩

end MicroCFTA.SourceCurrentAllocatedSharedConjunctionCompletion
