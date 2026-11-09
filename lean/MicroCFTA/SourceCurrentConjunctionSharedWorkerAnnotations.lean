import MicroCFTA.SourceCurrentConjunctionSharedWorkerEffects
import MicroCFTA.SourceCurrentConjunctionSharedWorklistAnnotations

/-!
# Physical annotations at every shared call outcome

The exact exploration state supplies the decision heap. Pure table work and
completed memo publication do not change that heap. Open inputs and memo
hits retain the initial state. These laws include every modeled failure.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerAnnotations
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentConjunctionRowsAllocation (Ready)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap
local notation "decision" => SourceCurrentConjunctionSharedWorker.decision
local notation "closed" => SourceCurrentConjunctionWorklist.closed

section Generic
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every decision outcome retains the initial physical annotation predicate. -/
theorem decision_heap (annotation : Guard → Prop) (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (known : AnnotationHeap annotation before.heap)
    (available : Available before.heap start) :
    AnnotationHeap annotation (decision p h budget start before).state.storage.requirements.physical.heap := by
  cases classified : closed start with
  | false =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.decision_state, classified,
        Bool.false_eq_true, ite_false, SourceCurrentConjunctionSharedWorklistStep.initial,
        SourceCurrentConjunctionRequirementRows.initial, SourceCurrentConjunctionRequirementCells.initial] using known
  | true =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.decision_state, classified, ite_true] using
        SourceCurrentConjunctionSharedWorklistAnnotations.explore_heap annotation p h budget start before ready known available
end Generic

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsWorker.Physical ConcreteSymbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
variable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
  [DecidableEq ConcreteNode]

/-- Hits, successful misses, and failed misses retain annotations at the exact endpoint. -/
theorem call_heap (annotation : ConcreteGuard → Prop) (p h budget : Nat) (memo : Memo)
    (query : ConcreteNode) (before : ConcretePhysical) (ready : Ready before)
    (known : AnnotationHeap annotation before.heap) (available : Available before.heap query) :
    AnnotationHeap annotation
      (SourceCurrentConjunctionSharedWorker.call p h budget memo query before).state.storage.requirements.physical.heap := by
  cases hit : memo query.referenceOf with
  | some entry =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.call_state, hit,
        SourceCurrentConjunctionSharedWorklistStep.initial, SourceCurrentConjunctionRequirementRows.initial,
        SourceCurrentConjunctionRequirementCells.initial] using known
  | none =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.call_state, hit] using
        decision_heap annotation p h budget query before ready known available

end MicroCFTA.SourceCurrentConjunctionSharedWorkerAnnotations
