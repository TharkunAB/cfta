import MicroCFTA.SourceCurrentConjunctionSharedWorkerEffects
import MicroCFTA.SourceCurrentConjunctionSharedWorklistGuardArity

/-!
# Causal guards and arity at the actual shared call boundary

Every decision retains its exact exploration state. Pure materialization,
growth and completed memo publication retain that state. Both concrete heap
invariants follow the same actual decision and call, including every fault.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerGuardArity
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentConjunctionRowsAllocation (Ready)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "decision" => SourceCurrentConjunctionSharedWorker.decision
local notation "closed" => SourceCurrentConjunctionWorklist.closed

section Generic
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every decision outcome retains the heap predicate at the same actual returned physical heap. -/
private theorem decision_heap (property : InternedConstructorTemplates.State Symbol Guard → Prop)
    (exploreKeeps : ∀ p h budget (start : Node) (before : Physical), Ready before →
      property before.heap → Available before.heap start →
      property (SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before).state.storage.requirements.physical.heap)
    (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (known : property before.heap) (available : Available before.heap start) :
    property (decision p h budget start before).state.storage.requirements.physical.heap := by
  cases classified : closed start with
  | false =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.decision_state, classified,
        Bool.false_eq_true, ite_false, SourceCurrentConjunctionSharedWorklistStep.initial,
        SourceCurrentConjunctionRequirementRows.initial, SourceCurrentConjunctionRequirementCells.initial] using known
  | true =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.decision_state, classified, ite_true] using
        exploreKeeps p h budget start before ready known available
/-- Every actual decision outcome retains causal Mu guard observations. -/
theorem decision_guard_heap (annotation : Guard → Prop) (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (known : SourceCurrentConstrainedCapGuardHeap.Heap annotation before.heap)
    (available : Available before.heap start) :
    SourceCurrentConstrainedCapGuardHeap.Heap annotation
      (decision p h budget start before).state.storage.requirements.physical.heap :=
  decision_heap (SourceCurrentConstrainedCapGuardHeap.Heap annotation)
    (SourceCurrentConjunctionSharedWorklistGuardArity.explore_guard_heap annotation)
    p h budget start before ready known available
end Generic

section Arity
variable {AritySymbol : Type}
local notation "ArityGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ArityNode" => Value AritySymbol ArityGuard
local notation "ArityPhysical" => SourceCurrentConjunctionRowsWorker.Physical AritySymbol FullSyntax.Formula
variable [DecidableEq AritySymbol]
  [DecidableEq (EdgeKey AritySymbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
  [DecidableEq (Value AritySymbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))]

/-- Every actual decision outcome retains complete edge-record arity. -/
theorem decision_arity_heap (p h budget : Nat) (start : ArityNode) (before : ArityPhysical)
    (ready : Ready before) (known : SourcePruningEnumerationArityOrigins.Heap before.heap)
    (available : Available before.heap start) :
    SourcePruningEnumerationArityOrigins.Heap
      (SourceCurrentConjunctionSharedWorker.decision (Symbol := AritySymbol) (Formula := FullSyntax.Formula)
        p h budget start before).state.storage.requirements.physical.heap :=
  decision_heap (Symbol := AritySymbol) (Formula := FullSyntax.Formula)
    SourcePruningEnumerationArityOrigins.Heap
    SourceCurrentConjunctionSharedWorklistGuardArity.explore_arity_heap
    p h budget start before ready known available
end Arity

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsWorker.Physical ConcreteSymbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
variable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
  [DecidableEq ConcreteNode]

/-- Hits, completed misses, and failed misses preserve known at their exact physical endpoint. -/
private theorem call_heap (property : InternedConstructorTemplates.State ConcreteSymbol ConcreteGuard → Prop)
    (decisionKeeps : ∀ p h budget (query : ConcreteNode) (before : ConcretePhysical), Ready before →
      property before.heap → Available before.heap query →
      property (decision p h budget query before).state.storage.requirements.physical.heap)
    (p h budget : Nat) (memo : Memo) (query : ConcreteNode) (before : ConcretePhysical)
    (ready : Ready before) (known : property before.heap) (available : Available before.heap query) :
    property (SourceCurrentConjunctionSharedWorker.call p h budget memo query before).state.storage.requirements.physical.heap := by
  cases hit : memo query.referenceOf with
  | some entry =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.call_state, hit,
        SourceCurrentConjunctionSharedWorklistStep.initial, SourceCurrentConjunctionRequirementRows.initial,
        SourceCurrentConjunctionRequirementCells.initial] using known
  | none =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.call_state, hit] using
        decisionKeeps p h budget query before ready known available

/-- Actual memo hits and every miss outcome retain the original causal guard heap. -/
theorem call_guard_heap (annotation : ConcreteGuard → Prop) (p h budget : Nat) (memo : Memo)
    (query : ConcreteNode) (before : ConcretePhysical) (ready : Ready before)
    (known : SourceCurrentConstrainedCapGuardHeap.Heap annotation before.heap)
    (available : Available before.heap query) :
    SourceCurrentConstrainedCapGuardHeap.Heap annotation
      (SourceCurrentConjunctionSharedWorker.call p h budget memo query before).state.storage.requirements.physical.heap :=
  call_heap (SourceCurrentConstrainedCapGuardHeap.Heap annotation) (decision_guard_heap annotation)
    p h budget memo query before ready known available

/-- Actual memo hits and every miss outcome retain the original whole-record arity. -/
theorem call_arity_heap (p h budget : Nat) (memo : Memo) (query : ConcreteNode) (before : ConcretePhysical)
    (ready : Ready before) (known : SourcePruningEnumerationArityOrigins.Heap before.heap)
    (available : Available before.heap query) :
    SourcePruningEnumerationArityOrigins.Heap
      (SourceCurrentConjunctionSharedWorker.call p h budget memo query before).state.storage.requirements.physical.heap :=
  call_heap SourcePruningEnumerationArityOrigins.Heap decision_arity_heap
    p h budget memo query before ready known available

end MicroCFTA.SourceCurrentConjunctionSharedWorkerGuardArity
