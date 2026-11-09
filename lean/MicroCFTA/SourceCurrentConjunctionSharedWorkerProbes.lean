import MicroCFTA.SourceCurrentConjunctionSharedWorkerEffects
import MicroCFTA.SourceCurrentConjunctionSharedWorklistProbes

/-!
# Clean probes at the actual shared call boundary

Decisions retain the exact exploration heap. Pure table reads, fixed-point
growth, and completed memo publication do not change that heap. Open inputs
and memo hits retain the initial physical state. These laws cover all faults
and do not select a checked caller or establish native execution bounds.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerProbes
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentConjunctionRowsAllocation (Ready)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
local notation "decision" => SourceCurrentConjunctionSharedWorker.decision
local notation "closed" => SourceCurrentConjunctionWorklist.closed

section Generic
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every decision outcome retains probes at the same actual returned physical heap. -/
theorem decision_probes (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (probes : ProbeHeap before.heap) (available : Available before.heap start) :
    ProbeHeap (decision p h budget start before).state.storage.requirements.physical.heap := by
  cases classified : closed start with
  | false =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.decision_state, classified,
        Bool.false_eq_true, ite_false, SourceCurrentConjunctionSharedWorklistStep.initial,
        SourceCurrentConjunctionRequirementRows.initial, SourceCurrentConjunctionRequirementCells.initial] using probes
  | true =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.decision_state, classified, ite_true] using
        SourceCurrentConjunctionSharedWorklistProbes.explore_probes p h budget start before ready probes available
end Generic

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsWorker.Physical ConcreteSymbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
variable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
  [DecidableEq ConcreteNode]

/-- Hits, completed misses, and failed misses preserve probes at their exact physical endpoint. -/
theorem call_probes (p h budget : Nat) (memo : Memo) (query : ConcreteNode) (before : ConcretePhysical)
    (ready : Ready before) (probes : ProbeHeap before.heap) (available : Available before.heap query) :
    ProbeHeap (SourceCurrentConjunctionSharedWorker.call p h budget memo query before).state.storage.requirements.physical.heap := by
  cases hit : memo query.referenceOf with
  | some entry =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.call_state, hit,
        SourceCurrentConjunctionSharedWorklistStep.initial, SourceCurrentConjunctionRequirementRows.initial,
        SourceCurrentConjunctionRequirementCells.initial] using probes
  | none =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.call_state, hit] using
        decision_probes p h budget query before ready probes available

end MicroCFTA.SourceCurrentConjunctionSharedWorkerProbes
