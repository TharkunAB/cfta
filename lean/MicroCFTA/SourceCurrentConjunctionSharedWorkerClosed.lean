import MicroCFTA.SourceCurrentConjunctionSharedWorkerEffects
import MicroCFTA.SourceCurrentConjunctionSharedWorklistClosed

/-!
# Derived closed private cells at the shared call boundary

Current readiness and query availability derive closed private cells, raw
row spines, and stored table queries. The initial query need not be closed.
Actual admission checks justify closed sampled inputs. Open queries and
memo hits retain empty private heaps. This result does not assert that an
arbitrary cached Boolean is correct.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerClosed
open InternedConstructorTemplates (Value EdgeKey)
open InternedProbeProvenance (Available)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionSharedWorklistClosed (Invariant)
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

/-- Both successful and failed decisions derive closed stored cells and table queries. -/
theorem decision_closed (p h budget : Nat) (start : Node) (before : Physical)
    (ready : Ready before) (available : Available before.heap start) :
    Invariant (decision p h budget start before).state := by
  cases selected : closed start with
  | false =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.decision_state, selected,
        Bool.false_eq_true, ite_false] using
        SourceCurrentConjunctionSharedWorklistClosed.initial_closed budget start before
  | true =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.decision_state, selected, ite_true] using
        SourceCurrentConjunctionSharedWorklistClosed.explore_closed p h budget start before ready available
end Generic

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsWorker.Physical ConcreteSymbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
variable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
  [DecidableEq ConcreteNode]

/-- Memo hits and all completed or failed misses retain derived private closedness. -/
theorem call_closed (p h budget : Nat) (memo : Memo) (query : ConcreteNode) (before : ConcretePhysical)
    (ready : Ready before) (available : Available before.heap query) :
    Invariant (SourceCurrentConjunctionSharedWorker.call p h budget memo query before).state := by
  cases hit : memo query.referenceOf with
  | some saved =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.call_state, hit] using
        SourceCurrentConjunctionSharedWorklistClosed.initial_closed budget query before
  | none =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.call_state, hit] using
        decision_closed p h budget query before ready available

end MicroCFTA.SourceCurrentConjunctionSharedWorkerClosed
