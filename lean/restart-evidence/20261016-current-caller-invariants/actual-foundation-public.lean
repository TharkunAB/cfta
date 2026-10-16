import MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity
import MicroCFTA.SourceCurrentConjunctionRequiredActual

#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.read
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.read
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.exposures
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.exposures
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.projections
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.projections
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.classes
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.classes
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.requirements
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.requirements
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.tuple
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.tuple
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.tuples
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.tuples
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.rows
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.rows
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.run
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.run
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.decision
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.decision
#print axioms MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.call
#check @MicroCFTA.SourceCurrentAllocatedConjunctionReadValidity.call
#print axioms MicroCFTA.SourceCurrentConjunctionRequiredActual.required_unique
#check @MicroCFTA.SourceCurrentConjunctionRequiredActual.required_unique
#print axioms MicroCFTA.SourceCurrentConjunctionRequiredActual.verified
#check @MicroCFTA.SourceCurrentConjunctionRequiredActual.verified

namespace MicroCFTA.CurrentActualFoundationProbe
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionGlobalMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

example (heap : State Symbol Guard) (memos : Memos) (semantic : SemanticReady heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap heap) (valid : EndpointMemoGateTrace.Valid heap memos) :
    EndpointMemoGateTrace.Valid heap memos := by
  have actual : SourceCurrentConjunctionCompletionReads.Exposures [] heap [] heap := .nil
  have calls : ExposuresReads actual memos memos := .nil
  exact (SourceCurrentAllocatedConjunctionReadValidity.exposures calls semantic costs
    (by intro value member; cases member) valid).1

example (heap : State Symbol Guard) (memos : Memos) (semantic : SemanticReady heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap heap) (valid : EndpointMemoGateTrace.Valid heap memos) :
    EndpointMemoGateTrace.Valid heap memos := by
  have actual : SourceCurrentConjunctionCompletionReads.Projections [] heap [] heap := .nil
  have calls : ProjectionsReads actual memos memos := .nil
  exact (SourceCurrentAllocatedConjunctionReadValidity.projections calls semantic costs
    (by intro job member; cases member) valid).1

example (before : Physical) (memos : Memos) (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (valid : EndpointMemoGateTrace.Valid before.heap memos) :
    EndpointMemoGateTrace.Valid before.heap memos ∧ Extends memos.unfolding memos.unfolding ∧ memos.query=memos.query := by
  have actual : SourceCurrentConjunctionWorklist.Run 4 [] [] before [] before := .done
  have calls : RunReads actual memos memos := .done
  exact SourceCurrentAllocatedConjunctionReadValidity.run calls ready
    (by intro nodes member; cases member) valid

example (before : Physical) (memos : Memos) (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (valid : EndpointMemoGateTrace.Valid before.heap memos) :
    EndpointMemoGateTrace.Valid before.heap memos := by
  have actual : SourceCurrentConjunctionWorklist.Run 4 [] [[.empty]] before [] before :=
    .empty rfl .done
  have calls : RunReads actual memos memos := .empty (impossible := rfl) .done
  exact (SourceCurrentAllocatedConjunctionReadValidity.run calls ready (by
    intro nodes member value included
    cases List.mem_singleton.mp member
    cases List.mem_singleton.mp included
    exact empty_available _) valid).1

example (before : Physical) (memos : Memos) (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (valid : EndpointMemoGateTrace.Valid before.heap memos) :
    EndpointMemoGateTrace.Valid before.heap memos := by
  have actual : SourceCurrentConjunctionWorklist.Run 0 [] [[]] before [] before :=
    .skip rfl rfl .done
  have calls : RunReads actual memos memos := .skip (nonempty := rfl) (skipped := rfl) .done
  exact (SourceCurrentAllocatedConjunctionReadValidity.run calls ready (by
    intro nodes member value included
    cases List.mem_singleton.mp member
    cases included) valid).1

example (budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo) (query original : Value Symbol Guard)
    (answer : Bool) (before : Physical) (memos : Memos)
    (found : memo query.referenceOf=some (original,answer))
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before) (available : Available before.heap query)
    (valid : EndpointMemoGateTrace.Valid before.heap memos) :
    EndpointMemoGateTrace.Valid before.heap memos :=
  (SourceCurrentAllocatedConjunctionReadValidity.call
    (CallReads.hit (budget := budget) (before := before) (memos := memos) found) ready available valid).1

example (budget : Nat) (memo : SourceCurrentEmptinessMemo.Memo) (query : Value Symbol Guard)
    (before : Physical) (memos : Memos) (absent : memo query.referenceOf=none)
    (opened : SourceCurrentConjunctionWorklist.closed query=false)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before) (available : Available before.heap query)
    (valid : EndpointMemoGateTrace.Valid before.heap memos) :
    EndpointMemoGateTrace.Valid before.heap memos ∧ Extends memos.unfolding memos.unfolding ∧ memos.query=memos.query := by
  have actual : SourceCurrentConjunctionMemo.Call budget memo query before false before
      (SourceCurrentEmptinessMemo.insert memo query false) := .miss absent (.open_input opened)
  have calls : CallReads actual memos memos := .miss (absent := absent) (.open_input opened)
  exact SourceCurrentAllocatedConjunctionReadValidity.call calls ready available valid

example (fuel readFuel : Nat) (paths : List SourceEqualityNeeded.Path) (values result : List (Value Symbol Guard))
    (before after : State Symbol Guard)
    (actual : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before=.done result after) :
    result=result ∧ after=after := SourceCurrentConjunctionRequiredActual.required_unique actual actual
end MicroCFTA.CurrentActualFoundationProbe
