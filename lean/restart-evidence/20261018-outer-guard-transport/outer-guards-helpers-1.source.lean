import MicroCFTA.SourceCurrentOuterPrefixInvariants
import MicroCFTA.SourceCurrentNativeGuardHeapReturns

/-!
# Causal guard profiles through actual outer calls and prefixes

Initial physical facts and actual earlier returns supply each intermediate
state. The guard predicate can be arbitrary. Successful calls and unfinished
prefixes retain the stored Mu body-to-probe profile law. This law does not
restrict every raw edge guard or prove recursive completion.
-/
namespace MicroCFTA.SourceCurrentOuterGuardHeapReturns
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterPrefixInvariants (Good NodeReady EdgeReady Inputs)
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Heap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
variable {width : Nat}

private theorem demand_valid (handle : Nat) (state : FlatMemoThunk.State Key Request Result)
    (keyOf : Request → Key → Prop) (property : FlatMemoThunk.Cell Request Result → Prop)
    (valid : FlatMemoThunk.Valid keyOf property state)
    (started : ∀ request, property ⟨request,.suspended⟩ → property ⟨request,.evaluating⟩) :
    FlatMemoThunk.Valid keyOf property (FlatMemoThunk.demand handle state).2 := by
  cases found : state.cells handle with
  | none => simpa only [FlatMemoThunk.demand,found] using valid
  | some cell =>
    cases cell with
    | mk request status =>
      cases status with
      | evaluating | returned value => simpa only [FlatMemoThunk.demand,found] using valid
      | suspended =>
        simp only [FlatMemoThunk.demand,found]
        exact FlatMemoThunk.setStatus_valid _ _ _ _ _ valid _ found (started request (valid.checked _ _ found))

private theorem begin_good (request : EdgeRequest) {before : Caller width}
    (good : Good before) (ready : EdgeReady before request) : Good (beginEdge request before).2.2 := by
  refine ⟨good.checked,good.stored,good.probes,good.nodes,?_⟩
  apply demand_valid
  · exact FlatMemoThunk.lookup_valid _ _ _ _ _ good.edges rfl
      ⟨ready,by intro value impossible; cases impossible⟩
  · intro owner supported
    exact ⟨supported.1,by intro value impossible; cases impossible⟩

private theorem bind_done (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (actual : first.bind next = .done value after) :
    ∃ result middle, first = .done result middle ∧ next result middle = .done value after := by
  cases first with
  | done result middle => exact ⟨result,middle,rfl,actual⟩
  | failed => cases actual

variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem raw_edge (annotation : Guard → Prop) (edge : Edge) (values : List Node) (before : Checked width)
    (guards : Heap annotation before.native.machine.heap) :
    Heap annotation (SourceCurrentAllocatedRawRebuild.edge edge values before).2.native.machine.heap := by
  exact guards

private theorem raw_node (annotation : Guard → Prop) (original : Node) (oldRows newRows : List Edge)
    (before : Checked width) (guards : Heap annotation before.native.machine.heap) :
    Heap annotation (SourceCurrentAllocatedRawRebuild.modify original oldRows newRows before).2.native.machine.heap := by
  unfold SourceCurrentAllocatedRawRebuild.modify SourceEqualityPartialNodeRebuild.modify
  split
  · exact guards
  · exact SourceCurrentConstrainedCapGuardHeap.preserve annotation _ _ guards
      (InternedShallowHeap.makeNode_noNewMu newRows _)

end MicroCFTA.SourceCurrentOuterGuardHeapReturns
