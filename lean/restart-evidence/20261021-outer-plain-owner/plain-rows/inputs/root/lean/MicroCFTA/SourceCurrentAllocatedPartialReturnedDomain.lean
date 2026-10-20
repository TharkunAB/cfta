import MicroCFTA.SourceCurrentAllocatedPartialActiveOrder
import MicroCFTA.SourceEqualityPartialPlainRegion

/-!
# Structural returned-edge certificates for the current caller

A parent result keeps original children, erases their slots, or uses the
singleton Empty sentinel. Each case retains ordinary height bounds and
the Region of the returned children. The certificate follows the actual
stored request in the edge result table. It is separate from EdgeLaw.
This module proves cache lifecycle laws. It does not assume or prove
that every general constrained parent result has one of these shapes.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialReturnedDomain
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Regions" => SourceEqualityPartialPlainRegion.Children
local notation "Region" => SourceEqualityPartialPlainRegion.Region

/-- Parent construction retains original children, erased slots, or its singleton Empty sentinel. -/
def Shape (original result : Edge) : Prop :=
  result.children = original.children ∨
    result.children = EqualityLeafProjectionRuntimeEmpty.erase original.children ∨ result.children = [.empty]

/-- Original parent children give the first concrete result shape. -/
theorem Shape.original {original result : Edge} (same : result.children = original.children) : Shape original result :=
  Or.inl same

/-- Raw or checked rejection gives the source singleton Empty sentinel. -/
theorem Shape.sentinel {original result : Edge} (same : result.children = [.empty]) : Shape original result :=
  Or.inr (Or.inr same)

private theorem erased_regions (values : List Node) : Regions (EqualityLeafProjectionRuntimeEmpty.erase values) := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons .empty ih

private theorem region_member {values : List Node} (regions : Regions values) (value : Node)
    (member : value ∈ values) : Region value := by
  cases regions with
  | nil => cases member
  | cons first rest =>
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ first
      · exact region_member rest value later
termination_by values.length

/-- The three concrete parent shapes preserve the Region of every returned child. -/
theorem Shape.regions {original result : Edge} (shape : Shape original result)
    (regions : Regions original.children) : Regions result.children := by
  rcases shape with same | erased | sentinel
  · exact same ▸ regions
  · exact erased ▸ erased_regions original.children
  · exact sentinel ▸ (show Regions [.empty] from .cons .empty .nil)

/-- Every returned child retains its concrete structural Region. -/
theorem Shape.child_region {original result : Edge} (shape : Shape original result)
    (regions : Regions original.children) (child : Node) (member : child ∈ result.children) : Region child :=
  region_member (shape.regions regions) child member

/-- All parent shapes derive the original edge-height bound without an arity assertion. -/
theorem Shape.height {original result : Edge} (shape : Shape original result) :
    MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgeHeight original := by
  rcases shape with same | erased | sentinel
  · exact SourceCurrentAllocatedPartialActiveOrder.original_or_erased_bound original result (Or.inl same)
  · exact SourceCurrentAllocatedPartialActiveOrder.original_or_erased_bound original result (Or.inr erased)
  · have zero : MergedOrdinaryHeight.edgeHeight result = 0 := by
      cases result with
      | mk entry children =>
          change children = [.empty] at sentinel
          subst children
          rfl
    rw [zero]
    exact Nat.zero_le _

/-- Every completed edge cell retains the child domain of its actual stored owner. -/
def Stored (state : Caller width) : Prop :=
  ∀ handle owner result, state.edgeResults.cells handle = some ⟨owner, .returned result⟩ → Shape owner.value result

/-- Empty outer result tables derive the returned domain over arbitrary lower warm state. -/
theorem initial (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    Stored (SourceCurrentAllocatedPartialState.initial checked merge fourth) := by
  intro handle owner result absent
  cases absent

/-- Checked advancement retains the exact complete edge result table. -/
theorem Stored.advance {before : Caller width} (stored : Stored before)
    (checked : SourceEqualityNativeDemand.State width) (fourth : SourceCurrentEmptinessMemo.Memo)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) :
    Stored (SourceCurrentAllocatedPartialState.advance before checked fourth merge) := stored

/-- Node publication changes no edge result cell. -/
theorem Stored.beginNode {before : Caller width} (stored : Stored before) (request : NodeRequest) :
    Stored (SourceCurrentAllocatedPartialState.beginNode request before).2.2 := stored

/-- Node completion changes no edge result cell. -/
theorem Stored.finishNode {before : Caller width} (stored : Stored before) (handle : Nat) (result : Node) :
    Stored (SourceCurrentAllocatedPartialState.finishNode handle result before) := stored

private theorem lookup_returned_before [DecidableEq Key] (key : Key) (request : Request)
    (memo : FlatMemoThunk.State Key Request Result) :
    FlatMemoThunk.Returned (FlatMemoThunk.lookupOrInsert key request memo).2 memo := by
  intro handle owner result returned
  cases found : memo.table key with
  | some existing => simpa only [FlatMemoThunk.lookupOrInsert, found] using returned
  | none =>
      by_cases same : handle = memo.next
      · subst handle
        simp [FlatMemoThunk.lookupOrInsert, found, put] at returned
      · simpa only [FlatMemoThunk.lookupOrInsert, found, put, ite_eq_right same] using returned

private theorem demand_returned_before (handle : Nat) (memo : FlatMemoThunk.State Key Request Result) :
    FlatMemoThunk.Returned (FlatMemoThunk.demand handle memo).2 memo := by
  intro other owner result returned
  cases found : memo.cells handle with
  | none => simpa only [FlatMemoThunk.demand, found] using returned
  | some cell =>
      cases cell with
      | mk original status =>
          cases status with
          | evaluating | returned value => simpa only [FlatMemoThunk.demand, found] using returned
          | suspended =>
              by_cases same : other = handle
              · subst other
                simp [FlatMemoThunk.demand, found, FlatMemoThunk.setStatus, put] at returned
              · simpa only [FlatMemoThunk.demand, found, FlatMemoThunk.setStatus, put, ite_eq_right same] using returned

/-- Edge publication and demand create no returned result or structural assumption. -/
theorem Stored.beginEdge {before : Caller width} (stored : Stored before) (request : EdgeRequest) :
    Stored (SourceCurrentAllocatedPartialState.beginEdge request before).2.2 := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  intro handle owner result returned
  exact stored handle owner result
    (lookup_returned_before request.key request before.edgeResults handle owner result
      (demand_returned_before published.1 published.2 handle owner result returned))

/-- Literal edge completion stores the certificate at its exact evaluating owner. -/
theorem Stored.finishEdge {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : EdgeRequest} (result : Edge)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩) (shape : Shape owner.value result) :
    Stored (SourceCurrentAllocatedPartialState.finishEdge handle result before) := by
  intro other original output returned
  by_cases same : other = handle
  · subst other
    have installed := finishEdge_returned handle owner result before running
    have equal := Option.some.inj (installed.symm.trans returned)
    cases equal
    exact shape
  · exact stored other original output (by
      change (FlatMemoThunk.finish handle result before.edgeResults).cells other = _ at returned
      simpa only [FlatMemoThunk.finish, running, FlatMemoThunk.setStatus, put, ite_eq_right same] using returned)

/-- The concrete returned domain derives the weaker height-only invariant. -/
theorem Stored.bounds {before : Caller width} (stored : Stored before) :
    SourceCurrentAllocatedPartialActiveOrder.ReturnedBounds before :=
  fun handle owner result returned => (stored handle owner result returned).height

/-- A stored returned edge supplies both Region membership and strict recursive rank descent. -/
theorem Stored.child {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : EdgeRequest} {result : Edge}
    (returned : before.edgeResults.cells handle = some ⟨owner, .returned result⟩)
    (regions : Regions owner.value.children) (inherited : SourceEqualityConstraintAllocation.Value)
    (child : Node) (member : child ∈ result.children) :
    Region child ∧ SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨inherited, child⟩ <
      SourceCurrentAllocatedPartialActiveOrder.edgeRank owner :=
  ⟨(stored handle owner result returned).child_region regions child member,
    SourceCurrentAllocatedPartialActiveOrder.returned_child_lt stored.bounds returned inherited member⟩

end MicroCFTA.SourceCurrentAllocatedPartialReturnedDomain
