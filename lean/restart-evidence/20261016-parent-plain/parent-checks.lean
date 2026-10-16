import MicroCFTA.SourceCurrentAllocatedParentPlain

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedParentPlain.Plain
#check @MicroCFTA.SourceCurrentAllocatedParentPlain.Plain
#print axioms MicroCFTA.SourceCurrentAllocatedParentPlain.resident_ranges
#check @MicroCFTA.SourceCurrentAllocatedParentPlain.resident_ranges
#print axioms MicroCFTA.SourceCurrentAllocatedParentPlain.finite
#check @MicroCFTA.SourceCurrentAllocatedParentPlain.finite
#print axioms MicroCFTA.SourceCurrentAllocatedParentPlain.done_shape
#check @MicroCFTA.SourceCurrentAllocatedParentPlain.done_shape

namespace ParentPlainChecks
open MicroCFTA
open EqualityNormalize InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialReturnedDomain (Shape Stored)
open SourceCurrentAllocatedParentPlain
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "edge" => SourceCurrentAllocatedParentWorker.edge
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "Regions" => SourceEqualityPartialPlainRegion.Children
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)] {width : Nat}

theorem returned_regions
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    {budget g s r e p h m c n : Nat} {request : Request} {result : EdgeValue Symbol Guard}
    {after : Checked width} {savedFourth : Fourth} {saved : Memo}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value) (plain : Plain request)
    (regions : Regions request.value.children)
    (done : edge g s r e p h m c n budget request.value.entry.key.symbol request.value.entry.key.constraint
      request.inherited request.value.children before.checked before.fourth before.merge = .done result after savedFourth saved) :
    Regions result.children :=
  ((done_shape formulas solver initial inheritedReady resident plain done).1).regions regions

theorem returned_child_rank
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    {budget g s r e p h m c n : Nat} {request : Request} {result : EdgeValue Symbol Guard}
    {after : Checked width} {savedFourth : Fourth} {saved : Memo}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value) (plain : Plain request)
    (done : edge g s r e p h m c n budget request.value.entry.key.symbol request.value.entry.key.constraint
      request.inherited request.value.children before.checked before.fourth before.merge = .done result after savedFourth saved)
    (inherited : SourceEqualityConstraintAllocation.Value) (child : Value Symbol Guard) (member : child ∈ result.children) :
    SourceCurrentAllocatedPartialActiveOrder.nodeRank ⟨inherited, child⟩ <
      SourceCurrentAllocatedPartialActiveOrder.edgeRank request := by
  have small := SourceCurrentAllocatedPartialActiveOrder.child_lt_edge request.inherited inherited result child member
  have bound := (done_shape formulas solver initial inheritedReady resident plain done).2
  simp only [SourceCurrentAllocatedPartialActiveOrder.edgeRank] at small ⊢
  omega

theorem consecutive_parents
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : Request) (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value) (plain : Plain request) :
    ∃ first middle firstFourth firstMemo result after savedFourth saved next final,
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => edge g s r e p h m c n budget request.value.entry.key.symbol
          request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge)
        first middle firstFourth firstMemo ∧
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => edge g s r e p h m c n budget request.value.entry.key.symbol
          request.value.entry.key.constraint request.inherited request.value.children middle firstFourth firstMemo)
        result after savedFourth saved ∧
      Post formulas solver next before (advance before after savedFourth saved) final ∧
      Shape request.value first ∧ Shape request.value result := by
  obtain ⟨first, middle, firstFourth, firstMemo, inventory₁, memos₁, firstStable,
    firstActual, firstReads, firstReceipt, firstPost, firstShape, _⟩ :=
    finite formulas solver budget request initial inheritedReady resident plain
  have inherited₂ := inheritedReady.grows firstPost.effects.grows.constraint_growth
  have resident₂ := InternedEdgeResidency.edge_grows _ _ firstPost.effects.keeps.growth request.value resident
  obtain ⟨result, after, savedFourth, saved, next, final, lastStable,
    lastActual, lastReads, lastReceipt, lastPost, lastShape, _⟩ :=
    finite formulas solver budget request firstPost.context inherited₂ resident₂ plain
  exact ⟨first, middle, firstFourth, firstMemo, result, after, savedFourth, saved, next, final,
    firstStable, lastStable, firstPost.trans lastPost, firstShape, lastShape⟩

theorem stored_owner_finish
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : Request) (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value) (plain : Plain request)
    (stored : Stored before) (handle : Nat)
    (running : before.edgeResults.cells handle = some ⟨request, .evaluating⟩) :
    ∃ result after savedFourth saved next final,
      Post formulas solver next before (advance before after savedFourth saved) final ∧
      Stored (SourceCurrentAllocatedPartialState.finishEdge handle result (advance before after savedFourth saved)) ∧
      SourceCurrentAllocatedPartialActiveOrder.ReturnedBounds
        (SourceCurrentAllocatedPartialState.finishEdge handle result (advance before after savedFourth saved)) := by
  obtain ⟨result, after, savedFourth, saved, next, final, stable, actual, reads, receipt, post, shape, bound⟩ :=
    finite formulas solver budget request initial inheritedReady resident plain
  have retained := stored.advance after savedFourth saved
  have finished := retained.finishEdge result running shape
  exact ⟨result, after, savedFourth, saved, next, final, post, finished, finished.bounds⟩

theorem raw_reject_needs_no_field
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (g s r e p h m c n budget : Nat) (request : Request)
    (initial : Context formulas solver inventory before memos)
    (test : SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = true) :
    let rejected := SourceCurrentAllocatedMkEdge.reject request.value.entry.key.symbol before.checked
    edge g s r e p h m c n budget request.value.entry.key.symbol request.value.entry.key.constraint
      request.inherited request.value.children before.checked before.fourth before.merge =
        .done rejected.1 rejected.2 before.fourth before.merge ∧
      Shape request.value rejected.1 ∧ MergedOrdinaryHeight.edgeHeight rejected.1 ≤ MergedOrdinaryHeight.edgeHeight request.value := by
  have constructor := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory
    request.value.entry.key.symbol before.checked initial.ready initial.admitted
  have shape : Shape request.value (SourceCurrentAllocatedMkEdge.reject request.value.entry.key.symbol before.checked).1 :=
    Shape.sentinel constructor.children
  exact ⟨SourceCurrentAllocatedParentWorker.edge_rejected g s r e p h m c n budget
    request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
    before.checked before.fourth before.merge test, shape, shape.height⟩

theorem nullary_result
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    {budget g s r e p h m c n : Nat} {request : Request} {result : EdgeValue Symbol Guard}
    {after : Checked width} {savedFourth : Fourth} {saved : Memo}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value) (plain : Plain request)
    (nullary : request.value.children = [])
    (done : edge g s r e p h m c n budget request.value.entry.key.symbol request.value.entry.key.constraint
      request.inherited request.value.children before.checked before.fourth before.merge = .done result after savedFourth saved) :
    (result.children = [] ∨ result.children = [.empty]) ∧ MergedOrdinaryHeight.edgeHeight result = 0 := by
  obtain ⟨shape, bound⟩ := done_shape formulas solver initial inheritedReady resident plain done
  have originalZero : MergedOrdinaryHeight.edgeHeight request.value = 0 := by
    cases original : request.value with
    | mk entry children =>
        rw [original] at nullary
        change children = [] at nullary
        subst children
        rfl
  refine ⟨?_, by omega⟩
  rcases shape with same | erased | sentinel
  · exact Or.inl (same.trans nullary)
  · exact Or.inl (by simpa only [nullary, EqualityLeafProjectionRuntimeEmpty.erase, List.map_nil] using erased)
  · exact Or.inr sentinel

theorem open_reference_child
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : Request) (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value) (plain : Plain request)
    (name : InternedBinderProtocol.Reference) (opaqueChild : request.value.children = [.reference name]) :
    ∃ result after savedFourth saved next final,
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => edge g s r e p h m c n budget request.value.entry.key.symbol
          request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge)
        result after savedFourth saved ∧
      Post formulas solver next before (advance before after savedFourth saved) final ∧
      (result.children = [.reference name] ∨ result.children = [.empty]) := by
  obtain ⟨result, after, savedFourth, saved, next, final, stable, actual, reads, receipt, post, shape, bound⟩ :=
    finite formulas solver budget request initial inheritedReady resident plain
  refine ⟨result, after, savedFourth, saved, next, final, stable, post, ?_⟩
  rcases shape with same | erased | sentinel
  · exact Or.inl (same.trans opaqueChild)
  · exact Or.inr (by simpa only [opaqueChild, EqualityLeafProjectionRuntimeEmpty.erase, List.map_cons, List.map_nil] using erased)
  · exact Or.inr sentinel

end ParentPlainChecks

#print axioms ParentPlainChecks.returned_regions
#check @ParentPlainChecks.returned_regions
#print axioms ParentPlainChecks.returned_child_rank
#check @ParentPlainChecks.returned_child_rank
#print axioms ParentPlainChecks.consecutive_parents
#check @ParentPlainChecks.consecutive_parents
#print axioms ParentPlainChecks.stored_owner_finish
#check @ParentPlainChecks.stored_owner_finish
#print axioms ParentPlainChecks.raw_reject_needs_no_field
#check @ParentPlainChecks.raw_reject_needs_no_field
#print axioms ParentPlainChecks.nullary_result
#check @ParentPlainChecks.nullary_result
#print axioms ParentPlainChecks.open_reference_child
#check @ParentPlainChecks.open_reference_child
