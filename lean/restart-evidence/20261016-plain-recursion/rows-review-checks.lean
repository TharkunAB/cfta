import MicroCFTA.SourceCurrentAllocatedPartialPlainNode

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainRows.descendants
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainRows.descendants
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainRows.rows
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainRows.rows
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainRecursionDefs.NodeResult
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainRecursionDefs.NodeResult
#print axioms MicroCFTA.SourceCurrentAllocatedPartialPlainRecursionDefs.Below
#check @MicroCFTA.SourceCurrentAllocatedPartialPlainRecursionDefs.Below

namespace PlainRowsReviewChecks
open MicroCFTA Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Stored Shape)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank edgeRank)
open SourceCurrentAllocatedPartialPlainRecursionDefs (Below)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

private theorem below_from_proved_node_completion
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget rank : Nat) : Below (width := width) formulas solver budget rank := by
  intro inventory before memos request _smaller initial inheritedReady available region stored active
  obtain ⟨result, after, next, final, _stable, actual, reads, checks, post, output, retained, law⟩ :=
    SourceCurrentAllocatedPartialPlainNode.finite formulas solver budget request initial inheritedReady available
      region stored active
  exact ⟨result, after, next, final, actual, reads, checks, post, output, retained, law⟩

theorem descendants_without_completion_callback
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (inherited : EqValue) (edge : Edge)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : EdgeResident before.checked.native.machine.heap edge)
    (regions : SourceEqualityPartialPlainRegion.Children edge.children)
    (stored : Stored before) (active : ActiveAbove (edgeRank ⟨inherited, edge⟩) before) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.descendants f g s r e p h m c n
          budget inherited edge before) result after ∧
      ∃ actual : Descendants budget inherited edge before result after,
        DescendantsReads formulas solver actual memos final ∧ Checks (descendantsTrace actual) ∧
        Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
        Stored after ∧ SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver ⟨inherited, edge⟩ result ∧
        ActiveAbove (edgeRank ⟨inherited, edge⟩) after := by
  have smaller : ∀ value ∈ edge.children, nodeRank ⟨inherited, value⟩ < edgeRank ⟨inherited, edge⟩ + 1 := by
    intro value member
    exact Nat.lt_trans (SourceCurrentAllocatedPartialActiveOrder.child_lt_edge inherited inherited edge value member)
      (Nat.lt_succ_self _)
  obtain ⟨result, after, next, final, actual, reads, checks, post, residentOut, storedOut⟩ :=
    SourceCurrentAllocatedPartialPlainRows.descendants formulas solver budget (edgeRank ⟨inherited, edge⟩ + 1)
      inherited edge initial inheritedReady resident regions smaller stored active
      (below_from_proved_node_completion formulas solver budget _)
  obtain ⟨_, _, _, law⟩ := SourceCurrentAllocatedPartialActual.descendants formulas solver reads inventory
    checks initial inheritedReady resident
  exact ⟨result, after, next, final, SourceCurrentAllocatedPartialWorkerCompletion.descendants_complete actual,
    actual, reads, checks, post, residentOut, storedOut, law,
    (SourceCurrentAllocatedPartialActiveFrames.descendants actual).activeExcept active⟩

theorem rows_without_completion_callback
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget rank : Nat) (inherited : EqValue) (edges : List Edge)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap edges)
    (regions : SourceEqualityPartialPlainRegion.Rows edges)
    (smaller : ∀ edge ∈ edges, edgeRank ⟨inherited, edge⟩ < rank)
    (stored : Stored before) (active : ActiveAbove (rank - 1) before) :
    ∃ results after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.rows f g s r e p h m c n
          budget inherited edges before) results after ∧
      ∃ actual : Rows budget inherited edges before results after,
        RowsReads formulas solver actual memos final ∧ Checks (rowsTrace actual) ∧
        Post formulas solver next before after final ∧ Edges after.checked.native.machine.heap results ∧
        Stored after ∧ SourceCurrentAllocatedPartialForestLanguage.RowsLaw formulas solver actual ∧
        results.length = edges.length ∧ ActiveAbove (rank - 1) after := by
  obtain ⟨results, after, next, final, actual, reads, checks, post, residentOut, storedOut⟩ :=
    SourceCurrentAllocatedPartialPlainRows.rows formulas solver budget rank inherited edges initial inheritedReady
      resident regions smaller stored active (below_from_proved_node_completion formulas solver budget rank)
  obtain ⟨_, _, _, law⟩ := SourceCurrentAllocatedPartialActual.rows formulas solver reads inventory
    checks initial inheritedReady resident
  exact ⟨results, after, next, final, SourceCurrentAllocatedPartialWorkerCompletion.rows_complete actual,
    actual, reads, checks, post, residentOut, storedOut, law, actual.length,
    (SourceCurrentAllocatedPartialActiveFrames.rows actual).activeExcept active⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
theorem returned_parent_shape_preserves_region_and_rank
    (original returned : Edge) (inherited : EqValue) (shape : Shape original returned)
    (regions : SourceEqualityPartialPlainRegion.Children original.children) :
    ∀ child ∈ returned.children, SourceEqualityPartialPlainRegion.Region child ∧
      nodeRank ⟨inherited, child⟩ < edgeRank ⟨inherited, original⟩ := by
  intro child member
  have smaller := SourceCurrentAllocatedPartialActiveOrder.child_lt_edge inherited inherited returned child member
  have height := shape.height
  refine ⟨shape.child_region regions child member, ?_⟩
  simp only [SourceCurrentAllocatedPartialActiveOrder.edgeRank] at smaller ⊢
  omega

theorem empty_rows_construct_exact_return_at_all_bounds
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (inherited : EqValue) (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (stored : Stored before) (active : ActiveAbove 0 before) :
    ∃ next, Post formulas solver next before before memos ∧ Stored before ∧
      ∀ f g s r e p h m c n, SourceCurrentAllocatedPartialWorker.rows f g s r e p h m c n
        budget inherited [] before = .done [] before := by
  have smaller : ∀ edge ∈ ([] : List Edge), edgeRank ⟨inherited, edge⟩ < 0 := by
    intro edge absent
    cases absent
  obtain ⟨results, after, next, final, _stable, actual, reads, _checks, post, _resident, storedOut, _law, _length, _active⟩ :=
    rows_without_completion_callback formulas solver budget 0 inherited [] initial inheritedReady
      (fun _ absent => nomatch absent) .nil smaller stored active
  cases actual
  cases reads
  refine ⟨next, post, storedOut, ?_⟩
  intro f g s r e p h m c n
  simp only [SourceCurrentAllocatedPartialWorker.rows]

end PlainRowsReviewChecks

#print axioms PlainRowsReviewChecks.descendants_without_completion_callback
#check @PlainRowsReviewChecks.descendants_without_completion_callback
#print axioms PlainRowsReviewChecks.rows_without_completion_callback
#check @PlainRowsReviewChecks.rows_without_completion_callback
#print axioms PlainRowsReviewChecks.returned_parent_shape_preserves_region_and_rank
#check @PlainRowsReviewChecks.returned_parent_shape_preserves_region_and_rank
#print axioms PlainRowsReviewChecks.empty_rows_construct_exact_return_at_all_bounds
#check @PlainRowsReviewChecks.empty_rows_construct_exact_return_at_all_bounds
