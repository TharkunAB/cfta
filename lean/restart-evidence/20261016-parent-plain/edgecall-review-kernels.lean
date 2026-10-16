import MicroCFTA.SourceCurrentAllocatedPartialPlainEdgeCall
import MicroCFTA.SourceCurrentAllocatedPartialActiveFrames
import MicroCFTA.SourceCurrentAllocatedPartialWorkerStability

namespace MicroCFTA.PlainEdgeCallReview
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialReturnedDomain (Shape Stored)
open SourceCurrentAllocatedPartialActiveOrder
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Regions" => SourceEqualityPartialPlainRegion.Children
local notation "Region" => SourceEqualityPartialPlainRegion.Region
variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem node_table_exact {width budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (actual : EdgeCall budget request before result after) : after.nodeResults = before.nodeResults := by
  cases actual with
  | hit started => simpa only [started] using (beginEdge_components request before).2.2.2
  | evaluate started body =>
      have kept := (beginEdge_components request before).2.2.2
      rw [started] at kept
      cases body
      exact kept

-- No literal success or body is supplied. The created call restores active bounds and the next child domain.
theorem finite_child_domain {width : Nat} {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (plain : SourceCurrentAllocatedParentPlain.Plain request) (stored : Stored before)
    (active : ActiveAbove (edgeRank request) before) (regions : Regions request.value.children) :
    ∃ result after next final,
      SourceCurrentAllocatedPartialWorkerCompletion.StableRun
        (fun f g s r e p h m c n => SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before)
        result after ∧
      ∃ actual : EdgeCall budget request before result after,
        EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
        Post formulas solver next before after final ∧ Stored after ∧
        after.nodeResults = before.nodeResults ∧
        FlatMemoThunk.Returned before.edgeResults after.edgeResults ∧ ActiveAbove (edgeRank request) after ∧
        ∀ inherited child, child ∈ result.children → Region child ∧ nodeRank ⟨inherited, child⟩ < edgeRank request := by
  obtain ⟨result, after, next, final, stable, actual, reads, checks, post, _available, saved, shape, _law⟩ :=
    SourceCurrentAllocatedPartialPlainEdgeCall.finite formulas solver budget request initial inherited resident plain stored active
  refine ⟨result, after, next, final, stable, actual, reads, checks, post, saved, node_table_exact actual,
    (SourceCurrentAllocatedPartialFrames.edge_call actual
      (SourceCurrentAllocatedPartialFrames.Protocol.of_valid initial.sound.valid)).edge_returned,
    (SourceCurrentAllocatedPartialActiveFrames.edge_call actual).activeExcept active, ?_⟩
  intro inherited child member
  refine ⟨shape.child_region regions child member, ?_⟩
  have smaller := child_lt_edge request.inherited inherited result child member
  have bounded := shape.height
  simp only [edgeRank] at smaller ⊢
  omega

-- The second call is constructed at the first computed inventory and warm full caller without a new invariant.
theorem two_queries {width : Nat} {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : EdgeRequest) (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (plain : SourceCurrentAllocatedParentPlain.Plain request) (stored : Stored before)
    (active : ActiveAbove (edgeRank request) before) :
    ∃ result middle firstInventory firstMemos output after next final,
      (∃ actual : EdgeCall budget request before result middle,
        EdgeCallReads formulas solver actual memos firstMemos) ∧
      (∃ actual : EdgeCall budget request middle output after,
        EdgeCallReads formulas solver actual firstMemos final) ∧
      Post formulas solver firstInventory before middle firstMemos ∧
      Post formulas solver next middle after final ∧ Post formulas solver next before after final ∧ Stored after := by
  obtain ⟨result, middle, firstInventory, firstMemos, _stable, first, firstReads, _checks, firstPost, _available,
    firstStored, _shape, _law⟩ := SourceCurrentAllocatedPartialPlainEdgeCall.finite formulas solver budget request
      initial inherited resident plain stored active
  have nextInherited := inherited.grows firstPost.effects.grows.constraint_growth
  have nextResident := edge_grows _ _ firstPost.effects.keeps.growth request.value resident
  have nextActive := (SourceCurrentAllocatedPartialActiveFrames.edge_call first).activeExcept active
  obtain ⟨output, after, next, final, _stable, second, secondReads, _checks, lastPost, _available, lastStored, _shape, _law⟩ :=
    SourceCurrentAllocatedPartialPlainEdgeCall.finite formulas solver budget request firstPost.context nextInherited
      nextResident plain firstStored nextActive
  exact ⟨result, middle, firstInventory, firstMemos, output, after, next, final, ⟨first, firstReads⟩,
    ⟨second, secondReads⟩, firstPost, lastPost, firstPost.trans lastPost, lastStored⟩

-- A real warm hit at zero bounds aligns the constructed endpoint to the identical whole caller.
theorem warm_zero_return {width : Nat} {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request owner : EdgeRequest) (handle : Nat) (result : Edge)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (plain : SourceCurrentAllocatedParentPlain.Plain request) (stored : Stored before)
    (active : ActiveAbove (edgeRank request) before)
    (published : before.edgeResults.table request.key = some handle)
    (returned : before.edgeResults.cells handle = some ⟨owner, .returned result⟩) :
    SourceCurrentAllocatedPartialWorker.edgeCall 0 0 0 0 0 0 0 0 0 0 budget request before = .done result before ∧
      ∃ next final, ∃ actual : EdgeCall budget request before result before,
        EdgeCallReads formulas solver actual memos final ∧ Post formulas solver next before before final ∧
        Stored before ∧ Shape request.value result ∧ SourceCurrentAllocatedPartialMemoSound.EdgeLaw formulas solver request result := by
  have warm := SourceCurrentAllocatedPartialWorker.edgeCall_ready 0 0 0 0 0 0 0 0 0 0 budget request before before handle result
    (beginEdge_ready request owner before handle result published returned)
  obtain ⟨chosen, after, next, final, ⟨f, g, s, r, e, p, h, m, c, n, stable⟩, actual, reads, _checks, post,
    _available, kept, shape, law⟩ := SourceCurrentAllocatedPartialPlainEdgeCall.finite formulas solver budget request
      initial inherited resident plain stored active
  have one := stable f g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedPartialWorkerStability.edgeCall_done_unique one warm
  exact ⟨warm, next, final, actual, reads, post, kept, shape, law⟩

-- An actual evaluating alias cannot also satisfy the required independent active bound.
omit [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node] in
theorem busy_excluded {width : Nat} (before : Caller width) (request owner : EdgeRequest) (handle : Nat)
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (published : before.edgeResults.table request.key = some handle)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩) :
    ¬ ActiveAbove (edgeRank request) before := by
  intro active
  have safe := edge_begin_safe formulas solver request before sound coherent resident active
  have blocked := beginEdge_busy request owner before handle published running
  rcases safe with ⟨value, ready⟩ | ⟨original, evaluates⟩
  · rw [blocked] at ready
    cases ready
  · rw [blocked] at evaluates
    cases evaluates

end MicroCFTA.PlainEdgeCallReview
#print axioms MicroCFTA.PlainEdgeCallReview.finite_child_domain
#print axioms MicroCFTA.PlainEdgeCallReview.two_queries
#print axioms MicroCFTA.PlainEdgeCallReview.warm_zero_return
#print axioms MicroCFTA.PlainEdgeCallReview.busy_excluded
