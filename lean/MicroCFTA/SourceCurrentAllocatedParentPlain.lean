import MicroCFTA.SourceCurrentAllocatedLocalPlainRanges
import MicroCFTA.SourceCurrentAllocatedPartialReturnedDomain

/-!
# Current parent completion with empty effective own equalities

The live branch derives its range plan from the actual loaded field.
The local worker retains original children or erases their slots.
The checked constructor can also return the singleton Empty sentinel.
The same literal return has strict reads, full caller effects, and a
structural height bound. No whole-forest closedness is required.
-/
namespace MicroCFTA.SourceCurrentAllocatedParentPlain
open EqualityNormalize InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialReturnedDomain (Shape)
open SourceCurrentAllocatedParentWorkerCompletion (StableRun)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "edge" => SourceCurrentAllocatedParentWorker.edge
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Only a live original guard needs empty effective own equalities. -/
def Plain (request : Request) : Prop :=
  contradictory request.value.entry.key.constraint = false →
    SourceCompactGuards.sourceEqualities request.value.entry.key.constraint = some []

/-- Actual resident field readback derives the full reached parent range plan. -/
theorem resident_ranges
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : Request) (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value) (plain : Plain request) :
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before :=
  SourceCurrentAllocatedLocalPlainRanges.resident_ranges budget request before initial.ready resident inheritedReady plain

private theorem parent_shape
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {budget : Nat} {request : Request} {before : Caller width}
    {loaded : Allocated} {result : EdgeValue Symbol Guard} {after : Checked width}
    {savedFourth : Fourth} {saved : Memo} {memos final : Memos}
    {actual : SourceCurrentAllocatedParentEdge.Edge budget request.value.entry.key.symbol
      request.value.entry.key.constraint loaded request.inherited request.value.children before.checked
      before.fourth before.merge result after savedFourth saved}
    (reads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos final)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value) (plain : Plain request)
    (field : contradictory request.value.entry.key.constraint = false →
      SourceEqualityConstraintFieldLookup.load request.value.entry.key.constraint before.checked.operations.constraints =
        .ok (some loaded)) : Shape request.value result := by
  cases reads with
  | rejected =>
      exact Shape.sentinel (SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory
        request.value.entry.key.symbol before.checked initial.ready initial.admitted).children
  | live localReads =>
      rename_i children middle test built reduction
      have cached := (initial.ready.good.fields request.value.entry.key request.value resident).1
      have found := field test
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready request.value.entry.key.constraint
        before.checked.operations.constraints initial.ready.good.operations.constraints cached loaded found
      have ownEmpty := SourceCurrentAllocatedLocalPlain.of_readback loadedReady.2 (plain test)
      obtain ⟨g, s, r, e, p, h, m, c, n, stable⟩ :=
        SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete reduction
      have completed := stable g s r e p h m c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      have localShape := (SourceCurrentAllocatedLocalPlain.done_shape g s r e p h m c n budget loaded
        request.inherited request.value.children before.checked middle before.fourth savedFourth before.merge saved children
        initial.ready.good.operations loadedReady.1 inheritedReady ownEmpty completed).2.2.2
      have available := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ request.value resident
      have ranges := SourceCurrentAllocatedLocalPlainRanges.ranges budget loaded request.inherited request.value.children
        before.checked before.fourth before.merge initial.ready.good.operations loadedReady.1 inheritedReady ownEmpty
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory
        request.value.entry.key.constraint localReads initial.ready initial.admitted cached found inheritedReady available
        initial.correct initial.stored initial.covered
        (SourceCurrentAllocatedLocalReductionActual.ranges_of_finite ranges) initial.globals
      have storedReady := loadedReady.1.grows receipt.effects.grows.constraint_growth
      have currentField : SourceCurrentConjunctionEquality.FieldAvailable middle.operations
          (SourceEqualityConjoinAllocation.readback loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations
          request.value.entry.key.constraint from ⟨cached, loaded, found⟩).grows receipt.effects.grows
      obtain ⟨chosen, returned, constructor⟩ := SourceCurrentAllocatedMkEdge.finite formulas solver next
        request.value.entry.key.symbol loaded children middle receipt.ready receipt.admitted storedReady currentField
        receipt.available
      have same := Prod.mk.inj (constructor.actual.symm.trans built)
      have sameValue := Except.ok.inj same.1
      cases sameValue
      cases same.2
      cases keep : SourceEqualityMkEdgeAllocation.accepted (SourceEqualityConjoinAllocation.readback loaded) children.length with
      | false => exact Shape.sentinel (by simpa only [keep, Bool.false_eq_true, ↓reduceIte] using constructor.children)
      | true =>
          have sameChildren : result.children = children := by
            simpa only [keep, ↓reduceIte] using constructor.children
          rcases localShape with original | erased
          · exact Shape.original (sameChildren.trans original)
          · exact Or.inr (Or.inl (sameChildren.trans erased))

/-- Initial caller facts construct the same stable parent return and its structural domain. -/
theorem finite
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    (budget : Nat) (request : Request) (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value) (plain : Plain request) :
    ∃ result after savedFourth saved next final,
      StableRun (fun g s r e p h m c n => edge g s r e p h m c n budget request.value.entry.key.symbol
        request.value.entry.key.constraint request.inherited request.value.children
        before.checked before.fourth before.merge) result after savedFourth saved ∧
      ∃ actual : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result
          (SourceCurrentAllocatedPartialState.advance before after savedFourth saved),
        SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver actual memos final ∧
        SourceCurrentAllocatedPartialEdgeCall.Receipt formulas solver next request before result
          (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final ∧
        Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after savedFourth saved) final ∧
        Shape request.value result ∧ MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgeHeight request.value := by
  obtain ⟨result, after, savedFourth, saved, next, final, stable, actual, reads, receipt, post⟩ :=
    SourceCurrentAllocatedParentWorkerActual.resident_finite formulas solver budget request initial inheritedReady resident
      (resident_ranges formulas solver budget request initial inheritedReady resident plain)
  have shape : Shape request.value result := by
    cases reads with
    | parent parentReads =>
        exact parent_shape formulas solver parentReads initial inheritedReady resident plain (by assumption)
  exact ⟨result, after, savedFourth, saved, next, final, stable, actual, reads, receipt, post, shape, shape.height⟩

/-- Every supplied successful bound retains the same three-way child shape and height. -/
theorem done_shape
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {before : Caller width} {memos : Memos}
    {budget g s r e p h m c n : Nat} {request : Request} {result : EdgeValue Symbol Guard}
    {after : Checked width} {savedFourth : Fourth} {saved : Memo}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value) (plain : Plain request)
    (done : edge g s r e p h m c n budget request.value.entry.key.symbol request.value.entry.key.constraint
      request.inherited request.value.children before.checked before.fourth before.merge = .done result after savedFourth saved) :
    Shape request.value result ∧ MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgeHeight request.value := by
  obtain ⟨chosen, reached, fourth, memo, next, final, ⟨G, S, R, E, P, H, M, C, N, stable⟩,
    actual, reads, receipt, post, shape, bound⟩ := finite formulas solver budget request initial inheritedReady resident plain
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SourceCurrentAllocatedParentWorkerStability.edge_done_unique
    (stable G S R E P H M C N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)) done
  exact ⟨shape, bound⟩

end MicroCFTA.SourceCurrentAllocatedParentPlain
