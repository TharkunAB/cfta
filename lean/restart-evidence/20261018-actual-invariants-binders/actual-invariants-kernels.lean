import MicroCFTA.SourceCurrentNativeOperationInvariants
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceEqualityAnnotationConstruction
set_option linter.all true
set_option maxErrors 4
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 10000000
namespace MicroCFTA.ActualInvariantKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentNativeOperationInvariants (Good)
open InternedNestedConstruction (Syntax)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def top : Guard := SourceEqualityConstraintConstructors.top
private def active : Guard := ⟨some [[[0,0],[0,1]]],.top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("same",.top) top []]
private def productive : Syntax Symbol Guard := .binder false (.node [
  .mk ("same",.top) top [],.mk ("same",.top) top [.var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("same",.top) active [leaf,productive]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Node := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private theorem constructed : built = .done root heap := by cbv
private def first : Node := ((children root)[0]?).getD .empty
private def mu : Node := ((children root)[1]?).getD .empty
private def row : EdgeValue Symbol Guard := match root with
  | .node _ (edge :: _) _ _ => edge
  | _ => (run (makeEdge ("fallback",.top) top []) empty).1
private def machine : Machine Symbol Guard := ⟨heap,Cache.emptyState⟩
private def allocation := SourceEqualityConstraintAllocation.construct active.equalities Cache.emptyState
private def own : SourceEqualityConstraintAllocation.Value := match allocation.1 with | .ok value => value | _ => .contradiction
private def operations := SourceEqualityMkEdgeAllocation.emptyField (SourceEqualityConstraintMemoAllocation.initial allocation.2)
private def before : Checked 8 := ⟨initial 8 machine,operations⟩
private def domain := IntersectionEmptyDomain.emptyDomain
private def request : EdgeRequest Symbol Guard := ⟨domain,row,row⟩
private noncomputable def evaluated := execute 24 (.code (requestEdge domain row row)) before
private noncomputable def after := evaluated.state
private def selectedRequest : NodeRequest Symbol Guard := ⟨domain,mu,mu⟩
private noncomputable def dispatched := SourceEqualityConstraintMemoAllocation.descend own 0 after.operations
private noncomputable def final : Checked 8 := {after with operations := dispatched.2}

private theorem active_cached : SourceEqualityGuardReadback.Cached active.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0,0],[0,1]]] = .normalized [[[0,0],[0,1]]] := by cbv
  intro paths same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem allocated :
    SourceEqualityConstraintFieldLookup.load active allocation.2 = .ok (some ⟨own,.top⟩) ∧
    SourceEqualityConjoinAllocation.readback (⟨own,.top⟩ : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula) = active ∧
    SourceEqualityConstraintAllocation.Ready allocation.2 own ∧
    SourceEqualityPhysicalPayload.read active.equalities = .ok own.payload ∧ Cache.Valid allocation.2 :=
  SourceEqualityConstraintFieldLookup.load_of_construct active active_cached Cache.emptyState Cache.empty_valid
  own allocation.2 (show allocation = (.ok own,allocation.2) by cbv)
private theorem initial_good : Good before := by
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression root heap constructed
  have guarded : SourceEqualityAnnotationHeap.Heap (fun guard : Guard => guard = active ∨ guard = top) heap := by
    have checked := SourceEqualityAnnotationConstruction.build (fun guard : Guard => guard = active ∨ guard = top) expression
      (by simp [expression,leaf,productive,SourceEqualityAnnotationConstruction.Allowed,
        SourceEqualityAnnotationConstruction.EdgesAllowed,SourceEqualityAnnotationConstruction.ManyAllowed]) [] empty
      (SourceEqualityAnnotationHeap.empty_heap _)
    simpa only [built,heap] using checked
  have initialValid := SourceEqualityConstraintMemoAllocation.initial_valid allocation.2 allocated.2.2.2.2
  have emptyField := SourceCurrentConjunctionFieldAllocation.empty_field (Formula := FullSyntax.Formula)
    (SourceEqualityConstraintMemoAllocation.initial allocation.2) initialValid
  have ownField : SourceCurrentConjunctionEquality.FieldAvailable operations active :=
    (show SourceCurrentConjunctionEquality.FieldAvailable (SourceEqualityConstraintMemoAllocation.initial allocation.2) active from
      ⟨active_cached,⟨own,.top⟩,allocated.1⟩).grows emptyField.2.1
  apply SourceCurrentNativeOperationInvariants.initial machine operations
    ⟨semantic.ready.semantic.1.normal.facts,Cache.empty_valid⟩ semantic.ready emptyField.1
  intro key edge found
  rcases guarded key edge found with same | same
  · rw [same]; exact ownField
  · rw [same]; exact emptyField.2.2
private theorem row_resident : EdgeResident heap row := by
  have original := (InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed
  exact resident_edges heap initial_good.native.machine.1.linked root original.resident row (by cbv; exact .head _)
private theorem mu_available : Available heap mu :=
  ((InternedFreshOrdinaryFacts.closed_verified expression).result root heap constructed).children mu (by cbv; exact .tail _ (.head _))
private theorem actual_cold : evaluated = .done row after := by cbv
private theorem actual_warm : execute 2 (.code (requestEdge domain row row)) after = .done row after := by cbv
private theorem actual_node : execute 2 (.code (requestNode domain mu mu)) after = .done mu after := by cbv

private theorem coldWarmProof :
    built = .done root heap ∧
    row.children = [first,mu] ∧
    execute 24 (.code (requestEdge domain row row)) before = .done row after ∧
    Good after ∧ SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
    after.operations.combinations (own.identity,own.identity) ≠ none ∧
    execute 2 (.code (requestEdge domain row row)) after = .done row after ∧ Good after := by
  have cold := SourceCurrentNativeOperationInvariants.edge 24 request before after row initial_good
    ⟨empty_domain machine,row_resident,row_resident⟩ actual_cold
  have grownRows : EdgeResident after.native.machine.heap row := cold.2.2.2.2
  have warm := SourceCurrentNativeOperationInvariants.edge 2 request after after row cold.1
    ⟨(empty_domain machine).grows _ cold.2.1,grownRows,grownRows⟩ actual_warm
  exact ⟨constructed,by cbv,actual_cold,cold.1,cold.1.operations,(by cbv; intro impossible; cases impossible),actual_warm,warm.1⟩

/-- Actual nonempty equality combination traverses ordinary and Mu children, then reuses the warm row. -/
theorem cold_warm :
    built = .done root heap ∧
    row.children = [first,mu] ∧
    execute 24 (.code (requestEdge domain row row)) before = .done row after ∧
    Good after ∧ SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
    after.operations.combinations (own.identity,own.identity) ≠ none ∧
    execute 2 (.code (requestEdge domain row row)) after = .done row after ∧ Good after := coldWarmProof

private theorem dispatchProof :
    execute 2 (.code (requestNode domain mu mu)) after = .done mu after ∧
    Good final ∧ SourceEqualityConstraintMemoAllocation.Valid final.operations ∧
    SourceEqualityConstraintAllocation.Ready final.operations.constraints dispatched.1 ∧
    after.operations.constraints.next < final.operations.constraints.next ∧
    SourceEqualityConstraintFieldLookup.load active final.operations.constraints = .ok (some ⟨own,.top⟩) := by
  have cold := SourceCurrentNativeOperationInvariants.edge 24 request before after row initial_good
    ⟨empty_domain machine,row_resident,row_resident⟩ actual_cold
  have initialGrowth := (SourceCurrentAllocatedPartialInitialization.operations_correct allocation.2 allocated.2.2.2.2).2.1
  have ownReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints own := allocated.2.2.1.grows initialGrowth.constraint_growth
  have afterReady := ownReady.grows cold.2.2.2.1.constraint_growth
  have nodeReady : NodeReady after.native.machine selectedRequest :=
    ⟨(empty_domain machine).grows _ cold.2.1,cold.2.2.1.available _ mu_available,cold.2.2.1.available _ mu_available⟩
  have next := SourceCurrentNativeOperationInvariants.node_dispatch 2 selectedRequest after after mu own 0 cold.1 nodeReady afterReady actual_node
  have loaded : SourceEqualityConstraintFieldLookup.load active before.operations.constraints = .ok (some ⟨own,.top⟩) :=
    SourceCurrentConjunctionEquality.load_grows active _ _ initialGrowth ⟨own,.top⟩ allocated.1
  exact ⟨actual_node,next.1,next.1.operations,next.2.1,by cbv,
    SourceCurrentConjunctionEquality.load_grows active _ _
      (SourceCurrentConjunctionEquality.grows_trans cold.2.2.2.1 next.2.2) ⟨own,.top⟩ loaded⟩

/-- A completed warm native node call derives a fresh ready inherited value and retains its original field. -/
theorem new_dispatch :
    execute 2 (.code (requestNode domain mu mu)) after = .done mu after ∧
    Good final ∧ SourceEqualityConstraintMemoAllocation.Valid final.operations ∧
    SourceEqualityConstraintAllocation.Ready final.operations.constraints dispatched.1 ∧
    after.operations.constraints.next < final.operations.constraints.next ∧
    SourceEqualityConstraintFieldLookup.load active final.operations.constraints = .ok (some ⟨own,.top⟩) := dispatchProof

end MicroCFTA.ActualInvariantKernels
