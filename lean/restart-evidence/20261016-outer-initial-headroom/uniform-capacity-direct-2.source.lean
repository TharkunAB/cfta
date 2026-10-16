import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentInitialCapacity
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterParentReads

/-!
# Parent capacity from initial uniform profiles and supplies

The same initial resident edge supplies its stored field and own precheck.
Its hereditary guard vector bounds the actual own class and path records.
Uniform constructor budgets dominate the literal reached parent budget.
No parent completion, future range plan, or inherited size bound is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformCapacity
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState (EdgeRequest)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryParentCapacity (ParentCapacity)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets (nodeBudget edgeBudget receipt_budget)
open MergedOrdinaryHeight (edgeHeight childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState.Stored
local notation "GuardEdge" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial uniform headroom derives every same-cache parent query-entry check. -/
theorem complete (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {request : EdgeRequest} {before : Caller (bits + 2)}
    (inventory : Inventory) {memos : Memos} (initial : Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (stored : Stored before)
    (limits : Limits) (rows arity bound : Nat) (guards : GuardEdge limits request.value)
    (profile : EdgeShape rows arity request.value) (heightBound : edgeHeight request.value ≤ bound)
    (nodes : before.checked.native.machine.heap.nodes.next + nodeBudget limits rows arity bound ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + edgeBudget limits rows arity bound ≤ 2 ^ (bits + 2)) :
    ParentCapacity bits budget request before := by
  intro live loaded found
  have cached := (initial.ready.good.fields request.value.entry.key request.value resident).1
  obtain ⟨own, branch, receipt⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory
    before.checked initial.ready initial.admitted request.value.entry.key.constraint cached loaded found request.inherited inherited
  have rawBound := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.guard request.value guards
  have lengthBound := EdgeShape.arity request.value profile
  have counts := receipt_budget receipt limits rawBound rows arity arity bound (Nat.le_refl _)
  have paths : ∀ records,
      (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard request.inherited before.checked.operations).1 =
        .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths,
        path.length ≤ SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits := by
    intro records actual
    have same : branch = .classes records := Except.ok.inj (receipt.actual.symm.trans actual)
    subst branch
    exact (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.receipt receipt limits rawBound).2.2.2
  have capacity := SourceCurrentAllocatedFiniteOrdinaryParentInitialCapacity.complete formulas solver bits budget
    request loaded initial found inherited resident stored.base.base.profiles stored.base.base.native stored.base.base.output
    rows arity arity (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound
    (EdgeShape.children request.value profile) lengthBound paths heightBound
    (Nat.le_trans (Nat.add_le_add_left counts.1 _) nodes) (Nat.le_trans (Nat.add_le_add_left counts.2 _) edges)
  exact capacity live loaded found

/-- The derived numeric plan supplies the old resident parent ranges at this same entry. -/
theorem resident_ranges (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {request : EdgeRequest} {before : Caller (bits + 2)}
    (inventory : Inventory) {memos : Memos} (initial : Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (stored : Stored before)
    (limits : Limits) (rows arity bound : Nat) (guards : GuardEdge limits request.value)
    (profile : EdgeShape rows arity request.value) (heightBound : edgeHeight request.value ≤ bound)
    (nodes : before.checked.native.machine.heap.nodes.next + nodeBudget limits rows arity bound ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + edgeBudget limits rows arity bound ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before :=
  SourceCurrentAllocatedFiniteOrdinaryParentCapacity.resident_ranges bits formulas solver budget request initial inherited
    resident (EdgeShape.domain request.value profile) stored.structural
    (complete bits formulas solver inventory initial inherited resident stored limits rows arity bound guards profile heightBound nodes edges)

/-- Initial headroom constructs strict reads for the supplied exact raw parent return. -/
theorem edge_body_reads (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {request : EdgeRequest} {before after : Caller (bits + 2)} {result : EdgeValue Symbol Guard}
    (actual : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result after)
    (inventory : Inventory) {memos : Memos} (initial : Context formulas solver inventory before memos)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (stored : Stored before)
    (limits : Limits) (rows arity bound : Nat) (guards : GuardEdge limits request.value)
    (profile : EdgeShape rows arity request.value) (heightBound : edgeHeight request.value ≤ bound)
    (nodes : before.checked.native.machine.heap.nodes.next + nodeBudget limits rows arity bound ≤ 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next + edgeBudget limits rows arity bound ≤ 2 ^ (bits + 2)) :
    ∃ final, SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads formulas solver actual memos final :=
  SourceCurrentAllocatedFiniteOrdinaryOuterParentReads.edge_body bits formulas solver actual inventory initial inherited
    resident (EdgeShape.domain request.value profile) stored.structural
    (complete bits formulas solver inventory initial inherited resident stored limits rows arity bound guards profile heightBound nodes edges)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformCapacity
