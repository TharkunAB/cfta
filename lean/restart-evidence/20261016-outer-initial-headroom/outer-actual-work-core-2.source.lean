import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRawRebuildResources

/-!
# Constructor Work through the same actual outer reads

The proof records requests at their actual intermediate heaps.
It follows parent reduction, returned descendants, and the original suffix.
Earlier reads derive the current Context, profile, and causal stores.
No capacity, reserved headroom, or future result law is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualOuterWork
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape RowsShape EdgeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets (nodeBudget edgeBudget)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers (parentRows)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "GPNode" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "GPRows" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows
local notation "GPEdge" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge
local notation "GPChildren" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children
local notation "parentGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit
section WorkAlgebra
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The trace retains its exact actual heaps and bounds both constructor request counts. -/
def WorkBounds (before after : Heap) (nodes edges : Nat) : Prop :=
  ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ nodes ∧ edgeRequests requests ≤ edges

/-- An unchanged heap emits no constructor request. -/
theorem WorkBounds.refl (before : Heap) : WorkBounds before before 0 0 :=
  ⟨[], .refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- Larger numeric envelopes retain the same trace and request list. -/
theorem WorkBounds.mono {before after : Heap} {nodes edges largerNodes largerEdges : Nat}
    (actual : WorkBounds before after nodes edges) (nodeBound : nodes ≤ largerNodes) (edgeBound : edges ≤ largerEdges) :
    WorkBounds before after largerNodes largerEdges := by
  obtain ⟨requests, trace, nodes, edges⟩ := actual
  exact ⟨requests, trace, Nat.le_trans nodes nodeBound, Nat.le_trans edges edgeBound⟩

/-- Sequential composition retains the actual request order and exact middle heap. -/
theorem WorkBounds.trans {before middle after : Heap} {firstNodes firstEdges lastNodes lastEdges : Nat}
    (first : WorkBounds before middle firstNodes firstEdges) (last : WorkBounds middle after lastNodes lastEdges) :
    WorkBounds before after (firstNodes + lastNodes) (firstEdges + lastEdges) := by
  obtain ⟨earlier, first, firstN, firstE⟩ := first
  obtain ⟨later, last, lastN, lastE⟩ := last
  refine ⟨earlier ++ later, first.trans last, ?_, ?_⟩
  · rw [nodeRequests_append]; exact Nat.add_le_add firstN lastN
  · rw [edgeRequests_append]; exact Nat.add_le_add firstE lastE

end WorkAlgebra

variable {width budget : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem values_grow {before after : Caller width} {values : List Node}
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical after.checked))
    (available : Values before.checked.native.machine.heap values) : Values after.checked.native.machine.heap values :=
  fun value member => effects.keeps.available value (available value member)

private theorem edges_grow {before after : Caller width} {values : List Edge}
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical after.checked))
    (resident : Edges before.checked.native.machine.heap values) : Edges after.checked.native.machine.heap values :=
  fun edge member => InternedEdgeResidency.edge_grows _ _ effects.keeps.growth edge (resident edge member)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem modify_work (original : Node) (oldRows newRows : List Edge) (before : SourceEqualityNativeDemand.State width) :
    WorkBounds before.native.machine.heap (SourceCurrentAllocatedRawRebuild.modify original oldRows newRows before).2.native.machine.heap 1 0 := by
  obtain ⟨trace, nodes, edges⟩ := SourceCurrentAllocatedFiniteOrdinaryRawRebuildResources.modify_work original oldRows newRows before
  exact ⟨_, trace, nodes, Nat.le_of_eq edges⟩

private theorem edge_work (original : Edge) (values : List Node) (before : SourceEqualityNativeDemand.State width) :
    WorkBounds before.native.machine.heap (SourceCurrentAllocatedRawRebuild.edge original values before).2.native.machine.heap 0 1 := by
  refine ⟨_, .work _ (makeEdge original.entry.key.symbol original.entry.key.constraint values), ?_, ?_⟩
  · simp only [SourceCurrentAllocatedFiniteOrdinaryReservations.makeEdge_observe, nodeRequests, Nat.le_refl]
  · simp only [SourceCurrentAllocatedFiniteOrdinaryReservations.makeEdge_observe, edgeRequests, Nat.le_refl]

variable [DecidableEq Symbol] [DecidableEq Node]

private def NodeBound (top : SourceCurrentAllocatedPartialChecks.Trace width budget) (request : NodeRequest) (before : Caller width)
    (_result : Node) (after : Caller width) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    DNode request.value → Stored before → ∀ rows arity bound (limits : Limits),
    NodeShape rows arity request.value → GPNode limits request.value → height request.value ≤ bound →
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound)

private def EdgeBound (top : SourceCurrentAllocatedPartialChecks.Trace width budget) (request : EdgeRequest) (before : Caller width)
    (_result : Edge) (after : Caller width) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Resident before.checked.native.machine.heap request.value →
    DEdge request.value → Stored before → ∀ rows arity bound (limits : Limits),
    EdgeShape rows arity request.value → GPEdge limits request.value → edgeHeight request.value ≤ bound →
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (nodeBudget limits rows arity bound) (edgeBudget limits rows arity bound)

private def RowsBound {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    (actual : Rows budget inherited values before results after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (rowsTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    DRows values → Stored before → ∀ rows arity bound (limits : Limits),
    RowsShape rows arity values → GPRows limits values → edgesHeight values ≤ bound →
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (values.length * rowNodes rows arity limits bound) (values.length * rowEdges rows arity limits bound)

private def DescendantsBound {inherited : EqValue} {value result : Edge} {before after : Caller width}
    (actual : Descendants budget inherited value before result after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (descendantsTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints inherited → Resident before.checked.native.machine.heap value →
    DEdge value → Stored before → ∀ rows arity bound (limits : Limits),
    EdgeShape rows arity value → GPEdge limits value → edgeHeight value ≤ bound →
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (descendantsNodes rows arity limits bound) (descendantsEdges rows arity limits bound)

private def ChildrenBound {combined : EqValue} {values results : List Node} {before after : Caller width}
    (actual : Children budget combined values before results after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (childrenTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    DChildren values → Stored before → ∀ rows arity bound (limits : Limits),
    ChildrenShape rows arity values → GPChildren limits values → childrenHeight values ≤ bound →
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (values.length * nodeNodes rows arity limits bound) (values.length * nodeEdges rows arity limits bound)

private def WalkBound {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    (actual : Walk budget combined index values before results after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (walkTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    DChildren values → Stored before → ∀ rows arity bound (limits : Limits),
    ChildrenShape rows arity values → GPChildren limits values → childrenHeight values ≤ bound →
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (values.length * nodeNodes rows arity limits bound) (values.length * nodeEdges rows arity limits bound)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualOuterWork
