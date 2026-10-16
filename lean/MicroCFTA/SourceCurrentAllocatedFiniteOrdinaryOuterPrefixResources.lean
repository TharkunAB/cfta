import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceRoot
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterResourceEdge
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterPrefixUnique

/-!
# Resource receipts for exact supplied outer prefixes

Initial profiles and headroom construct an independent completed prefix.
Raw graph uniqueness identifies its result and complete returned caller.
The receipt then applies to the supplied graph at those same endpoints.
No future entry Plan or completed alternative prefix is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterPrefixResources
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (NodeCertificate EdgeCertificate)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer (DescendantsCertificate)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank edgeRank)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom Below)
open SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryActualOuterWork (WorkBounds)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open MergedOrdinaryHeight (height edgeHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Initial supplies derive reads and Work for the exact supplied raw node return. -/
theorem node_call (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {request : NodeRequest} {before after : Caller (bits + 2)} {result : Node}
    (actual : NodeCall budget request before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value)
    (stored : Stored before) (active : ActiveAbove (nodeRank request) before)
    (rows arity bound : Nat) (limits : Limits) (profile : NodeShape rows arity request.value)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node limits request.value)
    (heightBound : height request.value ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap
      (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound)) :
    ∃ next final, NodeCallReads formulas solver actual memos final ∧ Checks (nodeCallTrace actual) ∧
      Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
      Stored after ∧ NodeNarrow request.value result ∧ NodeCertificate request result ∧
      WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
        (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound) := by
  obtain ⟨output, returned, next, final, _stable, constructed, reads, checks, post, availableAfter,
      retained, narrow, certificate, work, _finalRoom, _law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterResourceRoot.finite bits formulas solver budget request
      initial inherited available domain stored active rows arity bound limits profile guards heightBound room
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterPrefixUnique.node_call actual constructed
  exact ⟨next, final, reads, checks, post, availableAfter, retained, narrow, certificate, work⟩

/-- Initial supplies derive the same full receipt for the supplied raw edge return. -/
theorem edge_call (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {request : EdgeRequest} {before after : Caller (bits + 2)} {result : Edge}
    (actual : EdgeCall budget request before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (domain : DEdge request.value)
    (stored : Stored before) (active : ActiveAbove (edgeRank request) before)
    (rows arity bound : Nat) (limits : Limits) (profile : EdgeShape rows arity request.value)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits request.value)
    (heightBound : edgeHeight request.value ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap
      (SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.nodeBudget limits rows arity bound)
      (SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.edgeBudget limits rows arity bound)) :
    ∃ next final, EdgeCallReads formulas solver actual memos final ∧ Checks (edgeCallTrace actual) ∧
      Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
      Stored after ∧ EdgeNarrow request.value result ∧ EdgeCertificate request result ∧
      WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
        (SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.nodeBudget limits rows arity bound)
        (SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.edgeBudget limits rows arity bound) := by
  obtain ⟨output, returned, next, final, _stable, constructed, reads, checks, post, residentAfter,
      retained, narrow, certificate, _law⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterResourceEdge.finite bits formulas solver budget request
      initial inherited resident domain stored active rows arity bound limits profile guards heightBound room
  have work := SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.edge_call formulas solver reads inventory
    initial inherited resident domain stored rows arity bound limits profile guards heightBound
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterPrefixUnique.edge_call actual constructed
  exact ⟨next, final, reads, checks, post, residentAfter, retained, narrow, certificate, work⟩

/-- Closed smaller-node completion supplies reads for the exact descendant prefix. -/
theorem descendants (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {inherited : EqValue} {value result : Edge} {before after : Caller (bits + 2)}
    (actual : Descendants budget inherited value before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : EdgeResident before.checked.native.machine.heap value) (domain : DEdge value)
    (stored : Stored before) (cap : Nat) (active : ActiveAbove cap before)
    (smaller : ∀ child ∈ value.children, nodeRank ⟨inherited, child⟩ ≤ cap)
    (rows arity bound : Nat) (limits : Limits) (profile : EdgeShape rows arity value)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits value)
    (heightBound : edgeHeight value ≤ bound)
    (room : Headroom bits before.checked.native.machine.heap
      (descendantsNodes rows arity limits bound) (descendantsEdges rows arity limits bound)) :
    ∃ next final, DescendantsReads formulas solver actual memos final ∧ Checks (descendantsTrace actual) ∧
      Post formulas solver next before after final ∧ EdgeResident after.checked.native.machine.heap result ∧
      Stored after ∧ EdgeNarrow value result ∧ DescendantsCertificate value result ∧
      WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
        (descendantsNodes rows arity limits bound) (descendantsEdges rows arity limits bound) := by
  have completed : Below bits formulas solver budget (cap + 1) := by
    intro nextInventory current currentMemos request _lower context ready available domain stored above
      rows arity bound limits profile guards heightBound room
    obtain ⟨output, returned, next, final, _stable, constructed, reads, checks, post, availableAfter,
        retained, narrow, law⟩ :=
      SourceCurrentAllocatedFiniteOrdinaryOuterResourceNode.finite formulas solver budget request
        context ready available domain stored above rows arity bound limits profile guards heightBound room
    exact ⟨output, returned, next, final, constructed, reads, checks, post, availableAfter, retained, narrow, law⟩
  obtain ⟨output, returned, next, final, constructed, reads, checks, post, residentAfter, _retained, _narrow⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterResourceRows.descendants formulas solver budget (cap + 1) inherited value
      initial inheritedReady resident domain (fun child member => Nat.lt_succ_of_le (smaller child member)) stored
      (by simpa only [Nat.add_sub_cancel] using active) completed
      rows arity bound limits profile guards heightBound room
  have produced := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer.descendants formulas solver reads inventory
    initial inheritedReady resident domain stored
  have work := SourceCurrentAllocatedFiniteOrdinaryActualOuterWork.descendants formulas solver reads inventory
    initial inheritedReady resident domain stored rows arity bound limits profile guards heightBound
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterPrefixUnique.descendants actual constructed
  exact ⟨next, final, reads, checks, post, residentAfter, produced.1, produced.2.1, produced.2.2, work⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterPrefixResources
