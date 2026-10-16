import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterPrefixResources

namespace MicroCFTA.PrefixResourcesChecks
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedPartialActiveOrder (ActiveAbove nodeRank edgeRank child_lt_edge)
open SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs (Headroom)
open SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers (nodeNodes nodeEdges descendantsNodes descendantsEdges)
open SourceCurrentAllocatedFiniteOrdinaryActualOuterWork (WorkBounds)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers (parentRows)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "PN" => SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.nodeBudget
local notation "PE" => SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets.edgeBudget
local notation "PG" => SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

theorem empty_node_publication (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget handle : Nat} {inherited : EqValue} {before running : Caller (bits + 2)}
    (inventory : Inventory) {memos : Memos} (initial : Context formulas solver inventory before memos)
    (ready : EqReady before.checked.operations.constraints inherited) (stored : Stored before)
    (active : ActiveAbove (nodeRank ⟨inherited, .empty⟩) before)
    (started : beginNode ⟨inherited, .empty⟩ before = (handle, .evaluate ⟨inherited, .empty⟩, running))
    (limits : Limits) (restNodes restEdges : Nat)
    (room : Headroom bits before.checked.native.machine.heap restNodes restEdges) :
    ∃ next final,
      NodeCallReads formulas solver (NodeCall.evaluate (budget := budget) started .empty) memos final ∧
      Post formulas solver next before (finishNode handle .empty running) final ∧
      Stored (finishNode handle .empty running) ∧
      (finishNode handle .empty running).nodeResults.cells handle =
        some ⟨⟨inherited, .empty⟩, .returned .empty⟩ ∧
      WorkBounds before.checked.native.machine.heap (finishNode handle .empty running).checked.native.machine.heap 0 0 ∧
      Headroom bits (finishNode handle .empty running).checked.native.machine.heap restNodes restEdges := by
  have available := empty_available before.checked.native.machine.heap
  obtain ⟨next, final, reads, _checks, post, _output, retained, _narrow, _certificate, work⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterPrefixResources.node_call bits formulas solver (.evaluate started .empty) inventory initial ready available .empty stored active
      0 0 0 limits True.intro True.intro (Nat.le_refl _) (room.mono (Nat.zero_le _) (Nat.zero_le _))
  obtain ⟨_current, _good, _key, cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start formulas solver
    initial ready available started
  have published := finishNode_returned handle ⟨inherited, .empty⟩ .empty running cell
  have split : Headroom bits before.checked.native.machine.heap
      (nodeNodes 0 0 limits 0 + restNodes) (nodeEdges 0 0 limits 0 + restEdges) := by
    simpa only [nodeNodes, SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers.nodeEdges, Nat.zero_add] using room
  exact ⟨next, final, reads, post, retained, published, work, split.after work⟩

theorem parent_then_descendants (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {request : EdgeRequest} {before middle after : Caller (bits + 2)} {narrowed result : Edge}
    (first : EdgeCall budget request before narrowed middle)
    (following : Descendants budget request.inherited narrowed middle result after)
    (inventory : Inventory) {memos : Memos} (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Edge request.value) (stored : Stored before)
    (active : ActiveAbove (edgeRank request) before)
    (rows arity bound : Nat) (limits : Limits) (profile : EdgeShape rows arity request.value)
    (guards : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits request.value)
    (heightBound : MergedOrdinaryHeight.edgeHeight request.value ≤ bound) (restNodes restEdges : Nat)
    (room : Headroom bits before.checked.native.machine.heap
      (PN limits rows arity bound + (descendantsNodes (parentRows limits rows arity bound) (max arity 1) (PG limits) bound + restNodes))
      (PE limits rows arity bound + (descendantsEdges (parentRows limits rows arity bound) (max arity 1) (PG limits) bound + restEdges))) :
    ∃ edgeMemos next final,
      EdgeCallReads formulas solver first memos edgeMemos ∧ DescendantsReads formulas solver following edgeMemos final ∧
      Post formulas solver next before after final ∧ Stored after ∧
      SourceCurrentAllocatedFiniteOrdinaryRequired.EdgeNarrow request.value result ∧
      WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
        (PN limits rows arity bound + descendantsNodes (parentRows limits rows arity bound) (max arity 1) (PG limits) bound)
        (PE limits rows arity bound + descendantsEdges (parentRows limits rows arity bound) (max arity 1) (PG limits) bound) ∧
      Headroom bits after.checked.native.machine.heap restNodes restEdges := by
  obtain ⟨edgeInventory, edgeMemos, edgeReads, _edgeChecks, edgePost, edgeResident, edgeStored, narrow,
      certificate, edgeWork⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterPrefixResources.edge_call bits formulas solver first inventory initial inherited resident domain stored active
      rows arity bound limits profile guards heightBound (room.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  have remaining := room.after edgeWork
  have returnedProfile := certificate rows arity bound limits profile guards heightBound
  have ancestor := ((SourceCurrentAllocatedPartialActiveFrames.edge_call first).activeExcept active).mono
    (Nat.sub_le (edgeRank request) 1)
  have smaller : ∀ child ∈ narrowed.children, nodeRank ⟨request.inherited, child⟩ ≤ edgeRank request - 1 := by
    intro child member
    have lower := child_lt_edge request.inherited request.inherited narrowed child member
    have bounded := narrow.2
    change MergedOrdinaryHeight.edgeHeight narrowed ≤ MergedOrdinaryHeight.edgeHeight request.value at bounded
    change nodeRank ⟨request.inherited, child⟩ < 2 * (MergedOrdinaryHeight.edgeHeight narrowed + 1) at lower
    change nodeRank ⟨request.inherited, child⟩ ≤ 2 * (MergedOrdinaryHeight.edgeHeight request.value + 1) - 1
    omega
  obtain ⟨next, final, childReads, _childChecks, childPost, _childResident, childStored, childNarrow,
      _childCertificate, childWork⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryOuterPrefixResources.descendants bits formulas solver following edgeInventory edgePost.context
      (inherited.grows edgePost.effects.grows.constraint_growth) edgeResident narrow.1 edgeStored
      (edgeRank request - 1) ancestor smaller
      (parentRows limits rows arity bound) (max arity 1) bound (PG limits)
      returnedProfile.1 returnedProfile.2 (Nat.le_trans narrow.2 heightBound)
      (remaining.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  exact ⟨edgeMemos, next, final, edgeReads, childReads, edgePost.trans childPost, childStored,
    SourceCurrentAllocatedFiniteOrdinaryNarrow.edge_trans narrow childNarrow, edgeWork.trans childWork,
    remaining.after childWork⟩

end MicroCFTA.PrefixResourcesChecks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#print axioms MicroCFTA.PrefixResourcesChecks.empty_node_publication
#check @MicroCFTA.PrefixResourcesChecks.empty_node_publication
#print axioms MicroCFTA.PrefixResourcesChecks.parent_then_descendants
#check @MicroCFTA.PrefixResourcesChecks.parent_then_descendants
