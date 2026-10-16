import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterProfiles

namespace MicroCFTA.OuterProfilesIndependent
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialMemoSound (NodeLaw EdgeLaw)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinaryOuterProfiles.Stored
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width budget : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}

/-- A current ready hit constructs its graph and derives exact-state reuse with both strong stores. -/
theorem warm_node_same_state
    {inventory : Inventory} {request : NodeRequest} {before running : Caller width}
    {result : Node} {handle : Nat} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value)
    (stored : Stored before)
    (started : beginNode request before = (handle, (.ready result, running))) :
    running = before ∧ ∃ actual : NodeCall budget request before result before,
      NodeCallReads formulas solver actual memos memos ∧
      beginNode request before = (handle, (.ready result, before)) ∧
      Stored before ∧ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow request.value result ∧
      ∃ next, Post formulas solver next before before memos ∧ Available before.checked.native.machine.heap result ∧
        NodeLaw formulas solver request result := by
  have same := (stored.structural.node_ready formulas solver request running handle result initial.sound
    initial.ready.semantic.ready.semantic.1.normal.facts.coherent available domain started).1
  subst running
  let actual : NodeCall budget request before result before := .hit started
  have reads : NodeCallReads formulas solver actual memos memos := .hit (started := started)
  have strong := SourceCurrentAllocatedFiniteOrdinaryOuterProfiles.node_call formulas solver reads inventory
    initial inherited available domain stored
  have verified := SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_call formulas solver reads inventory
    initial inherited available domain stored.structural
  obtain ⟨next, post, resident, _, _, law⟩ := verified.2
  exact ⟨rfl, actual, reads, started, strong.1, strong.2, next, post, resident, law⟩

/-- Actual Parent reads construct the outer EdgeBody and join strong stores with the same semantic return. -/
theorem parent_to_outer
    {inventory : Inventory} {original result : Edge} {loaded : Allocated} {inherited : EqValue}
    {before : Caller width} {checked : Checked width} {fourth : Fourth} {memo : Memo} {memos final : Memos}
    {parent : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint
      loaded inherited original.children before.checked before.fourth before.merge result checked fourth memo}
    (parentReads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver parent memos final)
    (field : SourceEqualityMkEdgeAllocation.contradictory original.entry.key.constraint = false →
      SourceEqualityConstraintFieldLookup.load original.entry.key.constraint before.checked.operations.constraints = .ok (some loaded))
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap original)
    (domain : DEdge original) (stored : Stored before) :
    ∃ actual : EdgeBody budget ⟨inherited, original⟩ before result
      (SourceCurrentAllocatedPartialState.advance before checked fourth memo),
      EdgeBodyReads formulas solver actual memos final ∧ Checks (edgeBodyTrace actual) ∧
      ∃ next, Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before checked fourth memo) final ∧
        InternedEdgeResidency.EdgeResident checked.native.machine.heap result ∧
        Stored (SourceCurrentAllocatedPartialState.advance before checked fourth memo) ∧
        SourceCurrentAllocatedFiniteOrdinaryRequired.EdgeNarrow original result ∧ EdgeLaw formulas solver ⟨inherited, original⟩ result := by
  let actual : EdgeBody budget ⟨inherited, original⟩ before result
      (SourceCurrentAllocatedPartialState.advance before checked fourth memo) := .parent field parent
  have reads : EdgeBodyReads formulas solver actual memos final := .parent (field := field) parentReads
  have strong := SourceCurrentAllocatedFiniteOrdinaryOuterProfiles.edge_body formulas solver reads inventory
    initial inheritedReady resident domain stored
  have verified := SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_body formulas solver reads inventory
    initial inheritedReady resident domain stored.structural
  obtain ⟨next, post, resultResident, _, _, law⟩ := verified.2
  exact ⟨actual, reads, verified.1, next, post, resultResident, strong.1, strong.2, law⟩

end MicroCFTA.OuterProfilesIndependent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 10000000
#print axioms MicroCFTA.OuterProfilesIndependent.warm_node_same_state
#check @MicroCFTA.OuterProfilesIndependent.warm_node_same_state
#print axioms MicroCFTA.OuterProfilesIndependent.parent_to_outer
#check @MicroCFTA.OuterProfilesIndependent.parent_to_outer
