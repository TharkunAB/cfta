import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequiredReservations

namespace RequiredReservationIndependentChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryReservations
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
local notation "Counts" => SourceCurrentAllocatedFiniteOrdinaryOccurrences.children
variable {Symbol Guard : Type} {rows arity : Nat} [DecidableEq (EdgeKey Symbol Guard)]

/-- One literal worker return supplies both exact profile preservation and observed Work bounds. -/
theorem same_return (fuel readFuel : Nat) (paths : List (List Int))
    (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (semantic : SemanticReady before) (available : Values before values) (profile : ChildrenShape rows arity values) :
    ∃ requests, Trace before after requests ∧ Keeps before after ∧ SemanticReady after ∧ Values after results ∧
      ChildrenShape rows arity results ∧ results.length = values.length ∧
      nodeRequests requests ≤ (Counts values).1 ∧ edgeRequests requests ≤ (Counts values).2 ∧
      after.nodes.next ≤ before.nodes.next + (Counts values).1 ∧ after.edges.next ≤ before.edges.next + (Counts values).2 := by
  have physical := SourceCurrentAllocatedFiniteOrdinaryRequiredProfile.requireAll_done fuel readFuel paths values results before after
    done semantic available profile
  obtain ⟨requests, trace, nodes, edges, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryRequiredReservations.requireAll_done fuel readFuel paths values results before after done
      semantic available (ChildrenShape.domain values profile)
  exact ⟨requests, trace, physical.1, physical.2.1, physical.2.2.1, physical.2.2.2.1, physical.2.2.2.2,
    nodes, edges, nodeSupply, edgeSupply⟩

/-- Serial raw worker returns compose observed requests at their actual intermediate heap. -/
theorem serial_requests (fuel readFuel : Nat) (firstPaths lastPaths : List (List Int))
    (values middleValues results : List (Value Symbol Guard)) (before middle after : State Symbol Guard)
    (first : SourceEqualityRequiredExecution.requireAll fuel readFuel firstPaths values before = .done middleValues middle)
    (last : SourceEqualityRequiredExecution.requireAll fuel readFuel lastPaths middleValues middle = .done results after)
    (semantic : SemanticReady before) (available : Values before values) (profile : ChildrenShape rows arity values) :
    ∃ requests, Trace before after requests ∧ ChildrenShape rows arity results ∧
      nodeRequests requests ≤ (Counts values).1 + (Counts middleValues).1 ∧
      edgeRequests requests ≤ (Counts values).2 + (Counts middleValues).2 := by
  obtain ⟨one, oneTrace, _kept, middleSemantic, middleAvailable, middleProfile, _length, oneNodes, oneEdges, _nodes, _edges⟩ :=
    same_return fuel readFuel firstPaths values middleValues before middle first semantic available profile
  obtain ⟨two, twoTrace, _kept, _semantic, _available, lastProfile, _length, twoNodes, twoEdges, _nodes, _edges⟩ :=
    same_return fuel readFuel lastPaths middleValues results middle after last middleSemantic middleAvailable middleProfile
  refine ⟨one ++ two, .trans oneTrace twoTrace, lastProfile, ?_, ?_⟩
  · rw [nodeRequests_append]; omega
  · rw [edgeRequests_append]; omega

/-- A cached raw edge still records one request while reserving no new edge identity. -/
theorem warm_request (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard))
    (before : State Symbol Guard) (entry : Interned (EdgeKey Symbol Guard))
    (found : before.edges.table ⟨symbol, children.map Value.referenceOf, guard⟩ = some entry) :
    edgeRequests (observe (makeEdge symbol guard children) before) = 1 ∧
      edgeReservations (observe (makeEdge symbol guard children) before) = 0 := by
  simp only [makeEdge_observe, found, Option.isNone_some, edgeRequests, edgeReservations]
  decide

#print axioms same_return
#check @same_return
#print axioms serial_requests
#check @serial_requests
#print axioms warm_request
#check @warm_request
end RequiredReservationIndependentChecks
