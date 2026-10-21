import MicroCFTA.InternedNestedRequestFacts

/-!
# Derived provenance for the complete nested source syntax

The proof follows every nested constructor. It derives coherent records,
available children, outgoing edge links, and issued-reference history.
Pending outcomes retain the same invariants at their actual stopping point.
-/
namespace MicroCFTA.InternedNestedProvenance
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency
open InternedNestedConstruction InternedNestedFacts InternedNestedRequestFacts

/-- Every returned child is available in the actual final state. -/
def Values (state : State Symbol Guard) (values : List (Value Symbol Guard)) : Prop :=
  ∀ value ∈ values, Available state value

/-- Every returned edge is the complete canonical payload in the final state. -/
def Edges (state : State Symbol Guard) (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ edge ∈ edges, EdgeResident state edge

/-- Primitive depth and ordinary probe references require no interned reservation. -/
theorem depth_available (state : State Symbol Guard) : Available state (.reference .depth) :=
  reference_available state .depth (sentinel_references_issued state.nodes 0).1

theorem ordinary_available (state : State Symbol Guard) (depth : Nat) :
    Available state (.reference (.uninterned depth)) :=
  reference_available state (.uninterned depth) (sentinel_references_issued state.nodes depth).2

mutual
/-- All source record invariants follow from the nested expression and its
actual earlier inputs. No final record property is assumed. -/
theorem build_verified [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) :
    Verified state (build expression environment state) Available := by
  cases expression with
  | empty => simpa only [build] using pure_verified state facts .empty Available (empty_available state)
  | var index =>
      cases found : environment[index]? with
      | none => simpa only [build, found, Option.getD_none] using
          pure_verified state facts .empty Available (empty_available state)
      | some value => simpa only [build, found, Option.getD_some] using
          pure_verified state facts value Available (inputs value (List.mem_of_getElem? found))
  | node edges =>
      simp only [build]
      exact bind_verified state _ _ Edges Available (buildEdges_verified edges environment state facts inputs)
        (fun values after _ afterFacts resident => node_verified values after afterFacts resident)
  | union members =>
      simp only [build]
      exact bind_verified state _ _ Values Available (buildMany_verified members environment state facts inputs)
        (fun values after _ afterFacts available => union_verified values after afterFacts available)
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      have checked : ∀ name current, Facts current → Values current environment → Available current (.reference name) →
          Verified current (callback name current) Available := by
        intro name current currentFacts currentInputs localAvailable
        have withLocal : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | present
          · exact localAvailable
          · exact currentInputs value present
        exact bind_verified current _ _ Available Available
          (build_verified body (.reference name :: environment) current currentFacts withLocal)
          (fun value after _ afterFacts available => filter_verified name value after afterFacts available)
      have depth := checked .depth state facts inputs (depth_available state)
      rw [build]
      change Verified state ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary) Available
      apply bind_verified state _ _ Available Available depth
      intro depthValue afterDepth depthReturned depthFacts depthAvailable
      have afterDepthInputs : Values afterDepth environment := by
        intro value member
        simpa [depthReturned, Outcome.state] using depth.available value (inputs value member)
      have ordinary := checked (.uninterned depthValue.depth) afterDepth depthFacts afterDepthInputs
        (ordinary_available afterDepth depthValue.depth)
      apply bind_verified afterDepth _ _ Available Available ordinary
      intro ordinaryValue afterOrdinary ordinaryReturned ordinaryFacts ordinaryAvailable
      have finalDepth : Available afterOrdinary depthValue := by
        simpa [ordinaryReturned, Outcome.state] using ordinary.available depthValue depthAvailable
      have finalInputs : Values afterOrdinary environment := by
        intro value member
        simpa [ordinaryReturned, Outcome.state] using ordinary.available value (afterDepthInputs value member)
      apply request_verified smart depthValue ordinaryValue callback afterOrdinary ordinaryFacts finalDepth ordinaryAvailable
      intro name current growth history currentFacts localAvailable
      exact checked name current currentFacts
        (fun value member => (finalInputs value member).grows afterOrdinary current growth history) localAvailable
termination_by sizeOf expression

/-- Ordered child evaluation derives availability after every previous nested effect. -/
theorem buildMany_verified [DecidableEq (EdgeKey Symbol Guard)] (expression : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) :
    Verified state (buildMany expression environment state) Values := by
  cases expression with
  | nil => simpa only [buildMany] using pure_verified state facts [] Values (by intro value member; cases member)
  | cons first rest =>
      have head := build_verified first environment state facts inputs
      simp only [buildMany]
      apply bind_verified state _ _ Available Values head
      intro value afterHead returned headFacts valueAvailable
      have tailInputs : Values afterHead environment := by
        intro item member
        simpa [returned, Outcome.state] using head.available item (inputs item member)
      have tail := buildMany_verified rest environment afterHead headFacts tailInputs
      apply bind_verified afterHead _ _ Values Values tail
      intro values afterTail tailReturned tailFacts valuesAvailable
      apply pure_verified afterTail tailFacts (value :: values) Values
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · simpa [tailReturned, Outcome.state] using tail.available _ valueAvailable
      · exact valuesAvailable item member
termination_by sizeOf expression

/-- Every generated edge carries its actual canonical payload and available
children through all later sibling computations. -/
theorem buildEdges_verified [DecidableEq (EdgeKey Symbol Guard)] (expression : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) :
    Verified state (buildEdges expression environment state) Edges := by
  cases expression with
  | nil => simpa only [buildEdges] using pure_verified state facts [] Edges (by intro edge member; cases member)
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have childrenBuilt := buildMany_verified children environment state facts inputs
          simp only [buildEdges]
          apply bind_verified state _ _ Values Edges childrenBuilt
          intro values afterChildren childrenReturned childrenFacts valuesAvailable
          have edgeBuilt := edge_verified symbol constraint values afterChildren childrenFacts valuesAvailable
          apply bind_verified afterChildren _ _ EdgeResident Edges edgeBuilt
          intro edge afterEdge edgeReturned edgeFacts edgeResident
          have tailInputs : Values afterEdge environment := by
            intro value member
            have intermediate : Available afterChildren value := by
              simpa [childrenReturned, Outcome.state] using childrenBuilt.available value (inputs value member)
            simpa [edgeReturned, Outcome.state] using edgeBuilt.available value intermediate
          have tail := buildEdges_verified rest environment afterEdge edgeFacts tailInputs
          apply bind_verified afterEdge _ _ Edges Edges tail
          intro edges afterTail tailReturned tailFacts edgesResident
          apply pure_verified afterTail tailFacts (edge :: edges) Edges
          intro selected member
          rcases List.mem_cons.mp member with rfl | member
          · have retained := edge_grows afterEdge _ tail.growth _ edgeResident
            simpa [tailReturned, Outcome.state] using retained
          · exact edgesResident selected member
termination_by sizeOf expression
end

/-- Empty-state nested construction establishes all record invariants even
when a pending source cache entry is reached. -/
theorem closed_verified [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    Verified empty (build expression [] empty) Available :=
  build_verified expression [] empty empty_facts (by intro value member; cases member)

end MicroCFTA.InternedNestedProvenance
