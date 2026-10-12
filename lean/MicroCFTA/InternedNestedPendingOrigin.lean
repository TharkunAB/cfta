import MicroCFTA.InternedPendingOrigins

/-!
# Every possible nested pending result has an actual ancestor origin

The proof follows arbitrary source syntax and every real constructor branch.
Complete results retain the current pending-key coverage. A pending result
identifies one of the actual reservations reached earlier in that execution.
-/
namespace MicroCFTA.InternedPendingOrigins
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedNestedCoverage
open InternedBinderProtocol (NodeKey)

mutual
/-- Arbitrary nested source execution derives reservation provenance for each completed or pending outcome. -/
theorem build_certified [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (origins : Origins pending state) (covered : Covered pending state) :
    Certified pending (build expression environment state) := by
  cases expression with
  | empty | var index => simpa only [build, Certified] using And.intro origins covered
  | node edges =>
      simp only [build]
      exact bind_certified _ _ (buildEdges_certified edges environment state facts inputs origins covered)
        (buildEdges_verified edges environment state facts inputs)
        (fun _ after _ afterFacts _ afterOrigins afterCovered => work_certified _ after afterFacts.coherent.valid afterOrigins afterCovered)
  | union members =>
      simp only [build]
      exact bind_certified _ _ (buildMany_certified members environment state facts inputs origins covered)
        (buildMany_verified members environment state facts inputs)
        (fun _ after _ afterFacts _ afterOrigins afterCovered => work_certified _ after afterFacts.coherent.valid afterOrigins afterCovered)
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
      have certified : ∀ name current currentPending, Facts current → Values current environment →
          Available current (.reference name) → Origins currentPending current → Covered currentPending current →
          Certified currentPending (callback name current) := by
        intro name current currentPending currentFacts currentInputs localAvailable currentOrigins currentCovered
        have withLocal : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | present
          · exact localAvailable
          · exact currentInputs value present
        exact bind_certified _ _
          (build_certified body (.reference name :: environment) current currentFacts withLocal currentOrigins currentCovered)
          (build_verified body (.reference name :: environment) current currentFacts withLocal)
          (fun value after _ afterFacts _ afterOrigins afterCovered =>
            work_certified (withoutSelfReference name value) after afterFacts.coherent.valid afterOrigins afterCovered)
      have depth := checked .depth state facts inputs (depth_available state)
      rw [build]
      change Certified pending ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary)
      apply bind_certified _ _ (certified .depth state pending facts inputs (depth_available state) origins covered) depth
      intro depthValue afterDepth depthReturned depthFacts depthAvailable depthOrigins depthCovered
      have afterDepthInputs : Values afterDepth environment := by
        intro value member
        simpa [depthReturned, Outcome.state] using depth.available value (inputs value member)
      have ordinary := checked (.uninterned depthValue.depth) afterDepth depthFacts afterDepthInputs
        (ordinary_available afterDepth depthValue.depth)
      apply bind_certified _ _
        (certified (.uninterned depthValue.depth) afterDepth pending depthFacts afterDepthInputs
          (ordinary_available afterDepth depthValue.depth) depthOrigins depthCovered) ordinary
      intro ordinaryValue afterOrdinary ordinaryReturned ordinaryFacts ordinaryAvailable ordinaryOrigins ordinaryCovered
      have finalDepth : Available afterOrdinary depthValue := by
        simpa [ordinaryReturned, Outcome.state] using ordinary.available depthValue depthAvailable
      have finalInputs : Values afterOrdinary environment := by
        intro value member
        simpa [ordinaryReturned, Outcome.state] using ordinary.available value (afterDepthInputs value member)
      apply request_certified smart depthValue ordinaryValue callback afterOrdinary ordinaryFacts finalDepth ordinaryAvailable
        ordinaryOrigins ordinaryCovered
      intro name current growth history currentFacts localAvailable currentOrigins currentCovered
      exact certified name current _ currentFacts
        (fun value member => (finalInputs value member).grows afterOrdinary current growth history)
        localAvailable currentOrigins currentCovered
termination_by sizeOf expression

/-- Every ordered child preserves real reservation origins through the exact earlier source effects. -/
theorem buildMany_certified [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (origins : Origins pending state) (covered : Covered pending state) :
    Certified pending (buildMany expressions environment state) := by
  cases expressions with
  | nil => simpa only [buildMany, Certified] using And.intro origins covered
  | cons first rest =>
      have head := build_verified first environment state facts inputs
      simp only [buildMany]
      apply bind_certified _ _ (build_certified first environment state facts inputs origins covered) head
      intro value afterHead returned headFacts valueAvailable headOrigins headCovered
      have tailInputs : Values afterHead environment := by
        intro item member
        simpa [returned, Outcome.state] using head.available item (inputs item member)
      apply bind_certified _ _ (buildMany_certified rest environment afterHead headFacts tailInputs headOrigins headCovered)
        (buildMany_verified rest environment afterHead headFacts tailInputs)
      intro values final _ _ _ finalOrigins finalCovered
      exact ⟨finalOrigins, finalCovered⟩
termination_by sizeOf expressions

/-- Nested child and edge execution cannot create an untracked pending request. -/
theorem buildEdges_certified [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state environment) (origins : Origins pending state) (covered : Covered pending state) :
    Certified pending (buildEdges expressions environment state) := by
  cases expressions with
  | nil => simpa only [buildEdges, Certified] using And.intro origins covered
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have childrenBuilt := buildMany_verified children environment state facts inputs
          simp only [buildEdges]
          apply bind_certified _ _ (buildMany_certified children environment state facts inputs origins covered) childrenBuilt
          intro values afterChildren childrenReturned childrenFacts valuesAvailable childrenOrigins childrenCovered
          have edgeBuilt := edge_verified symbol constraint values afterChildren childrenFacts valuesAvailable
          apply bind_certified _ _ (work_certified (makeEdge symbol constraint values) afterChildren childrenFacts.coherent.valid
            childrenOrigins childrenCovered) edgeBuilt
          intro edge afterEdge edgeReturned edgeFacts edgeResident edgeOrigins edgeCovered
          have tailInputs : Values afterEdge environment := by
            intro value member
            have intermediate : Available afterChildren value := by
              simpa [childrenReturned, Outcome.state] using childrenBuilt.available value (inputs value member)
            simpa [edgeReturned, Outcome.state] using edgeBuilt.available value intermediate
          apply bind_certified _ _ (buildEdges_certified rest environment afterEdge edgeFacts tailInputs edgeOrigins edgeCovered)
            (buildEdges_verified rest environment afterEdge edgeFacts tailInputs)
          intro edges final _ _ _ finalOrigins finalCovered
          exact ⟨finalOrigins, finalCovered⟩
termination_by sizeOf expressions
end

/-- Any pending result of arbitrary closed source execution has an actual earlier fresh reservation. -/
theorem closed_pending_origin [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (state : State Symbol Guard) (pending : build expression [] empty = .pending key state) : Origin key state := by
  have certified := build_certified expression [] empty empty_facts
    (by intro value member; cases member) (pending := []) (by intro selected member; cases member) empty_correct.2
  simpa only [pending, Certified] using certified

end MicroCFTA.InternedPendingOrigins
