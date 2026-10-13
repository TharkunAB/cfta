import MicroCFTA.InternedFreeNameComposition
import MicroCFTA.InternedFreeNameForm
import MicroCFTA.InternedFreeNameRequest

/-!
# Full source free-name semantics and the recursive heap invariant

The mutual proof follows every source constructor and both binder forms.
It uses the actual two probes and fresh body call. Pending outcomes retain
the invariant for every complete recursive record.
-/
namespace MicroCFTA.InternedNestedFreeNames
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedRequestFacts
open InternedNestedMissReadback InternedStoredMuOrigins InternedNestedMuOrigins
open InternedFreeNameComposition InternedFreeNameRequest InternedFreshProbeKeys
open InternedRootProfile
open InternedBinderProtocol (Reference)

mutual
/-- Full source execution preserves decoded free names and computes the pure free-name set. -/
theorem build_free [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment)
    (heap : InternedFreeNameHeap.Heap state) (profileHeap : InternedProfileHeap.Heap state) :
    Checked (build expression environment state)
      (fun value => Same value.free
        (InternedFreeNameSemantics.evaluate expression (environment.map profile) (environment.map Value.free))) := by
  cases expression with
  | empty =>
      rw [build]
      apply done_checked _ _ _ heap
      intro name
      simp [InternedFreeNameSemantics.evaluate, Value.free]
  | var index =>
      rw [build]
      apply done_checked _ _ _ heap
      intro name
      rw [InternedFreeNameSemantics.evaluate]
      cases found : environment[index]? <;> simp [List.getElem?_map, found, Value.free]
  | node edges =>
      have verified := buildEdges_verified edges environment state normal.facts inputs
      have preserved := buildEdges_normal edges environment state normal inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildEdges_free edges environment state normal inputs heap profileHeap)
      intro values after returned afterHeap same
      have afterNormal : Normal after := by simpa only [returned, Outcome.state] using preserved
      have available := verified.result values after returned
      apply done_checked
      · exact InternedFreeNameHeap.preserve after _ afterHeap (InternedShallowHeap.makeNode_noNewMu values after)
      · intro name
        rw [InternedFreeNameSemantics.evaluate]
        exact (node_free values after afterNormal available name).trans (same name)
  | union members =>
      have verified := buildMany_verified members environment state normal.facts inputs
      have preserved := buildMany_normal members environment state normal inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildMany_free members environment state normal inputs heap profileHeap)
      intro values after returned afterHeap matched
      have afterNormal : Normal after := by simpa only [returned, Outcome.state] using preserved
      have available := verified.result values after returned
      apply done_checked
      · exact InternedFreeNameHeap.preserve after _ afterHeap (InternedShallowHeap.makeUnion_noNewMu values after)
      · intro name
        rw [InternedFreeNameSemantics.evaluate]
        exact (union_free values after afterNormal available name).trans (many_matched matched name)
  | binder smart body =>
      let captured := InternedProfileCallbackForm.captures
        (InternedFreeNameForm.symbolic body (environment.map profile) (environment.map Value.free))
      have checked : ∀ name current, Normal current → Values current environment → Available current (.reference name) →
          InternedFreeNameHeap.Heap current → InternedProfileHeap.Heap current →
          Checked (callback body environment name current)
            (fun value => ∀ other, other ≠ name → (other ∈ value.free ↔ other ∈ captured)) := by
        intro name current currentNormal currentInputs argument currentHeap currentProfiles
        have allInputs : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact argument
          · exact currentInputs value member
        apply callback_checked body environment name captured current currentNormal allInputs
        have raw := build_free body (.reference name :: environment) current currentNormal allInputs currentHeap currentProfiles
        refine ⟨raw.heap, ?_⟩
        intro value after returned other different
        have same := raw.result value after returned other
        simp only [List.map_cons, profile, Value.free] at same
        exact same.trans (InternedFreeNameForm.supplied_other body (environment.map profile)
          (environment.map Value.free) name other different)
      have depthInputs : Values state (.reference .depth :: environment) := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact depth_available state
        · exact inputs value member
      have depthNormal := callback_normal body environment .depth state normal depthInputs
      have depthVerified := callback_verified body environment .depth state normal.facts depthInputs
      have depthProfiles := InternedProfileExecutionFacts.callback_checked body environment .depth state normal depthInputs
        (by simpa only [List.map_cons, profile] using
          InternedNestedProfiles.build_profile body (.reference .depth :: environment) state normal depthInputs profileHeap)
      rw [build]
      change Checked ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary) _
      apply bind_checked _ _ _ _ (checked .depth state normal inputs (depth_available state) heap profileHeap)
      intro depth afterDepth depthDone depthHeap depthSame
      have afterNormal : Normal afterDepth := by simpa only [depthDone, Outcome.state] using depthNormal
      have afterProfiles : InternedProfileHeap.Heap afterDepth := by
        simpa only [depthDone, Outcome.state] using depthProfiles.heap
      have afterInputs : Values afterDepth environment := by
        intro value member
        simpa only [depthDone, Outcome.state] using depthVerified.available value (inputs value member)
      have depthAvailable := depthVerified.result depth afterDepth depthDone
      have ordinaryInputs : Values afterDepth (.reference (.uninterned depth.depth) :: environment) := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact ordinary_available afterDepth depth.depth
        · exact afterInputs value member
      have ordinaryNormal := callback_normal body environment (.uninterned depth.depth) afterDepth afterNormal ordinaryInputs
      have ordinaryVerified := callback_verified body environment (.uninterned depth.depth) afterDepth afterNormal.facts ordinaryInputs
      have ordinaryProfiles := InternedProfileExecutionFacts.callback_checked body environment (.uninterned depth.depth)
        afterDepth afterNormal ordinaryInputs (by
          simpa only [List.map_cons, profile] using
          InternedNestedProfiles.build_profile body (.reference (.uninterned depth.depth) :: environment)
            afterDepth afterNormal ordinaryInputs afterProfiles)
      apply bind_checked _ _ _ _ (checked (.uninterned depth.depth) afterDepth afterNormal afterInputs
        (ordinary_available afterDepth depth.depth) depthHeap afterProfiles)
      intro ordinary afterOrdinary ordinaryDone ordinaryHeap ordinarySame
      have finalNormal : Normal afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryNormal
      have finalProfiles : InternedProfileHeap.Heap afterOrdinary := by
        simpa only [ordinaryDone, Outcome.state] using ordinaryProfiles.heap
      have finalInputs : Values afterOrdinary environment := by
        intro value member
        simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available value (afterInputs value member)
      have finalDepth : Available afterOrdinary depth := by
        simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available depth depthAvailable
      have finalOrdinary := ordinaryVerified.result ordinary afterOrdinary ordinaryDone
      have result := request_checked smart body environment depth ordinary captured afterOrdinary finalNormal finalInputs
        finalDepth finalOrdinary ordinaryHeap finalProfiles depthSame ordinarySame checked
      simpa only [InternedFreeNameForm.binder_captures, Same] using result
termination_by sizeOf expression

/-- Every ordered source child list has the free-name sets of the pure interpreter. -/
theorem buildMany_free [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment)
    (heap : InternedFreeNameHeap.Heap state) (profileHeap : InternedProfileHeap.Heap state) :
    Checked (buildMany expressions environment state)
      (fun values => Matches values
        (InternedFreeNameSemantics.evaluateMany expressions (environment.map profile) (environment.map Value.free))) := by
  cases expressions with
  | nil =>
      rw [buildMany]
      apply done_checked _ _ _ heap
      rw [InternedFreeNameSemantics.evaluateMany]
      exact .nil
  | cons first rest =>
      have verified := build_verified first environment state normal.facts inputs
      have preserved := build_normal first environment state normal inputs
      have profiles := InternedNestedProfiles.build_profile first environment state normal inputs profileHeap
      rw [buildMany]
      apply bind_checked _ _ _ _ (build_free first environment state normal inputs heap profileHeap)
      intro value after returned afterHeap same
      have afterNormal : Normal after := by simpa only [returned, Outcome.state] using preserved
      have afterProfiles : InternedProfileHeap.Heap after := by simpa only [returned, Outcome.state] using profiles.heap
      have afterInputs : Values after environment := by
        intro captured member
        simpa only [returned, Outcome.state] using verified.available captured (inputs captured member)
      apply bind_checked _ _ _ _ (buildMany_free rest environment after afterNormal afterInputs afterHeap afterProfiles)
      intro values final completed finalHeap matched
      apply done_checked _ _ _ finalHeap
      rw [InternedFreeNameSemantics.evaluateMany]
      exact .cons same matched
termination_by sizeOf expressions

/-- Source edges retain exactly the free names from their live child lists. -/
theorem buildEdges_free [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment)
    (heap : InternedFreeNameHeap.Heap state) (profileHeap : InternedProfileHeap.Heap state) :
    Checked (buildEdges expressions environment state)
      (fun edges => Same (liveFree edges)
        (InternedFreeNameSemantics.evaluateEdges expressions (environment.map profile) (environment.map Value.free))) := by
  cases expressions with
  | nil =>
      rw [buildEdges]
      apply done_checked _ _ _ heap
      intro name
      simp [liveFree, InternedFreeNameSemantics.evaluateEdges]
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have verified := buildMany_verified children environment state normal.facts inputs
          have preserved := buildMany_normal children environment state normal inputs
          have profiles := InternedNestedProfiles.buildMany_profile children environment state normal inputs profileHeap
          rw [buildEdges]
          apply bind_checked _ _ _ _ (buildMany_free children environment state normal inputs heap profileHeap)
          intro values after returned afterHeap matched
          have afterNormal : Normal after := by simpa only [returned, Outcome.state] using preserved
          have afterProfiles : InternedProfileHeap.Heap after := by simpa only [returned, Outcome.state] using profiles.heap
          have childProfiles := profiles.result values after returned
          have available := verified.result values after returned
          have afterInputs : Values after environment := by
            intro captured member
            simpa only [returned, Outcome.state] using verified.available captured (inputs captured member)
          let edge := run (makeEdge symbol constraint values) after
          have edgeNormal : Normal edge.2 := edge_normal symbol constraint values after afterNormal available
          have edgeVerified := edge_verified symbol constraint values after afterNormal.facts available
          have edgeInputs : Values edge.2 environment := fun captured member => edgeVerified.available captured (afterInputs captured member)
          have edgeHeap : InternedFreeNameHeap.Heap edge.2 := afterHeap
          have edgeProfiles : InternedProfileHeap.Heap edge.2 := afterProfiles
          have childrenSame : edge.1.children = values := InternedShallowValues.makeEdge_children symbol constraint values after
            afterNormal.facts.coherent afterNormal.facts.cached available
          simp only [work, Outcome.bind]
          change Checked ((buildEdges rest environment edge.2).bind _) _
          apply bind_checked _ _ _ _ (buildEdges_free rest environment edge.2 edgeNormal edgeInputs edgeHeap edgeProfiles)
          intro edges final completed finalHeap same
          apply done_checked _ _ _ finalHeap
          intro name
          simp only [liveFree, List.flatMap_cons, InternedFreeNameSemantics.evaluateEdges]
          rw [show (run (makeEdge symbol constraint values) after).1.children = values from childrenSame,
            InternedProfileComposition.children_matched childProfiles]
          simp only [List.mem_append]
          apply or_congr _ (same name)
          split
          · exact many_matched matched name
          · exact Iff.rfl
termination_by sizeOf expressions
end

/-- Empty-cache source execution establishes decoded free names for every complete recursive record. -/
theorem closed_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    InternedFreeNameHeap.Heap (build expression [] empty).state :=
  (build_free expression [] empty empty_normal (by simp [Values])
    InternedFreeNameHeap.empty_heap InternedProfileHeap.empty_heap).heap

/-- A completed closed source expression has exactly the pure interpreter's free-name set. -/
theorem closed_free [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard) (completed : build expression [] empty = .done value state) :
    Same value.free (InternedFreeNameSemantics.evaluate expression [] []) :=
  (build_free expression [] empty empty_normal (by simp [Values])
    InternedFreeNameHeap.empty_heap InternedProfileHeap.empty_heap).result value state completed

end MicroCFTA.InternedNestedFreeNames
