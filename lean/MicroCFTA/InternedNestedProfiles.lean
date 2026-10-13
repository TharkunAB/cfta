import MicroCFTA.InternedProfileRequest
import MicroCFTA.InternedShallowValues

/-!
# Full source execution derives root profiles and recursive key profiles

The mutual proof follows the complete nested constructor syntax. Both
probes and each fresh body use the recursive proof for their original
expression. Complete hits use the already established table invariant.
The result includes pending executions and has no nesting restriction.
-/
namespace MicroCFTA.InternedNestedProfiles
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedRequestFacts
open InternedNestedMissReadback InternedStoredMuOrigins InternedNestedMuOrigins
open InternedProfileHeap InternedProfileExecutionFacts InternedProfileComposition InternedProfileRequest
open InternedRootProfile InternedProfileEquivalence InternedProfileSemantics InternedFreshProbeKeys
open InternedShallowHeap InternedRootProfileNode InternedRootProfileUnion
open InternedBinderProtocol (Reference)

/-- The actual ordinary constructor tests the profiles of its original edge children. -/
def liveEdges (edges : List (EdgeValue Symbol Guard)) : Bool :=
  edges.any (fun edge => edge.children.all (fun child => !isEmpty (profile child)))

mutual
/-- Every full source execution preserves decoded recursive records and derives its returned root profile. -/
theorem build_profile [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) (heap : InternedProfileHeap.Heap state) :
    Checked (build expression environment state)
      (fun value => Equivalent (profile value) (evaluate expression (environment.map profile))) := by
  cases expression with
  | empty =>
      rw [build]
      apply done_checked _ _ _ heap
      simp [evaluate, profile, Equivalent]
  | var index =>
      rw [build]
      apply done_checked _ _ _ heap
      rw [evaluate]
      cases found : environment[index]? <;> simp [List.getElem?_map, found, profile, Equivalent]
  | node edges =>
      have verified := buildEdges_verified edges environment state normal.facts inputs
      have preserved := buildEdges_normal edges environment state normal inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildEdges_profile edges environment state normal inputs heap)
      intro values after returned afterHeap decision
      have afterNormal : Normal after := by simpa only [returned, Outcome.state] using preserved
      have available := verified.result values after returned
      apply done_checked
      · exact InternedProfileHeap.preserve after _ afterHeap (makeNode_noNewMu values after)
      · rw [makeNode_profile_children values after afterNormal.facts afterNormal.proper available]
        change Equivalent (if liveEdges values then none else some []) (evaluate (.node edges) (environment.map profile))
        rw [decision, evaluate]
        exact refl _
  | union members =>
      have verified := buildMany_verified members environment state normal.facts inputs
      have preserved := buildMany_normal members environment state normal inputs
      rw [build]
      apply bind_checked _ _ _ _ (buildMany_profile members environment state normal inputs heap)
      intro values after returned afterHeap matched
      have afterNormal : Normal after := by simpa only [returned, Outcome.state] using preserved
      have available := verified.result values after returned
      apply done_checked
      · exact InternedProfileHeap.preserve after _ afterHeap (makeUnion_noNewMu values after)
      · rw [evaluate]
        exact trans (makeUnion_profile values after afterNormal.facts afterNormal.live afterNormal.proper available)
          (many_matched matched)
  | binder smart body =>
      have checked : ∀ name current, Normal current → Values current environment → Available current (.reference name) →
          InternedProfileHeap.Heap current → Checked (callback body environment name current)
            (fun value => Equivalent (profile value) (normalize name (evaluate body (some [name] :: environment.map profile)))) := by
        intro name current currentNormal currentInputs argument currentHeap
        have allInputs : Values current (.reference name :: environment) := by
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact argument
          · exact currentInputs value member
        apply callback_checked body environment name current currentNormal allInputs
        simpa only [List.map_cons, profile] using
          build_profile body (.reference name :: environment) current currentNormal allInputs currentHeap
      have depthInputs : Values state (.reference .depth :: environment) := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact depth_available state
        · exact inputs value member
      have depthNormal := callback_normal body environment .depth state normal depthInputs
      have depthVerified := callback_verified body environment .depth state normal.facts depthInputs
      rw [build]
      change Checked ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary) _
      apply bind_checked _ _ _ _ (checked .depth state normal inputs (depth_available state) heap)
      intro depth afterDepth depthDone depthHeap depthSame
      have afterNormal : Normal afterDepth := by simpa only [depthDone, Outcome.state] using depthNormal
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
      apply bind_checked _ _ _ _ (checked (.uninterned depth.depth) afterDepth afterNormal afterInputs
        (ordinary_available afterDepth depth.depth) depthHeap)
      intro ordinary afterOrdinary ordinaryDone ordinaryHeap ordinarySame
      have finalNormal : Normal afterOrdinary := by simpa only [ordinaryDone, Outcome.state] using ordinaryNormal
      have finalInputs : Values afterOrdinary environment := by
        intro value member
        simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available value (afterInputs value member)
      have finalDepth : Available afterOrdinary depth := by
        simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available depth depthAvailable
      have finalOrdinary := ordinaryVerified.result ordinary afterOrdinary ordinaryDone
      exact request_checked smart body environment depth ordinary afterOrdinary finalNormal finalInputs finalDepth finalOrdinary
        ordinaryHeap depthSame ordinarySame checked
termination_by sizeOf expression

/-- Every ordered source child list has exactly the profiles of the pure syntax interpreter. -/
theorem buildMany_profile [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) (heap : InternedProfileHeap.Heap state) :
    Checked (buildMany expressions environment state)
      (fun values => Matches values (evaluateMany expressions (environment.map profile))) := by
  cases expressions with
  | nil =>
      rw [buildMany]
      apply done_checked _ _ _ heap
      rw [evaluateMany]
      exact .nil
  | cons first rest =>
      have verified := build_verified first environment state normal.facts inputs
      have preserved := build_normal first environment state normal inputs
      rw [buildMany]
      apply bind_checked _ _ _ _ (build_profile first environment state normal inputs heap)
      intro value after returned afterHeap same
      have afterNormal : Normal after := by simpa only [returned, Outcome.state] using preserved
      have afterInputs : Values after environment := by
        intro captured member
        simpa only [returned, Outcome.state] using verified.available captured (inputs captured member)
      apply bind_checked _ _ _ _ (buildMany_profile rest environment after afterNormal afterInputs afterHeap)
      intro values final completed finalHeap matched
      apply done_checked _ _ _ finalHeap
      rw [evaluateMany]
      exact .cons same matched
termination_by sizeOf expressions

/-- Source edge construction retains every original abstract live-edge decision. -/
theorem buildEdges_profile [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (normal : Normal state) (inputs : Values state environment) (heap : InternedProfileHeap.Heap state) :
    Checked (buildEdges expressions environment state)
      (fun edges => liveEdges edges = evaluateEdges expressions (environment.map profile)) := by
  cases expressions with
  | nil =>
      rw [buildEdges]
      apply done_checked _ _ _ heap
      simp [liveEdges, evaluateEdges]
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          have verified := buildMany_verified children environment state normal.facts inputs
          have preserved := buildMany_normal children environment state normal inputs
          rw [buildEdges]
          apply bind_checked _ _ _ _ (buildMany_profile children environment state normal inputs heap)
          intro values after returned afterHeap matched
          have afterNormal : Normal after := by simpa only [returned, Outcome.state] using preserved
          have available := verified.result values after returned
          have afterInputs : Values after environment := by
            intro captured member
            simpa only [returned, Outcome.state] using verified.available captured (inputs captured member)
          let edge := run (makeEdge symbol constraint values) after
          have edgeNormal : Normal edge.2 := edge_normal symbol constraint values after afterNormal available
          have edgeVerified := edge_verified symbol constraint values after afterNormal.facts available
          have edgeInputs : Values edge.2 environment := fun captured member => edgeVerified.available captured (afterInputs captured member)
          have edgeHeap : InternedProfileHeap.Heap edge.2 := afterHeap
          have childrenSame : edge.1.children = values := InternedShallowValues.makeEdge_children symbol constraint values after
            afterNormal.facts.coherent afterNormal.facts.cached available
          simp only [work, Outcome.bind]
          change Checked ((buildEdges rest environment edge.2).bind _) _
          apply bind_checked _ _ _ _ (buildEdges_profile rest environment edge.2 edgeNormal edgeInputs edgeHeap)
          intro edges final completed finalHeap same
          apply done_checked _ _ _ finalHeap
          simp only [liveEdges, List.any_cons, evaluateEdges]
          rw [show (run (makeEdge symbol constraint values) after).1.children = values from childrenSame,
            children_matched matched]
          rw [show edges.any (fun edge => edge.children.all (fun child => !isEmpty (profile child))) =
            evaluateEdges rest (environment.map profile) from same]
termination_by sizeOf expressions
end

/-- Actual execution from empty caches establishes every complete stored recursive key profile. -/
theorem closed_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    InternedProfileHeap.Heap (build expression [] empty).state :=
  (build_profile expression [] empty empty_normal (by simp [Values]) InternedProfileHeap.empty_heap).heap

/-- Every completed closed source expression has the profile computed by the complete pure model. -/
theorem closed_profile [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard) (completed : build expression [] empty = .done value state) :
    Equivalent (profile value) (evaluate expression ([] : List Profile)) :=
  (build_profile expression [] empty empty_normal (by simp [Values]) InternedProfileHeap.empty_heap).result value state completed

end MicroCFTA.InternedNestedProfiles
