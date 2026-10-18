import MicroCFTA.SourceCurrentStoredProfilePlan
import MicroCFTA.InternedGuardedProfileSupport
import MicroCFTA.InternedRootProfileUnion

/-!
# Stored profile composition through actual ordinary constructors

Stored child plans use their own captured leaves. Coherent recapture
preserves their assigned profiles. Closed original values retain their
literal profiles. Actual normalization can sort and remove duplicates.
This module makes no source interpretation claim for raw Mu callbacks.
-/
namespace MicroCFTA.SourceCurrentStoredProfileComposition
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution (leaves manyLeaves edgeLeaves encode encodeMany encodeEdges)
open InternedRootProfile (Profile profile Equivalent)
open InternedProfileSemantics (evaluate evaluateMany evaluateEdges combineMany isEmpty)
open InternedNestedProvenance (Values Edges)
open InternedBinderProtocol (Reference)
open InternedStoredMuOrigins (Normal)
open SourceCurrentStoredProfileFunction (denote)

private def meaning (assignment : Reference → Profile) (value : Value Symbol Guard) : Profile :=
  match value with | .reference name => assignment name | _ => profile value

private theorem recapture (context : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (assignment : Reference → Profile) (state : State Symbol Guard) (coherent : Coherent state)
    (contextAvailable : Values state context) (available : Available state value)
    (covered : ∀ leaf ∈ leaves value, leaf ∈ context) :
    evaluate (encode context [] value) (context.map (meaning assignment)) = denote value assignment :=
  SourceCurrentStoredProfilePlan.recapture context value (meaning assignment) state coherent contextAvailable available covered

private theorem many_profiles (context values : List (Value Symbol Guard)) (assignment : Reference → Profile)
    (state : State Symbol Guard) (coherent : Coherent state) (contextAvailable : Values state context)
    (available : Values state values) (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context) :
    evaluateMany (encodeMany context [] values) (context.map (meaning assignment)) =
      values.map (fun value => denote value assignment) := by
  induction values with
  | nil => simp only [encodeMany,evaluateMany,List.map_nil]
  | cons first rest ih =>
      rw [encodeMany,evaluateMany,List.map_cons,
        recapture context first assignment state coherent contextAvailable (available first List.mem_cons_self)
          (fun leaf member => covered leaf (by simpa only [manyLeaves] using List.mem_append_left (manyLeaves rest) member)),
        ih (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun leaf member => covered leaf (by simpa only [manyLeaves] using List.mem_append_right (leaves first) member))]

private theorem edge_profiles (context : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (assignment : Reference → Profile) (state : State Symbol Guard) (coherent : Coherent state)
    (contextAvailable : Values state context)
    (available : Values state (edges.flatMap EdgeValue.children))
    (covered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ context) :
    evaluateEdges (encodeEdges context [] edges) (context.map (meaning assignment)) =
      edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) := by
  induction edges with
  | nil => simp only [encodeEdges,evaluateEdges,List.any_nil]
  | cons first rest ih =>
      cases first with
      | mk entry children =>
          rw [encodeEdges,evaluateEdges,List.any_cons,
            many_profiles context children assignment state coherent contextAvailable
              (fun value member => available value (List.mem_append_left _ member))
              (fun leaf member => covered leaf (by simpa only [edgeLeaves] using List.mem_append_left (edgeLeaves rest) member)),
            ih (fun value member => available value (List.mem_append_right _ member))
              (fun leaf member => covered leaf (by simpa only [edgeLeaves] using List.mem_append_right (manyLeaves children) member))]
          simp only [List.all_map,Function.comp_def,EdgeValue.children]

private theorem child_closed (values : List (Value Symbol Guard)) (closed : childFree values = [])
    (value : Value Symbol Guard) (member : value ∈ values) : value.free = [] := by
  cases found : value.free with
  | nil => rfl
  | cons name rest =>
      have selected : name ∈ childFree values := childFree_member values name |>.mpr
        ⟨value,member,by rw [found]; exact List.mem_cons_self⟩
      rw [closed] at selected
      cases selected

/-- A resident ordinary value interprets its exact ordered child profiles, including closed originals. -/
theorem node (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List Reference) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state (.node entry edges depth free)) :
    denote (.node entry edges depth free) assignment =
      if edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) then none else some [] := by
  by_cases closed : (Value.node entry edges depth free).free = []
  · have allClosed : ∀ child ∈ edges.flatMap EdgeValue.children, child.free = [] := by
      apply child_closed
      simpa only [Value.free,InternedNormalizationFree.node_free state normal.facts.coherent entry edges depth free available.resident] using closed
    have nonempty := InternedNonemptyRecords.resident_nonempty state normal.proper _ available.resident
    have live := InternedLiveEdges.resident_live state normal.live _ available.resident
    have positive : edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) = true := by
      cases edges with
      | nil => exact False.elim (nonempty rfl)
      | cons first rest =>
          have firstLive := live first List.mem_cons_self
          have selected : first.children.all (fun child => !isEmpty (denote child assignment)) = true := by
            apply List.all_eq_true.mpr
            intro child member
            rw [SourceCurrentStoredProfileFunction.closed child assignment
              (allClosed child (List.mem_flatMap.mpr ⟨first,List.mem_cons_self,member⟩)),
              InternedRootProfileNode.isEmpty_profile child state normal.proper
                (available.children child (List.mem_flatMap.mpr ⟨first,List.mem_cons_self,member⟩))]
            have emptyFalse : (child.referenceOf == .empty) = false := by
              apply Bool.eq_false_iff.mpr
              intro emptyTrue
              have anyTrue : first.children.any (fun child => child.referenceOf == .empty) = true :=
                List.any_eq_true.mpr ⟨child,member,emptyTrue⟩
              rw [firstLive] at anyTrue
              cases anyTrue
            rw [emptyFalse]
            rfl
          simp only [List.any_cons,selected,Bool.true_or]
    rw [SourceCurrentStoredProfileFunction.closed _ assignment closed,positive]
    simp only [profile,ite_true]
  · have opened : (Value.node entry edges depth free).free.isEmpty = false := by
      exact Bool.eq_false_iff.mpr (fun h => closed (List.isEmpty_iff.mp h))
    have collected : leaves (.node entry edges depth free) = edgeLeaves edges := by
      rw [leaves.eq_def]; simp only [opened,Bool.false_eq_true,ite_false]
    change evaluate (encode (leaves (.node entry edges depth free)) [] (.node entry edges depth free))
      ((leaves (.node entry edges depth free)).map (meaning assignment)) = _
    rw [encode.eq_def]
    simp only [opened,Bool.false_eq_true,ite_false,evaluate]
    rw [edge_profiles _ edges assignment state normal.facts.coherent
      (InternedStoredSubstitution.leaves_available _ state available)
      (fun child member => available.children child member)
      (fun leaf member => collected ▸ member)]

/-- A resident union combines its actual member profiles, including closed originals. -/
theorem union (entry : Interned InternedBinderProtocol.NodeKey) (members : List (Value Symbol Guard))
    (depth : Nat) (free : List Reference) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state (.union entry members depth free)) :
    denote (.union entry members depth free) assignment = combineMany (members.map (fun value => denote value assignment)) := by
  by_cases closed : (Value.union entry members depth free).free = []
  · have allClosed : ∀ child ∈ members, child.free = [] := by
      apply child_closed
      simpa only [Value.free,InternedNormalizationFree.union_free state normal.facts.coherent entry members depth free available.resident] using closed
    rw [SourceCurrentStoredProfileFunction.closed _ assignment closed,profile,
      InternedGuardedProfileSupport.many_profiles]
    congr 1
    apply List.map_congr_left
    intro value member
    exact (SourceCurrentStoredProfileFunction.closed value assignment (allClosed value member)).symm
  · have opened : (Value.union entry members depth free).free.isEmpty = false :=
      Bool.eq_false_iff.mpr (fun h => closed (List.isEmpty_iff.mp h))
    have collected : leaves (.union entry members depth free) = manyLeaves members := by
      rw [leaves.eq_def]; simp only [opened,Bool.false_eq_true,ite_false]
    change evaluate (encode (leaves (.union entry members depth free)) [] (.union entry members depth free))
      ((leaves (.union entry members depth free)).map (meaning assignment)) = _
    rw [encode.eq_def]
    simp only [opened,Bool.false_eq_true,ite_false,evaluate]
    rw [many_profiles _ members assignment state normal.facts.coherent
      (InternedStoredSubstitution.leaves_available _ state available)
      (fun child member => available.children child member)
      (fun leaf member => collected ▸ member)]

private theorem future_survives (edge : EdgeValue Symbol Guard) (assignment : Reference → Profile)
    (future : edge.children.all (fun child => !isEmpty (denote child assignment)) = true) :
    edge.children.any (fun child => child.referenceOf == .empty) = false := by
  apply Bool.eq_false_iff.mpr
  intro selected
  obtain ⟨child,member,emptyTrue⟩ := List.any_eq_true.mp selected
  have emptyChild := (InternedEmptyNormalization.reference_empty child).mp (eq_of_beq emptyTrue)
  have later := List.all_eq_true.mp future child member
  rw [emptyChild,SourceCurrentStoredProfileFunction.empty] at later
  cases later

/-- Actual node normalization retains exactly the assigned future live-row decision. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (assignment : Reference → Profile) (state : State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready state)
    (resident : Edges state edges) :
    denote (run (InternedConstructorTemplates.makeNode edges) state).1 assignment =
      if edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) then none else some [] := by
  have normal := ready.semantic.1.normal
  have selectedResident : Edges state (canonicalEdges (surviving edges)) := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have same : (canonicalEdges (surviving edges)).any
      (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) =
      edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true,List.any_eq_true]
    constructor
    · rintro ⟨edge,member,live⟩
      exact ⟨edge,(List.mem_filter.mp (canonicalEdges_member _ edge member)).1,live⟩
    · rintro ⟨edge,member,live⟩
      have survives : edge ∈ surviving edges := by
        simp only [surviving,List.mem_filter]
        exact ⟨member,by rw [future_survives edge assignment live]; rfl⟩
      exact ⟨edge,InternedEdgeResidency.canonicalEdges_retains state normal.facts.coherent _ edge
        (fun value included => resident value (List.mem_filter.mp included).1) survives,live⟩
  have checked := InternedNestedFacts.node_verified edges state normal.facts resident
  have output := checked.result _ _ rfl
  have afterNormal := (SourceRecursiveIntersectionSemanticHeap.node edges state ready.semantic resident).1.normal
  cases normalized : canonicalEdges (surviving edges) with
  | nil =>
      have noRows : edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) = false := by
        simpa only [normalized,List.any_nil] using same.symm
      simp only [InternedConstructorTemplates.makeNode,normalized,run,SourceCurrentStoredProfileFunction.empty,noRows]
      rfl
  | cons first rest =>
      obtain ⟨entry,exactValue⟩ := InternedEdgeResidency.identifyNode_readback (first :: rest) state
        normal.facts.coherent normal.facts.linked (by
          intro edge member
          exact selectedResident edge (normalized ▸ member))
      have shape : (run (InternedConstructorTemplates.makeNode edges) state).1 = identifyNode (first :: rest) entry := by
        simpa only [InternedConstructorTemplates.makeNode,normalized,run] using exactValue
      have available : Available (run (InternedConstructorTemplates.makeNode edges) state).2 (identifyNode (first :: rest) entry) := shape ▸ output
      rw [shape]
      change denote (.node entry (first :: rest) _ _) assignment = _
      rw [node entry (first :: rest) _ _ assignment _ afterNormal available]
      rw [←same,normalized]

end MicroCFTA.SourceCurrentStoredProfileComposition
