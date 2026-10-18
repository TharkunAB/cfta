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
  | nil => rfl
  | cons first rest ih =>
      rw [encodeMany,evaluateMany,List.map_cons,
        recapture context first assignment state coherent contextAvailable (available first List.mem_cons_self)
          (fun leaf member => covered leaf (List.mem_append_left _ member)),
        ih (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun leaf member => covered leaf (List.mem_append_right _ member))]

private theorem edge_profiles (context : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (assignment : Reference → Profile) (state : State Symbol Guard) (coherent : Coherent state)
    (contextAvailable : Values state context)
    (available : Values state (edges.flatMap EdgeValue.children))
    (covered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ context) :
    evaluateEdges (encodeEdges context [] edges) (context.map (meaning assignment)) =
      edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) := by
  induction edges with
  | nil => rfl
  | cons first rest ih =>
      cases first with
      | mk entry children =>
          rw [encodeEdges,evaluateEdges,List.any_cons,
            many_profiles context children assignment state coherent contextAvailable
              (fun value member => available value (List.mem_append_left _ member))
              (fun leaf member => covered leaf (List.mem_append_left _ member)),
            ih (fun value member => available value (List.mem_append_right _ member))
              (fun leaf member => covered leaf (List.mem_append_right _ member))]
          simp only [List.all_map,Function.comp_def,EdgeValue.children]

private theorem child_closed (values : List (Value Symbol Guard)) (closed : childFree values = [])
    (value : Value Symbol Guard) (member : value ∈ values) : value.free = [] := by
  cases found : value.free with
  | nil => rfl
  | cons name rest =>
      have selected : name ∈ childFree values := InternedFreshProbeKeys.childFree_member values name |>.mpr
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
              have anyTrue := List.any_eq_true.mpr ⟨child,member,emptyTrue⟩
              rw [firstLive] at anyTrue
              cases anyTrue
            rw [emptyFalse]
            rfl
          simp only [List.any_cons,selected,Bool.true_or]
    rw [SourceCurrentStoredProfileFunction.closed _ assignment closed,positive]
    rfl
  · have opened : (Value.node entry edges depth free).free.isEmpty = false := by
      exact List.isEmpty_eq_false.mpr closed
    have collected : leaves (.node entry edges depth free) = edgeLeaves edges := by
      rw [leaves.eq_def]; simp only [opened,Bool.false_eq_true,ite_false]
    unfold denote
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
  · have opened : (Value.union entry members depth free).free.isEmpty = false := List.isEmpty_eq_false.mpr closed
    have collected : leaves (.union entry members depth free) = manyLeaves members := by
      rw [leaves.eq_def]; simp only [opened,Bool.false_eq_true,ite_false]
    unfold denote
    rw [encode.eq_def]
    simp only [opened,Bool.false_eq_true,ite_false,evaluate]
    rw [many_profiles _ members assignment state normal.facts.coherent
      (InternedStoredSubstitution.leaves_available _ state available)
      (fun child member => available.children child member)
      (fun leaf member => collected ▸ member)]

end MicroCFTA.SourceCurrentStoredProfileComposition
