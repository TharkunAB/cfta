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

private theorem combine_empty_right (value : Profile) :
    InternedProfileSemantics.combine value (some []) = value := by
  cases value <;> simp [InternedProfileSemantics.combine]

private theorem combine_assoc (first second third : Profile) :
    InternedProfileSemantics.combine (InternedProfileSemantics.combine first second) third =
      InternedProfileSemantics.combine first (InternedProfileSemantics.combine second third) := by
  cases first <;> cases second <;> cases third <;> simp [InternedProfileSemantics.combine,List.append_assoc]

private theorem fold_append (first second : List Profile) : combineMany (first ++ second) =
    InternedProfileSemantics.combine (combineMany first) (combineMany second) := by
  induction first with
  | nil =>
      cases found : combineMany second <;>
        simp [combineMany,InternedProfileSemantics.combine,found]
  | cons first rest ih => simp only [List.cons_append,combineMany,ih,combine_assoc]

private theorem fold_none (values : List Profile) : combineMany values = none ↔ ∃ value ∈ values, value = none := by
  induction values with
  | nil => simp [combineMany]
  | cons first rest ih =>
      cases first <;> cases restProfile : combineMany rest <;>
        simp_all [combineMany,InternedProfileSemantics.combine]

private theorem fold_member (values : List Profile) (names : List Reference)
    (pure : combineMany values = some names) (name : Reference) :
    name ∈ names ↔ ∃ value ∈ values, name ∈ value.getD [] := by
  induction values generalizing names with
  | nil => simp_all [combineMany]
  | cons first rest ih =>
      cases first with
      | none => simp [combineMany,InternedProfileSemantics.combine] at pure
      | some firstNames =>
          cases restProfile : combineMany rest with
          | none => simp [combineMany,InternedProfileSemantics.combine,restProfile] at pure
          | some restNames =>
              have same : firstNames ++ restNames = names := by
                simpa only [combineMany,restProfile,InternedProfileSemantics.combine,Option.some.injEq] using pure
              subst names
              simp only [List.mem_append,ih restNames restProfile,List.mem_cons,exists_eq_or_imp,Option.getD_some]

private theorem fold_equiv (first second : List Profile) (same : ∀ value, value ∈ first ↔ value ∈ second) :
    Equivalent (combineMany first) (combineMany second) := by
  have opacity : combineMany first = none ↔ combineMany second = none := by
    rw [fold_none,fold_none]
    exact exists_congr fun value => and_congr_left fun _ => same value
  refine ⟨opacity,?_⟩
  intro name
  cases one : combineMany first with
  | none => rw [opacity.mp one]
  | some firstNames =>
      cases two : combineMany second with
      | none => have impossible := opacity.mpr two; simp [one] at impossible
      | some secondNames =>
          simp only [Option.getD_some]
          rw [fold_member first firstNames one,fold_member second secondNames two]
          exact exists_congr fun value => and_congr_left fun _ => same value

private theorem members_profile (value : Value Symbol Guard) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value) :
    combineMany ((unionMembers value).map (fun child => denote child assignment)) = denote value assignment := by
  cases value with
  | empty => simp only [unionMembers,List.map_nil,combineMany,SourceCurrentStoredProfileFunction.empty]
  | union entry members depth free => exact (union entry members depth free assignment state normal available).symm
  | reference | node | mu =>
      simp only [unionMembers,List.map_cons,List.map_nil,combineMany,combine_empty_right]

private theorem flatten_profile (values : List (Value Symbol Guard)) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (available : Values state values) :
    combineMany ((values.flatMap unionMembers).map (fun value => denote value assignment)) =
      combineMany (values.map (fun value => denote value assignment)) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      rw [List.flatMap_cons,List.map_append,fold_append,members_profile first assignment state normal
        (available first List.mem_cons_self),ih (fun value member => available value (List.mem_cons_of_mem _ member))]
      rfl

private theorem ordinary_profile (values : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (assignment : Reference → Profile) (state : State Symbol Guard) (normal : Normal state)
    (available : Values state values) (found : ordinaryEdges values = some edges) :
    combineMany (values.map (fun value => denote value assignment)) =
      if edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) then none else some [] := by
  induction values generalizing edges with
  | nil => cases found; rfl
  | cons first rest ih =>
      cases first with
      | node entry own depth free =>
          cases tail : ordinaryEdges rest with
          | none => simp [ordinaryEdges,tail] at found
          | some later =>
              have shape : own ++ later = edges := by simpa only [ordinaryEdges,tail,Option.map_some,Option.some.injEq] using found
              subst edges
              rw [List.map_cons,combineMany,node entry own depth free assignment state normal (available _ List.mem_cons_self),
                ih later (fun value member => available value (List.mem_cons_of_mem _ member)) tail,List.any_append]
              cases own.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) <;>
                cases later.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) <;> rfl
      | empty | reference | union | mu => simp [ordinaryEdges] at found

/-- Actual union flattening, deduplication and ordinary merging preserve assigned profiles up to sets. -/
theorem makeUnion [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (assignment : Reference → Profile) (state : State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready state)
    (available : Values state values) :
    Equivalent (denote (run (InternedConstructorTemplates.makeUnion values) state).1 assignment)
      (combineMany (values.map (fun value => denote value assignment))) := by
  have normal := ready.semantic.1.normal
  have flatAvailable : Values state (values.flatMap unionMembers) := by
    intro value member
    obtain ⟨original,included,inside⟩ := List.mem_flatMap.mp member
    exact InternedProbeProvenance.unionMembers_available original (available original included) value inside
  have selectedAvailable := InternedUnionFilterFusion.selected_available values state available
  have normalized : Equivalent
      (combineMany ((distinctNodes (values.flatMap unionMembers)).map (fun value => denote value assignment)))
      (combineMany (values.map (fun value => denote value assignment))) := by
    rw [←flatten_profile values assignment state normal available]
    apply fold_equiv
    intro selected
    simp only [List.mem_map]
    apply exists_congr
    intro value
    apply and_congr_left
    intro _
    exact ⟨distinctNodes_member _ value,
      InternedUnionRetention.distinctNodes_retains state normal.facts.coherent _
        (fun child member => (flatAvailable child member).resident) value⟩
  cases selected : distinctNodes (values.flatMap unionMembers) with
  | nil =>
      simpa only [InternedConstructorTemplates.makeUnion,selected,run,List.map_nil,combineMany,
        SourceCurrentStoredProfileFunction.empty] using normalized
  | cons first rest =>
      cases rest with
      | nil =>
          simpa only [InternedConstructorTemplates.makeUnion,selected,run,List.map_cons,List.map_nil,combineMany,
            combine_empty_right] using normalized
      | cons second tail =>
          have members : Values state (first :: second :: tail) := by simpa only [selected] using selectedAvailable
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := InternedEdgeResidency.ordinaryEdges_resident _ edges state normal.facts.linked
                (fun value member => (members value member).resident) ordinary
              have exactProfile := ordinary_profile (first :: second :: tail) edges assignment state normal members ordinary
              rw [selected,exactProfile] at normalized
              simpa only [InternedConstructorTemplates.makeUnion,selected,ordinary,
                makeNode edges assignment state ready resident] using normalized
          | none =>
              obtain ⟨entry,shape⟩ := InternedUnionFilterFusion.union_readback values first second tail state normal.facts available selected ordinary
              have output := (InternedProbeProvenance.makeUnion_available values state normal.facts.coherent normal.facts.cached available).2.2
              have afterNormal := (SourceRecursiveIntersectionSemanticHeap.union values state ready.semantic available).1.normal
              rw [shape,union entry (first :: second :: tail) _ _ assignment _ afterNormal (shape ▸ output)]
              simpa only [selected] using normalized

end MicroCFTA.SourceCurrentStoredProfileComposition
