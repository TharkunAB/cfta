import MicroCFTA.SourceCurrentStoredProfileComposition
import MicroCFTA.SourceCurrentProfileFold

/-!
# Assigned profiles through normal ordinary construction

Actual ordinary construction needs the primitive normalization invariants.
It does not need the recursive semantic heaps in Ready.
-/
namespace MicroCFTA.SourceCurrentStoredProfileNormalConstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedRootProfile (Profile Equivalent)
open InternedProfileSemantics (isEmpty combineMany)
open InternedBinderProtocol (Reference)
open InternedNestedProvenance (Values Edges)
open InternedStoredMuOrigins (Normal)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentProfileFold (combine_empty_right fold_append fold_equiv)

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
    (assignment : Reference → Profile) (state : State Symbol Guard) (normal : Normal state)
    (resident : Edges state edges) :
    denote (run (InternedConstructorTemplates.makeNode edges) state).1 assignment =
      if edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) then none else some [] := by
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
  have afterNormal : Normal (run (InternedConstructorTemplates.makeNode edges) state).2 :=
    ⟨checked.facts,
      InternedLiveEdges.makeNode_live edges state normal.live,
      InternedUnionNormalForm.makeNode_flat edges state normal.flat,
      InternedNonemptyRecords.makeNode_nonempty edges state normal.proper,
      InternedUnionNonemptyMembers.makeNode_membersNonempty edges state normal.members⟩
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
      rw [SourceCurrentStoredProfileComposition.node entry (first :: rest) _ _ assignment _ afterNormal available]
      rw [←same,normalized]


private theorem members_profile (value : Value Symbol Guard) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state value) :
    combineMany ((unionMembers value).map (fun child => denote child assignment)) = denote value assignment := by
  cases value with
  | empty => simp only [unionMembers,List.map_nil,combineMany,SourceCurrentStoredProfileFunction.empty]
  | union entry members depth free => exact (SourceCurrentStoredProfileComposition.union entry members depth free assignment state normal available).symm
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
              rw [List.map_cons,combineMany,SourceCurrentStoredProfileComposition.node entry own depth free assignment state normal (available _ List.mem_cons_self),
                ih later (fun value member => available value (List.mem_cons_of_mem _ member)) tail,List.any_append]
              cases own.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) <;>
                cases later.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) <;> rfl
      | empty | reference | union | mu => simp [ordinaryEdges] at found

/-- Actual union flattening, deduplication and ordinary merging preserve assigned profiles up to sets. -/
theorem makeUnion [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (assignment : Reference → Profile) (state : State Symbol Guard) (normal : Normal state)
    (available : Values state values) :
    Equivalent (denote (run (InternedConstructorTemplates.makeUnion values) state).1 assignment)
      (combineMany (values.map (fun value => denote value assignment))) := by
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
                makeNode edges assignment state normal resident] using normalized
          | none =>
              obtain ⟨entry,shape⟩ := InternedUnionFilterFusion.union_readback values first second tail state normal.facts available selected ordinary
              have output := (InternedProbeProvenance.makeUnion_available values state normal.facts.coherent normal.facts.cached available).2.2
              have afterNormal : Normal (run (InternedConstructorTemplates.makeUnion values) state).2 :=
                ⟨(InternedNestedFacts.union_verified values state normal.facts available).facts,
                  InternedLiveEdges.makeUnion_live values state normal.live,
                  InternedUnionNormalForm.makeUnion_flat values state normal.flat available,
                  InternedNonemptyRecords.makeUnion_nonempty values state normal.proper,
                  InternedUnionNonemptyMembers.makeUnion_membersNonempty values state normal.members available⟩
              rw [shape,SourceCurrentStoredProfileComposition.union entry (first :: second :: tail) _ _ assignment _ afterNormal (shape ▸ output)]
              simpa only [selected] using normalized


end MicroCFTA.SourceCurrentStoredProfileNormalConstruction
