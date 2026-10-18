import MicroCFTA.SourceCurrentStoredRootDeletion
import MicroCFTA.SourceCurrentStoredProfileNormalConstruction

/-!
# Original root deletion through actual normal constructors

Node construction retains its ordered child profile test. Deletion does
not enter those children. Union construction preserves deletion of its
original root references through flattening and canonical normalization.
-/
namespace MicroCFTA.SourceCurrentStoredRootDeletionConstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedRootProfile (Profile Equivalent)
open InternedProfileSemantics (combineMany isEmpty)
open InternedBinderProtocol (Reference)
open InternedNestedProvenance (Values Edges)
open InternedStoredMuOrigins (Normal)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredRootDeletion (deleted deletedMany)
open SourceCurrentProfileFold (combine_empty_right fold_append fold_equiv)

private theorem node_deleted [DecidableEq (EdgeKey Symbol Guard)]
    (cuts : Reference → Bool) (edges : List (EdgeValue Symbol Guard)) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (resident : Edges state edges) :
    deleted cuts (run (InternedConstructorTemplates.makeNode edges) state).1 assignment =
      denote (run (InternedConstructorTemplates.makeNode edges) state).1 assignment := by
  cases selected : canonicalEdges (surviving edges) with
  | nil => simp only [InternedConstructorTemplates.makeNode,selected,run,deleted,
      SourceCurrentStoredProfileFunction.empty]
  | cons first rest =>
      obtain ⟨entry,exactValue⟩ := InternedEdgeResidency.identifyNode_readback (first :: rest) state
        normal.facts.coherent normal.facts.linked (by
          intro edge member
          have included : edge ∈ canonicalEdges (surviving edges) := selected ▸ member
          exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge included)).1)
      simp only [InternedConstructorTemplates.makeNode,selected,run]
      rw [exactValue]
      change deleted cuts (.node entry (first :: rest) _ _) assignment = _
      rw [deleted]
      rfl

/-- Actual nodes retain the original ordered child test for every root deletion predicate. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)]
    (cuts : Reference → Bool) (edges : List (EdgeValue Symbol Guard)) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (resident : Edges state edges) :
    deleted cuts (run (InternedConstructorTemplates.makeNode edges) state).1 assignment =
      if edges.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) then none else some [] := by
  rw [node_deleted cuts edges assignment state normal resident]
  exact SourceCurrentStoredProfileNormalConstruction.makeNode edges assignment state normal resident

private theorem folded (cuts : Reference → Bool) (values : List (Value Symbol Guard))
    (assignment : Reference → Profile) :
    deletedMany cuts values assignment = combineMany (values.map (fun value => deleted cuts value assignment)) := by
  induction values with
  | nil => rw [deletedMany]; rfl
  | cons first rest ih => rw [deletedMany,List.map_cons,combineMany,ih]

private theorem members_profile (cuts : Reference → Bool) (value : Value Symbol Guard)
    (assignment : Reference → Profile) :
    combineMany ((unionMembers value).map (fun child => deleted cuts child assignment)) = deleted cuts value assignment := by
  cases value with
  | empty => simp only [unionMembers,List.map_nil,combineMany,deleted]
  | union entry members depth free =>
      rw [unionMembers,deleted]
      exact (folded cuts members assignment).symm
  | reference | node | mu => simp only [unionMembers,List.map_cons,List.map_nil,combineMany,combine_empty_right]

private theorem flatten_profile (cuts : Reference → Bool) (values : List (Value Symbol Guard))
    (assignment : Reference → Profile) :
    combineMany ((values.flatMap unionMembers).map (fun value => deleted cuts value assignment)) =
      combineMany (values.map (fun value => deleted cuts value assignment)) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      rw [List.flatMap_cons,List.map_append,fold_append,members_profile cuts first assignment,ih]
      rfl

private theorem ordinary_profile (cuts : Reference → Bool) (values : List (Value Symbol Guard))
    (edges : List (EdgeValue Symbol Guard)) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (available : Values state values)
    (found : ordinaryEdges values = some edges) :
    combineMany (values.map (fun value => deleted cuts value assignment)) =
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
              rw [List.map_cons,combineMany,deleted,
                SourceCurrentStoredProfileComposition.node entry own depth free assignment state normal (available _ List.mem_cons_self),
                ih later (fun value member => available value (List.mem_cons_of_mem _ member)) tail,List.any_append]
              cases own.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) <;>
                cases later.any (fun edge => edge.children.all (fun child => !isEmpty (denote child assignment))) <;> rfl
      | empty | reference | union | mu => simp [ordinaryEdges] at found

/-- Actual unions preserve deletion observations of the complete original input list. -/
theorem makeUnion [DecidableEq (EdgeKey Symbol Guard)]
    (cuts : Reference → Bool) (values : List (Value Symbol Guard)) (assignment : Reference → Profile)
    (state : State Symbol Guard) (normal : Normal state) (available : Values state values) :
    Equivalent (deleted cuts (run (InternedConstructorTemplates.makeUnion values) state).1 assignment)
      (deletedMany cuts values assignment) := by
  rw [folded cuts values assignment]
  have flatAvailable : Values state (values.flatMap unionMembers) := by
    intro value member
    obtain ⟨original,included,inside⟩ := List.mem_flatMap.mp member
    exact InternedProbeProvenance.unionMembers_available original (available original included) value inside
  have selectedAvailable := InternedUnionFilterFusion.selected_available values state available
  have normalized : Equivalent
      (combineMany ((distinctNodes (values.flatMap unionMembers)).map (fun value => deleted cuts value assignment)))
      (combineMany (values.map (fun value => deleted cuts value assignment))) := by
    rw [←flatten_profile cuts values assignment]
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
      simpa only [InternedConstructorTemplates.makeUnion,selected,run,List.map_nil,combineMany,deleted] using normalized
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
              have exactProfile := ordinary_profile cuts (first :: second :: tail) edges assignment state normal members ordinary
              rw [selected,exactProfile] at normalized
              simpa only [InternedConstructorTemplates.makeUnion,selected,ordinary,
                makeNode cuts edges assignment state normal resident] using normalized
          | none =>
              obtain ⟨entry,shape⟩ := InternedUnionFilterFusion.union_readback values first second tail state normal.facts available selected ordinary
              rw [shape,deleted,folded]
              simpa only [selected] using normalized

end MicroCFTA.SourceCurrentStoredRootDeletionConstruction
