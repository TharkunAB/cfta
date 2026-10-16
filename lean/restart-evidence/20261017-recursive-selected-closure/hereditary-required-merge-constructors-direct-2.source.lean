import MicroCFTA.SourceEqualityAnnotationLanguage
import MicroCFTA.InternedOrdinaryAbsenceReplay
import MicroCFTA.InternedUnionFilterFusion

/-!
# Local annotations through current constructor work

The premises describe only the supplied records. Other resident guards remain
unrestricted. Complete cache readback retains the requested children.
-/
namespace MicroCFTA.SourceCurrentHereditaryConstructors
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedRecordCoherence InternedFreshProbeKeys InternedNestedFacts
open SourceEqualityAnnotationLanguage
variable {Symbol Guard : Type}

/-- A row carries its own guard and the annotations of its actual children. -/
def Edge (valid : Guard → Prop) (edge : EdgeValue Symbol Guard) : Prop :=
  valid edge.entry.key.constraint ∧ ∀ child ∈ edge.children, Annotated valid child

/-- An ordinary row projection reads only annotations present in the supplied value. -/
theorem node_edge {valid : Guard → Prop} {value : Value Symbol Guard}
    (annotated : Annotated valid value) (edge : EdgeValue Symbol Guard)
    (member : edge ∈ nodeEdges value) : Edge valid edge := by
  cases annotated with
  | node entry edges depth free guards children =>
      exact ⟨guards edge member, fun child present => children child (List.mem_flatMap.mpr ⟨edge, member, present⟩)⟩
  | empty | reference | union | mu => cases member

/-- Literal edge work retains the complete requested guard and annotated children. -/
theorem makeEdge [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (available : ∀ value ∈ values, Available state value) (guardValid : valid guard)
    (annotated : ∀ value ∈ values, Annotated valid value) :
    Edge valid (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1 := by
  cases result : (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1 with
  | mk entry children =>
      have key := InternedOrdinaryAbsenceReplay.makeEdge_key symbol guard values state coherent
      have exactChildren := InternedShallowValues.makeEdge_children symbol guard values state coherent cached available
      rw [result] at key exactChildren
      change entry.key = _ at key
      change children = values at exactChildren
      change valid entry.key.constraint ∧ ∀ child ∈ children, Annotated valid child
      rw [key, exactChildren]
      exact ⟨guardValid, annotated⟩

/-- Node normalization selects rows from its actual annotated arguments. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge)
    (annotated : ∀ edge ∈ edges, Edge valid edge) :
    Annotated valid (run (InternedConstructorTemplates.makeNode edges) state).1 := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have validRows : ∀ edge ∈ canonicalEdges (surviving edges), Edge valid edge :=
    fun edge member => annotated edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold InternedConstructorTemplates.makeNode
  dsimp only
  split
  · exact .empty
  · rename_i first rest same
    obtain ⟨entry, exactResult⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa only [same] using selected)
    simp only [run, exactResult, identifyNode]
    apply Annotated.node
    · intro edge member
      exact (validRows edge (by simpa only [same] using member)).1
    · intro child member
      obtain ⟨edge, present, inside⟩ := List.mem_flatMap.mp member
      exact (validRows edge (by simpa only [same] using present)).2 child inside

/-- Concatenating ordinary rows introduces no new annotation. -/
theorem ordinaryUnion [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (available : ∀ value ∈ values, Available state value)
    (annotated : ∀ value ∈ values, Annotated valid value) :
    Annotated valid (run (MergedOrdinaryHeight.ordinaryUnion values) state).1 := by
  apply makeNode valid _ state coherent linked
  · intro edge member
    obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
    exact resident_edges state linked value (available value present).resident edge included
  · intro edge member
    obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
    exact node_edge (annotated value present) edge included

private theorem ordinary_rows (valid : Guard → Prop) (values : List (Value Symbol Guard))
    (edges : List (EdgeValue Symbol Guard)) (annotated : ∀ value ∈ values, Annotated valid value)
    (found : ordinaryEdges values = some edges) : ∀ edge ∈ edges, Edge valid edge := by
  induction values generalizing edges with
  | nil => cases Option.some.inj found; intro edge member; cases member
  | cons value rest ih =>
      cases value <;> simp only [ordinaryEdges] at found
      case node entry rows depth free =>
        cases tail : ordinaryEdges rest with
        | none => simp only [tail, Option.map_none] at found; cases found
        | some later =>
            have same := Option.some.inj (by simpa only [tail, Option.map_some] using found)
            subst edges
            intro edge member
            rcases List.mem_append.mp member with first | last
            · exact node_edge (annotated _ List.mem_cons_self) edge first
            · exact ih later (fun value member => annotated value (List.mem_cons_of_mem _ member)) tail edge last
      all_goals cases found

/-- Flattening union members copies their existing local annotations. -/
theorem union_member (valid : Guard → Prop) (value : Value Symbol Guard)
    (annotated : Annotated valid value) (member : Value Symbol Guard)
    (present : member ∈ unionMembers value) : Annotated valid member := by
  cases annotated with
  | empty => cases present
  | reference name => exact (List.mem_singleton.mp present) ▸ Annotated.reference name
  | node entry edges depth free guards children => exact (List.mem_singleton.mp present) ▸ Annotated.node entry edges depth free guards children
  | union entry members depth free children => exact children member present
  | mu entry body depth ordinary annotated => exact (List.mem_singleton.mp present) ▸ Annotated.mu entry body depth ordinary annotated

/-- Current union normalization retains annotations without a global heap condition. -/
theorem makeUnion [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (available : ∀ value ∈ values, Available state value)
    (annotated : ∀ value ∈ values, Annotated valid value) :
    Annotated valid (run (InternedConstructorTemplates.makeUnion values) state).1 := by
  have selected : ∀ value ∈ distinctNodes (values.flatMap unionMembers), Annotated valid value := by
    intro value member
    obtain ⟨original, present, inside⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact union_member valid original (annotated original present) value inside
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil => simpa only [InternedConstructorTemplates.makeUnion, normalized, run] using (Annotated.empty (valid := valid) (Symbol := Symbol))
  | cons first rest =>
      cases rest with
      | nil => simpa only [InternedConstructorTemplates.makeUnion, normalized, run] using selected first (by simp [normalized])
      | cons second tail =>
          have inputs : ∀ value ∈ first :: second :: tail, Available state value := by
            simpa only [InternedNestedProvenance.Values, normalized] using InternedUnionFilterFusion.selected_available values state available
          have safe : ∀ value ∈ first :: second :: tail, Annotated valid value := by simpa only [normalized] using selected
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | some edges =>
              have resident := ordinaryEdges_resident _ edges state facts.linked (fun value member => (inputs value member).resident) ordinary
              simpa only [InternedConstructorTemplates.makeUnion, normalized, ordinary] using makeNode valid edges state facts.coherent facts.linked resident
                (ordinary_rows valid _ edges safe ordinary)
          | none =>
              obtain ⟨entry, returned⟩ := InternedUnionFilterFusion.union_readback values first second tail state facts available normalized ordinary
              rw [returned]
              exact .union entry _ _ _ safe

end MicroCFTA.SourceCurrentHereditaryConstructors
