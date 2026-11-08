import MicroCFTA.SourceSynthesisTypePathRoles
import MicroCFTA.InternedEdgeResidency

/-!
# Annotated first fields through actual constructors

Node normalization retains the complete selected row records. Empty and
ordinary union operands flatten to ordinary records only. Their actual
union request therefore uses its empty, singleton, or ordinary-node branch.
The proofs retain first-writer cache readback. They do not classify symbols.
-/
namespace MicroCFTA.SourceSynthesisAnnotationFieldConstructors
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields)
variable {Symbol Guard : Type}

/-- Actual node pruning and cache readback retain the annotated first fields. -/
theorem makeNode_fields [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (resident : Edges state edges)
    (typed : ∀ edge ∈ edges, ∀ value, edge.children[0]? = some value → Annotated valid value) :
    AnnotationFields valid (run (makeNode edges) state).1 := by
  have selected : Edges state (canonicalEdges (surviving edges)) :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  have selectedTyped : ∀ edge ∈ canonicalEdges (surviving edges),
      ∀ value, edge.children[0]? = some value → Annotated valid value :=
    fun edge member => typed edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · exact .empty
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (by simpa [InternedNestedProvenance.Edges, same] using selected)
    simp only [run, readback, identifyNode]
    exact .node _ _ _ _ (by simpa [same] using selectedTyped)

private theorem ordinary_fields (valid : Guard → Prop) (values : List (Value Symbol Guard))
    (nodes : ∀ value ∈ values,
      ∃ entry rows depth free, value = .node entry rows depth free ∧
        ∀ edge ∈ rows, ∀ child, edge.children[0]? = some child → Annotated valid child) :
    ∃ edges, ordinaryEdges values = some edges ∧
      ∀ edge ∈ edges, ∀ child, edge.children[0]? = some child → Annotated valid child := by
  induction values with
  | nil => exact ⟨[], rfl, by intro edge member; cases member⟩
  | cons value values ih =>
      obtain ⟨entry, rows, depth, free, same, typed⟩ := nodes value List.mem_cons_self
      subst value
      obtain ⟨remaining, read, tailTyped⟩ := ih
        (fun value member => nodes value (List.mem_cons_of_mem _ member))
      refine ⟨rows ++ remaining, ?_, ?_⟩
      · simp only [ordinaryEdges, read, Option.map_some]
      · intro edge member child found
        rcases List.mem_append.mp member with first | rest
        · exact typed edge first child found
        · exact tailTyped edge rest child found

/-- Actual union normalization stays empty or ordinary and retains the first fields. -/
theorem makeUnion_fields [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (available : Values state values)
    (fields : ∀ value ∈ values, AnnotationFields valid value) :
    AnnotationFields valid (run (makeUnion values) state).1 := by
  have allAvailable : Values state (distinctNodes (values.flatMap unionMembers)) := by
    intro value member
    obtain ⟨source, included, present⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    exact unionMembers_available source (available source included) value present
  have allNodes : ∀ value ∈ distinctNodes (values.flatMap unionMembers),
      ∃ entry rows depth free, value = .node entry rows depth free ∧
        ∀ edge ∈ rows, ∀ child, edge.children[0]? = some child → Annotated valid child := by
    intro value member
    obtain ⟨source, included, present⟩ := List.mem_flatMap.mp (distinctNodes_member _ value member)
    have shape := fields source included
    cases shape with
    | empty => simp only [unionMembers, List.not_mem_nil] at present
    | node entry rows depth free typed =>
        exact ⟨entry, rows, depth, free, List.mem_singleton.mp present, typed⟩
  cases normalized : distinctNodes (values.flatMap unionMembers) with
  | nil =>
      simpa only [makeUnion, normalized, run] using (AnnotationFields.empty (valid := valid) (Symbol := Symbol))
  | cons first rest =>
      cases rest with
      | nil =>
          obtain ⟨entry, rows, depth, free, same, typed⟩ := allNodes first (by simp [normalized])
          have firstFields : AnnotationFields valid first := by
            rw [same]
            exact .node entry rows depth free typed
          simpa only [makeUnion, normalized, run] using firstFields
      | cons second tail =>
          have inputs : Values state (first :: second :: tail) := by
            intro value member
            exact allAvailable value (by simpa only [normalized] using member)
          have nodes : ∀ value ∈ first :: second :: tail,
              ∃ entry rows depth free, value = .node entry rows depth free ∧
                ∀ edge ∈ rows, ∀ child, edge.children[0]? = some child → Annotated valid child := by
            simpa only [normalized] using allNodes
          obtain ⟨edges, ordinary, typed⟩ := ordinary_fields valid _ nodes
          have resident := ordinaryEdges_resident _ edges state facts.linked
            (fun value member => (inputs value member).resident) ordinary
          simpa only [makeUnion, normalized, ordinary] using makeNode_fields valid edges state facts resident typed

end MicroCFTA.SourceSynthesisAnnotationFieldConstructors
