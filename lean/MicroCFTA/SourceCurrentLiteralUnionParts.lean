import MicroCFTA.SourceCurrentLiteralRootParts
import MicroCFTA.InternedUnionFilterFusion
import MicroCFTA.InternedStoredPlanBinderDepthExact

/-!
# Literal root parts of actual union normalization

Literal atoms and ordinary rows pass only through root unions. Mu bodies
remain opaque. Actual flattening, identity selection, complete cache readback,
and live ordinary-row normalization retain exactly these source parts.
-/
namespace MicroCFTA.SourceCurrentLiteralUnionParts
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts (Facts)
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency InternedLiveEdges InternedUnionRetention InternedUnionDescendants
open InternedUnionFilterFusion
open SourceCurrentLiteralRootParts (Literal Row)

private theorem flatten_literal (value atom : Value Symbol Guard) :
    (∃ member ∈ unionMembers value, Literal member atom) ↔ Literal value atom := by
  cases value with
  | empty =>
      constructor
      · rintro ⟨member,present,_⟩; cases present
      · intro impossible; cases impossible
  | reference | node | mu => simp only [unionMembers,List.mem_singleton,exists_eq_left]
  | union entry members level free =>
      exact (SourceCurrentLiteralRootParts.literal_union entry members level free atom).symm

private theorem flatten_row (value : Value Symbol Guard) (row : EdgeValue Symbol Guard) :
    (∃ member ∈ unionMembers value, Row member row) ↔ Row value row := by
  cases value with
  | empty =>
      constructor
      · rintro ⟨member,present,_⟩; cases present
      · intro impossible; cases impossible
  | reference | node | mu => simp only [unionMembers,List.mem_singleton,exists_eq_left]
  | union entry members level free =>
      exact (SourceCurrentLiteralRootParts.row_union entry members level free row).symm

private theorem selected (state : State Symbol Guard) (facts : Facts state)
    (values : List (Value Symbol Guard)) (available : Values state values)
    (predicate : Value Symbol Guard → Prop)
    (flatten : ∀ value, (∃ member ∈ unionMembers value, predicate member) ↔ predicate value) :
    (∃ member ∈ distinctNodes (values.flatMap unionMembers), predicate member) ↔
      ∃ value ∈ values, predicate value := by
  have flatAvailable : Values state (values.flatMap unionMembers) := by
    intro value member
    obtain ⟨source,present,included⟩ := List.mem_flatMap.mp member
    exact unionMembers_available source (available source present) value included
  constructor
  · rintro ⟨member,present,part⟩
    obtain ⟨source,original,included⟩ := List.mem_flatMap.mp (distinctNodes_member _ member present)
    exact ⟨source,original,(flatten source).mp ⟨member,included,part⟩⟩
  · rintro ⟨source,present,part⟩
    obtain ⟨member,included,part⟩ := (flatten source).mpr part
    exact ⟨member,distinctNodes_retains state facts.coherent _
      (fun value included => (flatAvailable value included).resident) member
      (List.mem_flatMap.mpr ⟨source,present,included⟩),part⟩

private theorem ordinary_no_literal (values : List (Value Symbol Guard))
    (edges : List (EdgeValue Symbol Guard)) (found : ordinaryEdges values = some edges)
    (atom : Value Symbol Guard) : ¬ ∃ value ∈ values, Literal value atom := by
  rintro ⟨value,present,part⟩
  obtain ⟨entry,own,level,free,shape,_⟩ := ordinaryEdges_contains values edges found value present
  rw [shape] at part
  cases part

private theorem node_no_literal [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (facts : Facts state) (edges : List (EdgeValue Symbol Guard))
    (resident : Edges state edges) (atom : Value Symbol Guard) :
    ¬ Literal (run (makeNode edges) state).1 atom := by
  have inputs : Edges state (canonicalEdges (surviving edges)) :=
    fun row member => resident row (List.mem_filter.mp (canonicalEdges_member _ row member)).1
  cases kept : canonicalEdges (surviving edges) with
  | nil =>
      simp only [makeNode,kept,run]
      intro impossible
      cases impossible
  | cons first rest =>
      obtain ⟨entry,readback⟩ := identifyNode_readback (first::rest) state facts.coherent facts.linked
        (by simpa only [Edges,kept] using inputs)
      simp only [makeNode,kept,run,readback,identifyNode]
      intro impossible
      cases impossible

private theorem ordinary_rows (values : List (Value Symbol Guard))
    (edges : List (EdgeValue Symbol Guard)) (found : ordinaryEdges values = some edges)
    (row : EdgeValue Symbol Guard) : row ∈ edges ↔ ∃ value ∈ values, Row value row := by
  induction values generalizing edges with
  | nil => cases found; simp
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at found <;> try contradiction
      rename_i entry own level free
      cases tail : ordinaryEdges rest with
      | none => simp [tail] at found
      | some later =>
          have same : own ++ later = edges := by simpa only [tail,Option.map_some,Option.some.injEq] using found
          subst edges
          simp only [List.mem_append,List.mem_cons]
          constructor
          · rintro (present | present)
            · exact ⟨_,Or.inl rfl,(SourceCurrentLiteralRootParts.row_node entry own level free row).mpr present⟩
            · obtain ⟨value,present,part⟩ := (ih later tail).mp present
              exact ⟨value,Or.inr present,part⟩
          · rintro ⟨value,same | present,part⟩
            · subst value
              exact Or.inl ((SourceCurrentLiteralRootParts.row_node entry own level free row).mp part)
            · exact Or.inr ((ih later tail).mpr ⟨value,present,part⟩)

private theorem node_rows [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (facts : Facts state) (edges : List (EdgeValue Symbol Guard))
    (resident : Edges state edges) (live : surviving edges = edges) (row : EdgeValue Symbol Guard) :
    Row (run (makeNode edges) state).1 row ↔ row ∈ edges := by
  have exactRows : row ∈ canonicalEdges (surviving edges) ↔ row ∈ edges := by
    rw [live]
    exact ⟨canonicalEdges_member edges row,canonicalEdges_retains state facts.coherent edges row resident⟩
  rw [←exactRows]
  have inputs : Edges state (canonicalEdges (surviving edges)) :=
    fun row member => resident row (List.mem_filter.mp (canonicalEdges_member _ row member)).1
  cases kept : canonicalEdges (surviving edges) with
  | nil =>
      simp only [makeNode,kept,run,List.not_mem_nil]
      constructor
      · intro impossible; cases impossible
      · intro impossible; cases impossible
  | cons first rest =>
      obtain ⟨entry,readback⟩ := identifyNode_readback (first::rest) state facts.coherent facts.linked
        (by simpa only [Edges,kept] using inputs)
      simp only [makeNode,kept,run,readback,identifyNode]
      exact SourceCurrentLiteralRootParts.row_node entry _ _ _ row

/-- Actual union normalization retains exactly the literal reference and whole-Mu atoms of its original inputs. -/
theorem literal [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (facts : Facts state) (values : List (Value Symbol Guard)) (available : Values state values)
    (atom : Value Symbol Guard) :
    Literal (run (makeUnion values) state).1 atom ↔ ∃ value ∈ values, Literal value atom := by
  rw [←selected state facts values available (fun value => Literal value atom) (fun value => flatten_literal value atom)]
  cases chosen : distinctNodes (values.flatMap unionMembers) with
  | nil =>
      simp only [makeUnion,chosen,run,List.not_mem_nil,false_and,exists_false]
      constructor
      · intro impossible; cases impossible
      · intro impossible; cases impossible
  | cons first rest =>
      cases rest with
      | nil => simp only [makeUnion,chosen,run,List.mem_singleton,exists_eq_left]
      | cons second tail =>
          cases ordinary : ordinaryEdges (first::second::tail) with
          | none =>
              obtain ⟨entry,readback⟩ := union_readback values first second tail state facts available chosen ordinary
              rw [readback]
              exact SourceCurrentLiteralRootParts.literal_union entry _ _ _ atom
          | some edges =>
              have inputs : Values state (first::second::tail) := by
                simpa only [chosen] using selected_available values state available
              have resident := ordinaryEdges_resident _ edges state facts.linked
                (fun value member => (inputs value member).resident) ordinary
              simp only [makeUnion,chosen,ordinary]
              exact iff_of_false (node_no_literal state facts edges resident atom)
                (ordinary_no_literal _ edges ordinary atom)

/-- Actual union normalization retains exactly the complete ordinary root rows of its original inputs. -/
theorem row [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (facts : Facts state) (live : Live state) (values : List (Value Symbol Guard)) (available : Values state values)
    (output : EdgeValue Symbol Guard) :
    Row (run (makeUnion values) state).1 output ↔ ∃ value ∈ values, Row value output := by
  rw [←selected state facts values available (fun value => Row value output) (fun value => flatten_row value output)]
  cases chosen : distinctNodes (values.flatMap unionMembers) with
  | nil =>
      simp only [makeUnion,chosen,run,List.not_mem_nil,false_and,exists_false]
      constructor
      · intro impossible; cases impossible
      · intro impossible; cases impossible
  | cons first rest =>
      cases rest with
      | nil => simp only [makeUnion,chosen,run,List.mem_singleton,exists_eq_left]
      | cons second tail =>
          cases ordinary : ordinaryEdges (first::second::tail) with
          | none =>
              obtain ⟨entry,readback⟩ := union_readback values first second tail state facts available chosen ordinary
              rw [readback]
              exact SourceCurrentLiteralRootParts.row_union entry _ _ _ output
          | some edges =>
              have inputs : Values state (first::second::tail) := by
                simpa only [chosen] using selected_available values state available
              have resident := ordinaryEdges_resident _ edges state facts.linked
                (fun value member => (inputs value member).resident) ordinary
              have retained := InternedStoredPlanBinderDepth.ordinaryEdges_surviving _ edges state live inputs ordinary
              simp only [makeUnion,chosen,ordinary]
              exact (node_rows state facts edges resident retained output).trans
                (ordinary_rows _ edges ordinary output)

end MicroCFTA.SourceCurrentLiteralUnionParts
