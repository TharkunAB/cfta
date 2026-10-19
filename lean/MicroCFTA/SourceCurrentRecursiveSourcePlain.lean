import MicroCFTA.SourceCurrentClassRecursiveValueOrigins
import MicroCFTA.SourceCurrentRequiredProjectionOrigins

/-!
# Plain recursive values at an original false gate

Required origins retain the exact recursive value and ordinary child path,
or that value has hereditary plain guards. The original false gate makes
the retained recursive value plain. No gate on a changed value is needed.
This result does not transport an event observation through later edits.
-/
namespace MicroCFTA.SourceCurrentRecursiveSourcePlain
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityAnnotationLanguage EndpointStatefulGateTrace SourceEqualityProjectionGraph
open SourceCurrentRequiredRowOrigins (Origin)
open SourceCurrentClassRecursiveValueOrigins (Occurs)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Recursive" => SourceEqualityRequiredGraph.Recursive
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- A literal ordinary-child occurrence inherits hereditary annotations. -/
theorem annotated {valid : Guard → Prop} {value positions needle}
    (occurrence : Occurs value positions needle) (annotations : Annotated valid value) :
    Annotated valid needle := by
  induction occurrence with
  | root => exact annotations
  | child rowIndex childIndex row child selected chosen rest ih =>
    exact ih ((SourceCurrentHereditaryUnconstrained.node_edge annotations row
      (List.mem_of_getElem? selected)).2 child (List.mem_of_getElem? chosen))

/-- Required origins retain an exact recursive occurrence or make its guards plain. -/
theorem origin {original prepared positions needle}
    (related : Origin original prepared) (occurrence : Occurs prepared positions needle)
    (recursive : Recursive needle) :
    Occurs original positions needle ∨ Annotated Plain needle := by
  induction occurrence generalizing original with
  | root value =>
    cases related with
    | identity => exact .inl (.root _)
    | plain _ _ annotations => exact .inr annotations
    | ordinary _ _ _ _ _ ordinary _ =>
      cases value <;> simp_all [SourceEqualityRequiredGraph.Recursive,SourceEqualityRequiredCache.Ordinary]
  | @child entry edges depth free rowIndex childIndex row child selected chosen path needle rest ih =>
    cases related with
    | identity => exact .inl (.child rowIndex childIndex row child selected chosen rest)
    | plain _ _ annotations =>
      exact .inr (annotated (.child rowIndex childIndex row child selected chosen rest) annotations)
    | ordinary sourceEntry originals level names _ ordinary mapped =>
      obtain ⟨sourceIndex,sourceRow,found,fields,children⟩ := mapped.indexed rowIndex row selected
      have signed : select row.children (Int.ofNat childIndex) = some child := by
        simpa only [select,Int.ofNat_eq_natCast,
          ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg _)),Int.toNat_natCast] using chosen
      obtain ⟨sourceChild,sourceChosen,childOrigin⟩ :=
        SourceEqualityProjectionLanguage.all₂_signed children (Int.ofNat childIndex) child signed
      have natural : sourceRow.children[childIndex]? = some sourceChild := by
        simpa only [select,Int.ofNat_eq_natCast,
          ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg _)),Int.toNat_natCast] using sourceChosen
      rcases ih childOrigin recursive with retained | plain
      · exact .inl (.child sourceIndex childIndex sourceRow sourceChild found natural retained)
      · exact .inr plain

private theorem child_closed {values : List Node} (closed : childFree values = [])
    (value : Node) (member : value ∈ values) : value.free = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name included
  have found := (childFree_member values name).mpr ⟨value,member,included⟩
  rw [closed] at found
  cases found

private theorem finite_excludes {state : Heap} (semantic : SemanticReady state)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal state) {value positions needle}
    (available : Available state value) (occurrence : Occurs value positions needle)
    (zero : value.depth = 0) (closed : value.free = []) (recursive : Recursive needle) : False := by
  induction occurrence with
  | root value =>
    have ordinary := SourceCurrentRequiredFiniteExposure.ordinary_of_zero_closed state semantic normal
      value available zero closed
    cases value <;> simp_all [SourceEqualityRequiredGraph.Recursive,SourceEqualityRequiredCache.Ordinary]
  | @child entry edges depth free rowIndex childIndex row child selected chosen path needle rest ih =>
    have inside : child ∈ edges.flatMap EdgeValue.children :=
      List.mem_flatMap.mpr ⟨row,List.mem_of_getElem? selected,List.mem_of_getElem? chosen⟩
    have bound := InternedUnionSeparation.child_depth state semantic.ready.semantic.1.normal.facts.coherent
      (.node entry edges depth free) child available inside
    have names := InternedNormalizationFree.node_free state semantic.ready.semantic.1.normal.facts.coherent
      entry edges depth free available.resident
    exact ih (available.children child inside) (by rw [zero] at bound; omega)
      (child_closed (names.symm.trans closed) child inside) recursive

section Actual
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem false_edges (index : Nat) (path : EqualityNormalize.Path) (rows : List Row)
    (before after : Heap) (trace : EdgesTrace source reaches index path rows before false after)
    (semantic : SemanticReady before) (available : Values before (rows.flatMap EdgeValue.children))
    (target : Heap) (retained : Grows after target) :
    ∀ row ∈ rows, ChildTrace source reaches row.children index path target false target := by
  induction rows generalizing before with
  | nil => intro row member; cases member
  | cons first rest ih =>
    cases trace with
    | next head tail =>
      have initial := SourceCurrentPrimaryReplay.child_replay source reaches _ _ _ _ _ _ head semantic
        (fun value member => available value (by simp [member]))
      have nextAvailable : Values _ (rest.flatMap EdgeValue.children) :=
        fun value member => initial.2.1.available value (available value (by simp [member]))
      have later := SourceCurrentPrimaryReplay.edges_replay source reaches _ _ _ _ _ _ tail initial.1 nextAvailable
      intro row member
      rcases List.mem_cons.mp member with rfl | included
      · exact initial.2.2 target (grows_trans later.2.1.growth retained)
      · exact ih _ tail initial.1 nextAvailable row included

private theorem false_selected {values : List Node} {index : Nat} {path : EqualityNormalize.Path}
    {value : Node} {before after : Heap}
    (trace : ChildTrace source reaches values index path before false after)
    (found : values[index]? = some value) : NodeTrace source reaches path value before false after := by
  cases trace with
  | missing absent => rw [absent] at found; cases found
  | present selected node =>
    cases Option.some.inj (selected.symm.trans found)
    exact node

private theorem gate_occurrence {anchor : Heap} (semantic : SemanticReady anchor)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal anchor) {value positions needle}
    (available : Available anchor value) (occurrence : Occurs value positions needle)
    (recursive : Recursive needle) (remaining : EqualityNormalize.Path) {before after : Heap}
    (current : SemanticReady before) (resident : Available before value)
    (gate : NodeTrace source reaches (positions ++ remaining) value before false after) :
    Annotated Plain needle := by
  induction occurrence generalizing before after with
  | root value =>
    cases value with
    | empty | reference | node => cases recursive
    | union => cases gate
    | mu entry body depth ordinary =>
      have accepted : source (.mu entry body depth ordinary) = true := by
        cases gate with
        | closed accepted _ => exact accepted
        | unfold accepted _ _ _ => exact accepted
      exact SourceCurrentGatePlainRegion.annotations anchor _
        semantic.ready.semantic.1.normal.facts.coherent available accepted
  | @child entry edges depth free rowIndex childIndex row child selected chosen path needle rest ih =>
    cases gate with
    | finite fast =>
      exact False.elim (finite_excludes semantic normal available
        (.child rowIndex childIndex row child selected chosen rest)
        (by simpa only [Value.depth,beq_iff_eq] using (Bool.and_eq_true_iff.mp fast).1)
        (List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp fast).2) recursive)
    | branches slow scanned =>
      have effects := SourceCurrentPrimaryReplay.edges_replay source reaches childIndex (path ++ remaining)
        edges before false after scanned current (fun child member => resident.children child member)
      have inside : child ∈ edges.flatMap EdgeValue.children :=
        List.mem_flatMap.mpr ⟨row,List.mem_of_getElem? selected,List.mem_of_getElem? chosen⟩
      have traced := false_selected (false_edges childIndex (path ++ remaining) edges before after
        scanned current (fun child member => resident.children child member) after (grows_refl _)
        row (List.mem_of_getElem? selected)) chosen
      exact ih (available.children child inside) recursive effects.1
        (effects.2.1.available child (resident.children child inside)) traced

/-- An original false gate makes every recursive ordinary-path prefix plain. -/
theorem gate {state : Heap} (semantic : SemanticReady state)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal state) {value positions needle}
    (available : Available state value) (occurrence : Occurs value positions needle)
    (recursive : Recursive needle) (remaining : EqualityNormalize.Path) {after : Heap}
    (actual : NodeTrace source reaches (positions ++ remaining) value state false after) :
    Annotated Plain needle :=
  gate_occurrence semantic normal available occurrence recursive remaining semantic available actual

/-- Required preparation and an original false gate make the exact recursive reader value plain. -/
theorem required {state : Heap} (semantic : SemanticReady state)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal state) {original prepared positions needle}
    (available : Available state original) (related : Origin original prepared)
    (occurrence : Occurs prepared positions needle) (recursive : Recursive needle)
    (remaining : EqualityNormalize.Path) {after : Heap}
    (actual : NodeTrace source reaches (positions ++ remaining) original state false after) :
    Annotated Plain needle := by
  rcases origin related occurrence recursive with retained | plain
  · exact gate semantic normal available retained recursive remaining actual
  · exact plain

end Actual
end MicroCFTA.SourceCurrentRecursiveSourcePlain
