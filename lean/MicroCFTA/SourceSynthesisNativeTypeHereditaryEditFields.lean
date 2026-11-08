import MicroCFTA.SourceSynthesisHereditaryProgramFields
import MicroCFTA.SourceSynthesisNativeTypeSharedEdit

/-!
# Recursive Program fields through actual annotation-only shared edits

Only child zero can have an edit. Every later child and its remaining
state follow the literal unselected branches. The first Type field retains
its annotation through the actual Type route. Row reconstruction retains
the complete source symbol and guard. Actual node normalization retains
the recursive row certificates. These are completed local execution laws.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeHereditaryEditFields
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityProjectionGraph (select)
open SourceEqualityEdits (Edits)
open SourceCurrentHereditaryTypePaths (TypePath ForestPath)
open SourceCurrentHereditaryTypeEditPlan
open SourceCurrentHereditaryTypeRouteConstructors (ForestRoutes route_nil)
open SourceCurrentEditDomains (Populated HasLeaf)
open SourceCurrentAllocatedSharedEditGraph
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem tail_identity {record originals entries offset inputs before outputs after}
    (actual : EditChildren (width := width) record originals entries offset inputs before outputs after)
    (only : ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) entries = none)
    (positive : 0 < offset) : outputs = inputs ∧ after = before := by
  cases actual with
  | nil => exact ⟨rfl, rfl⟩
  | unselected index absent rest =>
      obtain ⟨rfl, rfl⟩ := tail_identity rest only (by omega)
      exact ⟨rfl, rfl⟩
  | selected index found first rest =>
      rw [only offset (by omega)] at found
      cases found
termination_by inputs.length

private theorem children_tail {record originals entries inputs before outputs after}
    (actual : EditChildren (width := width) record originals entries 0 inputs before outputs after)
    (only : ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) entries = none) :
    outputs.tail = inputs.tail := by
  cases inputs with
  | nil => cases actual; rfl
  | cons value inputs =>
      cases actual with
      | unselected index absent rest =>
          obtain ⟨rfl, rfl⟩ := tail_identity rest only (by omega)
          rfl
      | selected index found first rest =>
          obtain ⟨rfl, rfl⟩ := tail_identity rest only (by omega)
          rfl

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem first_retained {valid : Guard → Prop} {inputs outputs : List (Value Symbol Guard)}
    (routes : ForestRoutes valid inputs outputs)
    (typed : ∀ value, inputs[0]? = some value → Annotated valid value) :
    ∀ value, outputs[0]? = some value → Annotated valid value := by
  have inputRoute : ForestPath valid [0] inputs := by
    intro value selected
    exact .annotated [] value (typed value (by simpa [select] using selected))
  intro value selected
  exact route_nil (routes [0] inputRoute value (by simpa [select] using selected))

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem replace_head {values results : List (Value Symbol Guard)}
    {head : Value Symbol Guard} {tail : List (Value Symbol Guard)}
    (shape : values = head :: tail) (count : results.length = values.length)
    (tails : results.tail = values.tail) : ∃ first, results = first :: tail := by
  cases results with
  | nil =>
      rw [shape] at count
      simp only [List.length_nil, List.length_cons] at count
      omega
  | cons first remaining =>
      have same : remaining = tail := by simpa only [shape, List.tail_cons] using tails
      exact ⟨first, congrArg (List.cons first) same⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem edge_replaced (valid : Guard → Prop) (literal : String → Symbol)
    {source result : EdgeValue Symbol Guard} (fields : EdgeFields valid literal source)
    (symbol : result.entry.key.symbol = source.entry.key.symbol)
    (guard : result.entry.key.constraint = source.entry.key.constraint)
    (count : result.children.length = source.children.length)
    (typed : ∀ value, result.children[0]? = some value → Annotated valid value)
    (tails : result.children.tail = source.children.tail) : EdgeFields valid literal result := by
  cases fields with
  | annotated source annotation own shape original =>
      obtain ⟨first, children⟩ := replace_head shape count tails
      exact .annotated result first (guard.trans own) children (typed first (by rw [children]; rfl))
  | application source types marker function argument own constraint shape typesTyped markerTyped functionFields argumentFields =>
      obtain ⟨first, children⟩ := replace_head shape count tails
      exact .application result first marker function argument (symbol.trans own) (guard.trans constraint) children
        (typed first (by rw [children]; rfl)) markerTyped functionFields argumentFields
  | filter source goal candidates own constraint shape goalTyped candidateFields =>
      obtain ⟨first, children⟩ := replace_head shape count tails
      exact .filter result first candidates (symbol.trans own) (guard.trans constraint) children
        (typed first (by rw [children]; rfl)) candidateFields

private theorem rows_fields (lib : Library) (literal : String → Symbol)
    {record originals entries inputs before outputs after}
    (actual : EditRows (width := width) record originals entries inputs before outputs after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries)) (resident : Edges before.checked.native.machine.heap inputs)
    (closed : ClosedEdges inputs)
    (paths : ∀ edge ∈ inputs, ChildrenPaths (Origin lib) entries 0 edge.children)
    (fields : ∀ edge ∈ inputs, EdgeFields (Origin lib) literal edge)
    (only : ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) entries = none) :
    ∀ edge ∈ outputs, EdgeFields (Origin lib) literal edge := by
  cases inputs with
  | nil => cases actual; intro edge member; cases member
  | cons edge inputs =>
      cases actual with
      | cons edited built rest =>
          have facts := ready.checked.semantic.ready.semantic.1.normal.facts
          obtain ⟨current, first, available, valuesClosed, routes⟩ :=
            SourceSynthesisNativeTypeSharedEdit.children lib edited ready originalAvailable originalClosed originalRoutes
              populated (facts.cached.edges _ _ (resident edge List.mem_cons_self))
              (closed edge List.mem_cons_self) (paths edge List.mem_cons_self)
          have typed := first_retained routes (fields edge List.mem_cons_self).first
          have oldResident := InternedEdgeResidency.edge_grows _ _ first.heap edge (resident edge List.mem_cons_self)
          obtain ⟨constructed, last, returned, exactChildren, exactGuard⟩ :=
            SourceSynthesisNativeTypeSharedHeap.edge lib edge _ built current oldResident available
          have physical := MergedPhysicalGroupEdges.makeEdge_fields _
            current.checked.semantic.ready.semantic.1.normal.facts edge.entry.key.symbol edge.entry.key.constraint _ available
          have resultSymbol := physical.1
          rw [built] at resultSymbol
          have own := edge_replaced (Origin lib) literal (fields edge List.mem_cons_self)
            resultSymbol exactGuard (by rw [exactChildren]; exact children_length edited)
            (by rw [exactChildren]; exact typed) (by rw [exactChildren]; exact children_tail edited only)
          have preceding := first.trans last
          have later := rows_fields lib literal rest constructed
            (fun original member => preceding.available original (originalAvailable original member)) originalClosed originalRoutes
            populated (fun row member => InternedEdgeResidency.edge_grows _ _ preceding.heap row
              (resident row (List.mem_cons_of_mem _ member)))
            (fun row member => closed row (List.mem_cons_of_mem _ member))
            (fun row member => paths row (List.mem_cons_of_mem _ member))
            (fun row member => fields row (List.mem_cons_of_mem _ member)) only
          intro result member
          rcases List.mem_cons.mp member with rfl | member
          · exact own
          · exact later result member
termination_by inputs.length

/-- Actual annotation-only below-edits retain all routes and every recursive Program field. -/
theorem below_fields (lib : Library) (literal : String → Symbol)
    {record originals entries input before output after}
    (actual : EditNode (width := width) record originals (.editBelow entries) input before output after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries)) (nonempty : HasLeaf (.editBelow entries))
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (paths : NodePaths (Origin lib) (.editBelow entries) input) (fields : ValueFields (Origin lib) literal input)
    (annotationOnly : ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) entries = none) :
    Ready lib after ∧ Extension before.checked.native.machine after.checked.native.machine ∧
      Available after.checked.native.machine.heap output ∧ output.free = [] ∧
      (∀ path, TypePath (Origin lib) path input → TypePath (Origin lib) path output) ∧
      ValueFields (Origin lib) literal output := by
  obtain ⟨next, extension, present, resultClosed, retained⟩ :=
    SourceSynthesisNativeTypeSharedEdit.node lib actual ready originalAvailable originalClosed originalRoutes
      populated nonempty available closed paths
  refine ⟨next, extension, present, resultClosed, retained, ?_⟩
  cases fields with
  | empty =>
      cases actual with
      | empty => exact .empty
      | recursive recursive head body => cases recursive
  | node entry edges depth free checked =>
      cases actual with
      | ordinary edited built =>
          have facts := ready.checked.semantic.ready.semantic.1.normal.facts
          have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
          have closedRows := MergedColdReaderClosed.node_children_closed _ facts entry edges depth free available closed
          have rowPaths := fun edge member => node_to_children paths edge member
          have newFields := rows_fields lib literal edited ready originalAvailable originalClosed originalRoutes
            populated resident closedRows rowPaths checked annotationOnly
          obtain ⟨middleReady, _first, resultRows, _rowsClosed, _routes⟩ :=
            SourceSynthesisNativeTypeSharedEdit.rows lib edited ready originalAvailable originalClosed originalRoutes
              populated resident closedRows rowPaths
          have returned := SourceSynthesisHereditaryProgramFields.makeNode_fields (Origin lib) literal _ _
            middleReady.checked.semantic.ready.semantic.1.normal.facts resultRows newFields
          simpa only [built] using returned
      | recursive recursive head body => cases recursive

end MicroCFTA.SourceSynthesisNativeTypeHereditaryEditFields
