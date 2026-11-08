import MicroCFTA.SourceSynthesisNativeTypeSharedEdit
import MicroCFTA.SourceSynthesisTypePathRoles
import MicroCFTA.SourceSynthesisClassProgramRoles
import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerCompletion

/-!
# Program first fields after actual current edits

The route to position zero certifies an ordinary Program's Type fields.
Actual below-edits retain an empty or ordinary result. Preserved routes
therefore retain its first-field certificate. The strict Program-role law
uses the same current graph's derived executable return and full guards.
These local results do not establish completion or all reached source roles.
-/
namespace MicroCFTA.SourceSynthesisTypeRouteProgramFields
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache (Ordinary)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceEqualityProjectionGraph (select)
open SourceCurrentHereditaryTypePaths (TypePath ForestPath)
open SourceCurrentHereditaryTypeEditPlan (NodePaths node_to_children)
open SourceCurrentEditDomains (Populated HasLeaf)
open SourceSynthesisTypePathRoles (AnnotationFields)

section Pure
variable {Symbol Guard : Type}

/-- An ordinary value's first-child route derives all its first-field annotations. -/
theorem of_route {valid : Guard → Prop} {value : Value Symbol Guard}
    (ordinary : Ordinary value) (route : TypePath valid [0] value) : AnnotationFields valid value := by
  cases value with
  | empty => exact .empty
  | reference | union | mu => cases ordinary
  | node entry rows depth free =>
      apply AnnotationFields.node entry rows depth free
      intro row member child selected
      apply SourceCurrentHereditaryTypeRouteConstructors.route_nil
      exact SourceCurrentHereditaryTypeRouteConstructors.ordinary_children route row member child
        (by simpa [select] using selected)

/-- The first-field certificate supplies the structural route to position zero. -/
theorem to_route {valid : Guard → Prop} {value : Value Symbol Guard}
    (fields : AnnotationFields valid value) : TypePath valid [0] value :=
  SourceSynthesisTypePathRoles.annotation_path fields []
end Pure

open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceRecursiveIntersectionKernel (Extension)
open SourceEqualityEdits
open SourceCurrentAllocatedSharedEditGraph
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual below-edits of an ordinary input retain an empty or ordinary result. -/
theorem below_ordinary (lib : Library) {record originals entries input before output after}
    (actual : EditNode (width := width) record originals (.editBelow entries) input before output after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries))
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (paths : NodePaths (Origin lib) (.editBelow entries) input) (ordinary : Ordinary input) : Ordinary output := by
  cases input with
  | empty =>
      cases actual with
      | empty => trivial
      | recursive recursive head body => cases recursive
  | reference | union | mu => cases ordinary
  | node entry edges depth free =>
      cases actual with
      | ordinary edited built =>
          have facts := ready.checked.semantic.ready.semantic.1.normal.facts
          have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
          have rowClosed := MergedColdReaderClosed.node_children_closed _ facts entry edges depth free available closed
          have returned := SourceSynthesisNativeTypeSharedEdit.rows lib edited ready originalAvailable originalClosed
            originalRoutes populated resident rowClosed (fun row member => node_to_children paths row member)
          have shape := SourceEqualityRequiredCache.node_ordinary _ _
            returned.1.checked.semantic.ready.semantic.1.normal.facts returned.2.2.1
          simpa only [built] using shape
      | recursive recursive head body => cases recursive

/-- The same current graph retains all Type routes and the output first-field certificate. -/
theorem node_fields (lib : Library) {record originals entries input before output after}
    (actual : EditNode (width := width) record originals (.editBelow entries) input before output after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries)) (nonempty : HasLeaf (.editBelow entries))
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (fields : AnnotationFields (Origin lib) input) (paths : NodePaths (Origin lib) (.editBelow entries) input) :
    Ready lib after ∧ Extension before.checked.native.machine after.checked.native.machine ∧
      Available after.checked.native.machine.heap output ∧ output.free = [] ∧
      (∀ path, TypePath (Origin lib) path input → TypePath (Origin lib) path output) ∧
      AnnotationFields (Origin lib) output := by
  obtain ⟨next, extension, present, resultClosed, retained⟩ :=
    SourceSynthesisNativeTypeSharedEdit.node lib actual ready originalAvailable originalClosed
      originalRoutes populated nonempty available closed paths
  have inputOrdinary : Ordinary input := by cases fields <;> trivial
  have resultOrdinary := below_ordinary lib actual ready originalAvailable originalClosed
    originalRoutes populated available closed paths inputOrdinary
  exact ⟨next, extension, present, resultClosed, retained, of_route resultOrdinary (retained [0] (to_route fields))⟩

/-- A current graph's own executable return also retains the strict full-guard Program role. -/
theorem node_program_fields (lib : Library) (literal : String → Symbol)
    {record originals entries input before output after}
    (actual : EditNode (width := width) record originals (.editBelow entries) input before output after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries)) (nonempty : HasLeaf (.editBelow entries))
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (fields : AnnotationFields (Origin lib) input) (paths : NodePaths (Origin lib) (.editBelow entries) input)
    (role : ProgramValue literal input)
    (annotationOnly : ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) entries = none) :
    Ready lib after ∧ Extension before.checked.native.machine after.checked.native.machine ∧
      Available after.checked.native.machine.heap output ∧ output.free = [] ∧
      (∀ path, TypePath (Origin lib) path input → TypePath (Origin lib) path output) ∧
      AnnotationFields (Origin lib) output ∧ ProgramValue literal output := by
  have operationGood := SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked ready.checked.good) ready.checked.semantic ready.costs
  have sharedGood : SourceCurrentLowerOperationInvariants.SharedGood before :=
    ⟨operationGood, ready.physicalMemo, fun path value present => (ready.slots path value present).1⟩
  obtain ⟨bound, completed⟩ := SourceCurrentAllocatedSharedEditWorkerCompletion.node_uniform actual
  have outputRole := SourceSynthesisClassProgramRoles.below_roles (completed bound (Nat.le_refl _))
    sharedGood originalAvailable available role annotationOnly
  obtain ⟨next, extension, present, resultClosed, retained, outputFields⟩ :=
    node_fields lib actual ready originalAvailable originalClosed originalRoutes populated nonempty available closed fields paths
  exact ⟨next, extension, present, resultClosed, retained, outputFields, outputRole⟩

end MicroCFTA.SourceSynthesisTypeRouteProgramFields
