import MicroCFTA.SourceSynthesisNativeTypeSharedHeap
import MicroCFTA.SourceSynthesisAnnotationFieldConstructors
import MicroCFTA.SourceSynthesisProgramBuildRolesGeneric

/-!
# Joint Program fields at actual node reconstruction

The same actual node request retains shared Type readiness and closedness.
Complete returned row roles supply the strict Program shape. Their first
Type fields supply the root field certificate. Program guards need no Type
annotation. These laws do not derive row facts for every reached caller.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeProgramNode
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisTypePathRoles (AnnotationFields)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue ProgramEdge)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentAllocatedSharedEditGraph (advanceHeap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- One actual reconstruction retains shared readiness, strict roles and first Type fields. -/
theorem node (lib : Library) (literal : String → Symbol)
    {before : Shared width} {rows : List (EdgeValue Symbol Guard)}
    {result : Value Symbol Guard} {heap : Heap}
    (actual : run (makeNode rows) before.checked.native.machine.heap = (result, heap))
    (ready : Ready lib before) (resident : Edges before.checked.native.machine.heap rows)
    (closed : ClosedEdges rows) (roles : ∀ row ∈ rows, ProgramEdge literal row)
    (fields : ∀ row ∈ rows, ∀ value, row.children[0]? = some value → Annotated (Origin lib) value) :
    Ready lib (advanceHeap before heap) ∧
      Extension before.checked.native.machine (advanceHeap before heap).checked.native.machine ∧
      Available heap result ∧ result.free = [] ∧ ProgramValue literal result ∧ AnnotationFields (Origin lib) result := by
  obtain ⟨next, extension, available, resultClosed⟩ :=
    SourceSynthesisNativeTypeSharedHeap.node lib actual ready resident closed
  have facts := ready.checked.semantic.ready.semantic.1.normal.facts
  have role := SourceSynthesisProgramBuildRolesGeneric.makeNode_roles literal rows
    before.checked.native.machine.heap facts resident roles
  have annotated := SourceSynthesisAnnotationFieldConstructors.makeNode_fields (Origin lib) rows
    before.checked.native.machine.heap facts resident fields
  exact ⟨next, extension, available, resultClosed, by simpa only [actual] using role,
    by simpa only [actual] using annotated⟩
end MicroCFTA.SourceSynthesisNativeTypeProgramNode
