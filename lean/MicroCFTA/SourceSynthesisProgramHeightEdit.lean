import MicroCFTA.SourceSynthesisProgramHeight
import MicroCFTA.SourceSynthesisNativeTypeSharedEdit

/-!
# Program height through actual annotation-only shared edits

Only child zero can have an edit. Every later child remains the same
physical value. Rebuilt raw rows retain their Program heights. Actual
node normalization can remove rows, so the output height cannot increase.

Initial shared readiness and the actual Type routes justify each physical
constructor frame. These laws do not prove global completion or Type progress.
-/
namespace MicroCFTA.SourceSynthesisProgramHeightEdit
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentHereditaryTypeEditPlan
open SourceCurrentEditDomains (Populated)
open SourceCurrentAllocatedSharedEditGraph
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

private theorem rows_height (lib : Library)
    {record originals entries inputs before outputs after}
    (actual : EditRows (width := width) record originals entries inputs before outputs after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries)) (resident : Edges before.checked.native.machine.heap inputs)
    (closed : ClosedEdges inputs)
    (paths : ∀ row ∈ inputs, ChildrenPaths (Origin lib) entries 0 row.children)
    (only : ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) entries = none) :
    SourceSynthesisProgramHeight.edges outputs = SourceSynthesisProgramHeight.edges inputs := by
  cases inputs with
  | nil => cases actual; rfl
  | cons row inputs =>
      cases actual with
      | cons edited built rest =>
          have facts := ready.checked.semantic.ready.semantic.1.normal.facts
          obtain ⟨current, first, available, _valuesClosed, _routes⟩ :=
            SourceSynthesisNativeTypeSharedEdit.children lib edited ready originalAvailable originalClosed originalRoutes
              populated (facts.cached.edges _ _ (resident row List.mem_cons_self))
              (closed row List.mem_cons_self) (paths row List.mem_cons_self)
          have oldResident := InternedEdgeResidency.edge_grows _ _ first.heap row (resident row List.mem_cons_self)
          obtain ⟨constructed, last, _returned, exactChildren, _exactGuard⟩ :=
            SourceSynthesisNativeTypeSharedHeap.edge lib row _ built current oldResident available
          have own := SourceSynthesisProgramHeight.edge_same_tail row _
            ((congrArg List.tail exactChildren).trans (children_tail edited only))
          have preceding := first.trans last
          have later := rows_height lib rest constructed
            (fun original member => preceding.available original (originalAvailable original member)) originalClosed originalRoutes
            populated (fun edge member => InternedEdgeResidency.edge_grows _ _ preceding.heap edge
              (resident edge (List.mem_cons_of_mem _ member)))
            (fun edge member => closed edge (List.mem_cons_of_mem _ member))
            (fun edge member => paths edge (List.mem_cons_of_mem _ member)) only
          simp only [SourceSynthesisProgramHeight.edges]
          rw [own, later]
termination_by inputs.length

/-- Actual annotation-only below-edits cannot increase an ordinary Program height. -/
theorem below (lib : Library)
    {record originals entries input before output after}
    (actual : EditNode (width := width) record originals (.editBelow entries) input before output after)
    (ready : Ready lib before) (originalAvailable : Values before.checked.native.machine.heap originals)
    (originalClosed : ClosedValues originals)
    (originalRoutes : ∀ own ∈ record.paths, ForestPath (Origin lib) (own.map Int.ofNat) originals)
    (populated : Populated (.editBelow entries))
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (paths : NodePaths (Origin lib) (.editBelow entries) input)
    (ordinary : SourceEqualityRequiredCache.Ordinary input)
    (only : ∀ index : Nat, index ≠ 0 → SourceEqualityNeededMap.lookup (index : Int) entries = none) :
    SourceSynthesisProgramHeight.value output ≤ SourceSynthesisProgramHeight.value input := by
  cases input with
  | empty =>
      cases actual with
      | empty => exact Nat.le_refl _
      | recursive recursive head body => cases recursive
  | reference name => cases ordinary
  | union entry members depth free => cases ordinary
  | mu entry body depth ordinaryShape => cases ordinary
  | node entry inputs depth free =>
      cases actual with
      | ordinary edited built =>
          have facts := ready.checked.semantic.ready.semantic.1.normal.facts
          have resident := InternedEdgeResidency.resident_edges _ facts.linked _ available.resident
          have closedRows := MergedColdReaderClosed.node_children_closed _ facts entry inputs depth free available closed
          have rowPaths := fun row member => node_to_children paths row member
          have bounded := rows_height lib edited ready originalAvailable originalClosed originalRoutes
            populated resident closedRows rowPaths only
          obtain ⟨middleReady, _first, resultRows, _rowsClosed, _routes⟩ :=
            SourceSynthesisNativeTypeSharedEdit.rows lib edited ready originalAvailable originalClosed originalRoutes
              populated resident closedRows rowPaths
          have returned := SourceSynthesisProgramHeight.makeNode_le _ _
            middleReady.checked.semantic.ready.semantic.1.normal.facts resultRows
          rw [built] at returned
          rw [bounded] at returned
          simpa only [SourceSynthesisProgramHeight.value] using returned
      | recursive recursive head body => cases recursive

end MicroCFTA.SourceSynthesisProgramHeightEdit
