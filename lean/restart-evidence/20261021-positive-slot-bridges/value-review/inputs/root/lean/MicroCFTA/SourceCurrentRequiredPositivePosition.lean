import MicroCFTA.SourceCurrentRequiredRowOrigins
import MicroCFTA.SourceEqualityProjectionLanguage
import MicroCFTA.SourceEqualityRequiredExecution

/-!
# Positive ordinary row positions through actual Required calls

Child indices retain their natural positions. Different row indices and
union alternatives can share one path. Mu bodies and references remain
opaque. This finite relation does not follow observational unfolding.
-/
namespace MicroCFTA.SourceCurrentRequiredPositivePosition
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceEqualityAnnotationLanguage
open SourceCurrentRequiredRowOrigins (Origin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A nonplain ordinary row occurs at a finite child path with opaque Mu barriers. -/
inductive PositiveAt : Node → List Nat → Prop where
  /-- A selected root row has a nonplain full guard. -/
  | root {entry rows depth free} (rowIndex : Nat) (row : Row)
      (selected : rows[rowIndex]? = some row)
      (positive : SourceMemoGate.plain row.entry.key.constraint = false) :
      PositiveAt (.node entry rows depth free) []
  /-- An ordinary child retains its natural index while row choice remains explicit. -/
  | child {entry rows depth free} (rowIndex childIndex : Nat) (row : Row) (child : Node)
      (selected : rows[rowIndex]? = some row) (chosen : row.children[childIndex]? = some child)
      {path} (rest : PositiveAt child path) :
      PositiveAt (.node entry rows depth free) (childIndex :: path)
  /-- A literal union alternative adds no child-path component. -/
  | member {entry members depth free} (memberIndex : Nat) (child : Node)
      (selected : members[memberIndex]? = some child) {path} (rest : PositiveAt child path) :
      PositiveAt (.union entry members depth free) path

/-- A hereditary plain value contains no positive occurrence at these positions. -/
theorem not_plain {value path} (positive : PositiveAt value path) : ¬ Annotated Plain value := by
  induction positive with
  | root rowIndex row selected nonplain =>
      intro annotations
      have plain := (SourceCurrentHereditaryUnconstrained.node_edge annotations row
        (List.mem_of_getElem? selected)).1
      rw [nonplain] at plain
      cases plain
  | child rowIndex childIndex row child selected chosen rest ih =>
      intro annotations
      exact ih ((SourceCurrentHereditaryUnconstrained.node_edge annotations row
        (List.mem_of_getElem? selected)).2 child (List.mem_of_getElem? chosen))
  | member memberIndex child selected rest ih =>
      intro annotations
      exact ih (SourceCurrentHereditaryUnconstrained.union_member annotations child
        (List.mem_of_getElem? selected))

/-- Required origins retain the same positive child-index path in the original value. -/
theorem origin {original result path} (related : Origin original result)
    (positive : PositiveAt result path) : PositiveAt original path := by
  induction positive generalizing original with
  | @root entry rows depth free rowIndex row selected nonplain =>
      cases related with
      | identity => exact .root rowIndex row selected nonplain
      | plain _ _ annotations => exact False.elim (not_plain (PositiveAt.root rowIndex row selected nonplain) annotations)
      | ordinary sourceEntry originals level names _ ordinary mapped =>
          obtain ⟨sourceIndex, sourceRow, found, fields, children⟩ := mapped.indexed rowIndex row selected
          exact .root sourceIndex sourceRow found (by simpa only [fields.1] using nonplain)
  | @child entry rows depth free rowIndex childIndex row child selected chosen path rest ih =>
      cases related with
      | identity => exact .child rowIndex childIndex row child selected chosen rest
      | plain _ _ annotations =>
          exact False.elim (not_plain (PositiveAt.child rowIndex childIndex row child selected chosen rest) annotations)
      | ordinary sourceEntry originals level names _ ordinary mapped =>
          obtain ⟨sourceIndex, sourceRow, found, fields, children⟩ := mapped.indexed rowIndex row selected
          obtain ⟨sourceChild, sourceChosen, childOrigin⟩ :=
            SourceEqualityProjectionLanguage.all₂_selected children childIndex child chosen
          exact .child sourceIndex childIndex sourceRow sourceChild found sourceChosen (ih childOrigin)
  | @member entry members depth free memberIndex child selected path rest ih =>
      cases related with
      | identity => exact .member memberIndex child selected rest
      | plain _ _ annotations => exact False.elim (not_plain (PositiveAt.member memberIndex child selected rest) annotations)
      | ordinary _ _ _ _ _ ordinary _ => cases ordinary

/-- An actual safe Required return preserves every positive finite child position backwards. -/
theorem required [DecidableEq (EdgeKey Symbol Guard)] {fuel readFuel needed original result before after path}
    (actual : SourceEqualityRequiredWorker.require fuel readFuel needed original before = .done result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before original)
    (guards : GuardHeap Plain before) (safe : SourceCurrentRequiredRowOrigins.ExposureSafe needed original)
    (positive : PositiveAt result path) : PositiveAt original path :=
  origin (SourceCurrentRequiredRowOrigins.node
    (SourceEqualityRequiredWorkerSound.require_graph fuel readFuel needed original before result after actual)
    semantic costs available guards safe) positive

end MicroCFTA.SourceCurrentRequiredPositivePosition
