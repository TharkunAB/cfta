import MicroCFTA.SourceCurrentRequiredPositivePosition
import MicroCFTA.SourceCurrentNormalizedChildSeparation
import MicroCFTA.InternedValueMass
import MicroCFTA.SymbolicBijections

/-!
# A retained child pair from finite positive paths

This module counts distinct literal positive paths. Mu bodies and references
remain opaque. The theorem consumes a backwards path relation. It makes no
claim that an execution supplies that relation.
-/
namespace MicroCFTA.SourceCurrentPositiveOwnerPair
open InternedConstructorTemplates
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentNormalizedChildSeparation (Rel)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Path" => List Nat

private def candidates : Nat → Node → List Path
  | 0, _ => []
  | fuel + 1, .node _ rows _ _ =>
      [] :: rows.flatMap (fun row => row.children.zipIdx.flatMap
        (fun child => (candidates fuel child.1).map (child.2 :: ·)))
  | fuel + 1, .union _ members _ _ =>
      [] :: members.flatMap (candidates fuel)
  | _ + 1, _ => [[]]

private theorem candidates_complete {value path} (positive : PositiveAt value path) :
    ∀ fuel, InternedValueMass.value value < fuel → path ∈ candidates fuel value := by
  induction positive with
  | root rowIndex row selected nonplain =>
      intro fuel bounded
      cases fuel with
      | zero => omega
      | succ fuel => exact List.mem_cons_self
  | @child entry rows depth free rowIndex childIndex row child selected chosen path rest ih =>
      intro fuel bounded
      cases fuel with
      | zero => omega
      | succ fuel =>
          have smaller := InternedValueMass.node_child_lt entry rows depth free row
            (List.mem_of_getElem? selected) child (List.mem_of_getElem? chosen)
          have present := ih fuel (by omega)
          apply List.mem_cons_of_mem
          apply List.mem_flatMap.mpr
          refine ⟨row, List.mem_of_getElem? selected, ?_⟩
          apply List.mem_flatMap.mpr
          refine ⟨(child, childIndex), List.mk_mem_zipIdx_iff_getElem?.mpr chosen, ?_⟩
          exact List.mem_map.mpr ⟨path, present, rfl⟩
  | @member entry members depth free memberIndex child selected path rest ih =>
      intro fuel bounded
      cases fuel with
      | zero => omega
      | succ fuel =>
          have smaller := InternedValueMass.union_member_lt entry members depth free child
            (List.mem_of_getElem? selected)
          exact List.mem_cons_of_mem [] (List.mem_flatMap.mpr
            ⟨child, List.mem_of_getElem? selected, ih fuel (by omega)⟩)

private noncomputable def positivePaths (value : Node) : List Path := by
  classical
  exact ((candidates (InternedValueMass.value value + 1) value).filter
    (fun path => decide (PositiveAt value path))).eraseDups

private theorem positivePaths_spec {value path} :
    path ∈ positivePaths value ↔ PositiveAt value path := by
  classical
  simp only [positivePaths, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun positive =>
    ⟨candidates_complete positive _ (by omega), positive⟩⟩

private theorem positivePaths_nodup (value : Node) : (positivePaths value).Nodup := by
  classical
  exact SymbolicDriver.eraseDups_nodup _

/-- A total backwards positive relation forces a distinct pair through the same child in one fixed class. -/
theorem same_child_pair
    {classes : EqualityNormalize.Constraints}
    (fixed : EqualityNormalize.congruenceStep classes = some classes)
    (index : Nat) {entry depth free} {rows : List Row}
    (row : Row) (member : row ∈ rows)
    (nonplain : SourceMemoGate.plain row.entry.key.constraint = false)
    (back : ∀ q, PositiveAt (.node entry rows depth free) q →
      ∃ j p original, row.children[j]? = some original ∧ PositiveAt original p ∧
        Rel classes (index :: q) (j :: p)) :
    ∃ paths ∈ classes, ∃ left right,
      index :: left ∈ paths ∧ index :: right ∈ paths ∧ left ≠ right := by
  classical
  by_contra absent
  have dropped : ∀ paths ∈ classes, ∀ left right : Path,
      index :: left ∈ paths → index :: right ∈ paths → left = right := by
    intro paths selected left right first second
    by_contra different
    exact absent ⟨paths, selected, left, right, first, second, different⟩
  let positions := positivePaths (.node entry rows depth free)
  have distinct : positions.Nodup := positivePaths_nodup _
  obtain ⟨rowIndex, selected⟩ := List.mem_iff_getElem?.mp member
  have root : [] ∈ positions := positivePaths_spec.mpr (.root rowIndex row selected nonplain)
  have total : ∀ q ∈ positions, ∃ target ∈ positions.erase [],
      Rel classes (index :: q) target := by
    intro q present
    obtain ⟨j, p, original, chosen, positive, related⟩ := back q (positivePaths_spec.mp present)
    have included : j :: p ∈ positions :=
      positivePaths_spec.mpr (.child rowIndex j row original selected chosen positive)
    exact ⟨j :: p, (List.mem_erase_of_ne (by simp)).mpr included, related⟩
  have injective : ∀ first ∈ positions, ∀ second ∈ positions,
      ∀ target ∈ positions.erase [], Rel classes (index :: first) target →
        Rel classes (index :: second) target → first = second := by
    intro first _ second _ target _ firstRelated secondRelated
    exact SourceCurrentNormalizedChildSeparation.child_separate fixed index dropped
      firstRelated secondRelated
  have counted := SymbolicDriver.relation_cardinality_le positions (positions.erase []) []
    distinct (fun q target => Rel classes (index :: q) target) total injective
  have shorter := List.length_erase_of_mem root
  have nonempty : 0 < positions.length := List.length_pos_of_mem root
  omega

end MicroCFTA.SourceCurrentPositiveOwnerPair
