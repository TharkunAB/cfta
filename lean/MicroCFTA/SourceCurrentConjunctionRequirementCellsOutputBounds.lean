import MicroCFTA.SourceCurrentConjunctionRequirementCellsExecution

/-!
# Literal output widths for shared requirement cells

The current cell bounds its returned operand count. Each pending projection
adds at most one value. An early Empty result returns one operand. These
bounds use the actual stored lists and need no semantic heap assumptions.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsOutputBounds
open InternedConstructorTemplates
namespace Cells
export SourceCurrentConjunctionRequirementCells (State lookup force)
end Cells
namespace Pull
export SourceCurrentConjunctionRequirementPull (Cursor run projection)
end Pull
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard

/-- Canonical map readback cannot increase the original occurrence count. -/
theorem canonical_length (nodes : List Node) :
    (SourceCurrentConjunctionRequirements.canonical nodes).length ≤ nodes.length := by
  have mapLength : (SourceCurrentConjunctionMap.elems SourceCurrentConjunctionRequirements.key nodes).length ≤ nodes.length := by
    apply (SourceCurrentConjunctionMap.elems_nodup _ nodes).length_le_of_subset
    intro value member
    obtain ⟨entry, present, same⟩ := List.mem_map.mp member
    have found := SourceEqualityNeededMap.lookup_of_mem entry.1 _ entry.2
      (SourceCurrentConjunctionMap.fromList_ascending _ nodes) present
    exact same ▸ (SourceCurrentConjunctionMap.fromList_origin _ nodes entry.1 entry.2 found).1
  unfold SourceCurrentConjunctionRequirements.canonical
  split
  · rename_i impossible
    cases nodes with
    | nil => simp at impossible
    | cons first rest => simp only [List.length_cons, List.length_nil]; omega
  · exact mapLength

/-- The cached operands or the literal collected prefix and pending jobs bound the output. -/
def bound (handle : Nat) (before : Cells.State Symbol Formula) : Nat :=
  match Cells.lookup handle before with
  | none => 0
  | some (.column nodes) | some (.done nodes) => nodes.length
  | some (.pending cursor) => cursor.collected.length + cursor.pending.length

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- A completed cursor returns at most one operand per original pending job. -/
theorem run_length {p h : Nat} {cursor : Pull.Cursor Symbol Formula}
    {before after : SourceCurrentConjunctionRowsWorker.Physical Symbol Formula} {nodes : List Node}
    (actual : Pull.run p h cursor before = .done nodes after) :
    nodes.length ≤ cursor.collected.length + cursor.pending.length := by
  rcases cursor with ⟨pending, collected⟩
  induction pending generalizing collected before after nodes with
  | nil =>
      rw [SourceCurrentConjunctionRequirementPull.run_nil] at actual
      cases actual
      simpa only [List.length_nil, Nat.add_zero] using canonical_length collected
  | cons job rest ih =>
      rw [SourceCurrentConjunctionRequirementPull.run_step] at actual
      cases projected : Pull.projection p h job before with
      | failed fault physical =>
          simp only [SourceCurrentConjunctionRequirementPull.step, projected,
            SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual
          cases actual
      | done value physical =>
          by_cases impossible : SourceCurrentConjunctionRequirements.isEmpty value = true
          · simp only [SourceCurrentConjunctionRequirementPull.step, projected,
              SourceCurrentConjunctionRowsWorker.Outcome.bind, impossible, ite_true] at actual
            cases actual
            simp only [List.length_cons, List.length_nil]
            omega
          · simp only [SourceCurrentConjunctionRequirementPull.step, projected,
              SourceCurrentConjunctionRowsWorker.Outcome.bind, impossible] at actual
            have tail := ih (collected := collected ++ [value]) (before := physical)
              (after := after) (nodes := nodes) actual
            simp only [List.length_append, List.length_cons, List.length_nil] at tail ⊢
            omega

/-- Every successful force obeys the width computed from that same initial cell. -/
theorem force_length {p h handle : Nat} {before after : Cells.State Symbol Formula} {nodes : List Node}
    (actual : Cells.force p h handle before = .done nodes after) :
    nodes.length ≤ bound handle before := by
  cases found : Cells.lookup handle before with
  | none =>
      rw [SourceCurrentConjunctionRequirementCells.force_step] at actual
      simp only [SourceCurrentConjunctionRequirementCells.forceStep, found] at actual
      cases actual
  | some cell =>
      cases cell with
      | done saved =>
          rw [SourceCurrentConjunctionRequirementCells.force_step] at actual
          simp only [SourceCurrentConjunctionRequirementCells.forceStep, found] at actual
          cases actual
          simp only [bound, found]
          exact Nat.le_refl _
      | column original =>
          rw [SourceCurrentConjunctionRequirementCells.force_step] at actual
          simp only [SourceCurrentConjunctionRequirementCells.forceStep, found] at actual
          cases actual
          simpa only [bound, found] using canonical_length original
      | pending cursor =>
          have run := SourceCurrentConjunctionRequirementCellsExecution.force_pending_run found actual
          simpa only [bound, found] using run_length run

end MicroCFTA.SourceCurrentConjunctionRequirementCellsOutputBounds
