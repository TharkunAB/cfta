import MicroCFTA.MergedAlternativesGroups
import MicroCFTA.MergedAlternativesRecursion
import MicroCFTA.MergedRowGroups

/-!
# Four-edge threshold witnesses

These witnesses check the current group branch, duplicate handling, guard
widening, and the five-recursive-operand call cycle. The earlier two-operand
counterexample remains historical because that group is now preserved.
-/
namespace MicroCFTA.MergedAlternativesThreshold
open Language MergedAlternativesGroups

/-- Exactly four distinct raw rows stay in their original order. -/
theorem four_rows : MergedRowGroups.squash 99 [0, 1, 2, 3] = [0, 1, 2, 3] := by decide

/-- The fifth distinct raw row changes the source group branch. -/
theorem five_rows : MergedRowGroups.squash 99 [0, 1, 2, 3, 4] = [99] := by decide

/-- Repeated declarations do not increase the number of distinct source rows. -/
theorem duplicate_rows :
    MergedRowGroups.squash 99
      (MergedRowGroups.rowsAt [((), 0), ((), 1), ((), 2), ((), 3), ((), 0), ((), 3)] ()) =
      [0, 1, 2, 3] := by decide

/-- Five distinct semantic guards all reject the nullary term. -/
def rejecting (index : Fin 5) : Edge Unit Unit :=
  ⟨(), [], fun | .node _ children => decide (children.length = index.val + 1)⟩

/-- The guards differ on longer terms, so full-edge duplicate removal cannot identify them. -/
theorem rejecting_injective : Function.Injective rejecting := by
  intro first second same
  let probe : Term Unit := .node () (List.replicate (first.val + 1) (.node () []))
  have guards := congrArg (fun edge : Edge Unit Unit => edge.guard probe) same
  have matched : first.val + 1 = second.val + 1 := by
    simpa [rejecting, probe] using guards.symm
  apply Fin.ext
  omega

/-- All five source-group edges are distinct before the threshold branch. -/
theorem rejecting_distinct : (List.ofFn rejecting).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro first second firstBound secondBound same
  exact congrArg Fin.val (rejecting_injective (by simpa only [List.getElem_ofFn] using same))

/-- None of the five original alternatives accepts the nullary term. -/
theorem rejecting_original (edge : Edge Unit Unit) (member : edge ∈ List.ofFn rejecting) :
    ¬EdgeAccepts (fun _ _ => True) edge (.node () []) := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  simp [EdgeAccepts, rejecting]

/-- A current five-edge merge accepts the nullary term rejected by every input. -/
theorem five_guard_widening :
    ∃ edge ∈ mergeGroup id (fun _ => ()) (List.ofFn rejecting),
      EdgeAccepts (fun _ _ => True) edge (.node () []) := by
  refine ⟨⟨(), [], fun _ => true⟩, ?_, [], rfl, .nil, rfl⟩
  exact List.mem_singleton_self _

/-- Each recursive operand supplies one f edge pointing back to itself. -/
def recursiveGroup : List (Edge (Option (Fin 5)) Unit) :=
  List.ofFn fun index => ⟨(), [some index], fun _ => true⟩

/-- The five-operand recursive group enters the current large-group branch. -/
theorem recursive_group_merges :
    mergeGroup id (fun _ => none) recursiveGroup = [⟨(), [none], fun _ => true⟩] := rfl

/-- The exact merged child column retains five recursive boundary operands. -/
def recursiveColumn : List (Option (Fin 5)) := recursiveGroup.flatMap Edge.children

/-- The repair recognizes a boundary in the current large-group column. -/
theorem recursive_column_boundary : recursiveColumn.any Option.isSome = true := rfl

/-- The current five-operand dependency slice, with or without the boundary repair. -/
def requests (repaired : Bool) : MergedAlternativesRecursion.Task → List MergedAlternativesRecursion.Task
  | .mergeJoined => [.combineColumn]
  | .combineColumn => if repaired && recursiveColumn.any Option.isSome then [] else [.mergeJoined]

/-- The five-operand source case has the same mandatory call dependency shape. -/
theorem requests_eq (repaired : Bool) : requests repaired = MergedAlternativesRecursion.requests repaired := by
  funext task
  cases task <;> rfl

/-- Removing the repair would restore the call cycle even with the four-edge threshold. -/
theorem five_without_repair :
    ¬MergedAlternativesRecursion.Completes (requests false) .mergeJoined := by
  rw [requests_eq]
  exact MergedAlternativesRecursion.legacy_no_completion _

/-- The current five-operand case has a finite dependency tree with the repair. -/
theorem five_repaired : MergedAlternativesRecursion.Completes (requests true) .mergeJoined := by
  rw [requests_eq]
  exact MergedAlternativesRecursion.repaired_completion

end MicroCFTA.MergedAlternativesThreshold
