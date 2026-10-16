import MicroCFTA.SourceCurrentCurriedDefaulting

#print axioms MicroCFTA.SourceCurrentCurriedDefaulting.narrow_any
#check @MicroCFTA.SourceCurrentCurriedDefaulting.narrow_any
#print axioms MicroCFTA.SourceCurrentCurriedDefaulting.agrees_without_any
#check @MicroCFTA.SourceCurrentCurriedDefaulting.agrees_without_any
#print axioms MicroCFTA.SourceCurrentCurriedDefaulting.narrow_no_open
#check @MicroCFTA.SourceCurrentCurriedDefaulting.narrow_no_open
#print axioms MicroCFTA.SourceCurrentCurriedDefaulting.narrow_no_default
#check @MicroCFTA.SourceCurrentCurriedDefaulting.narrow_no_default
#print axioms MicroCFTA.SourceCurrentCurriedDefaulting.narrow_list
#check @MicroCFTA.SourceCurrentCurriedDefaulting.narrow_list
#print axioms MicroCFTA.SourceCurrentCurriedDefaulting.narrow_any_member
#check @MicroCFTA.SourceCurrentCurriedDefaulting.narrow_any_member
#print axioms MicroCFTA.SourceCurrentCurriedDefaulting.narrow_sublist
#check @MicroCFTA.SourceCurrentCurriedDefaulting.narrow_sublist
#print axioms MicroCFTA.SourceCurrentCurriedDefaulting.narrow_idempotent
#check @MicroCFTA.SourceCurrentCurriedDefaulting.narrow_idempotent
#print axioms MicroCFTA.SourceCurrentCurriedDefaulting.counterexample_fields
#check @MicroCFTA.SourceCurrentCurriedDefaulting.counterexample_fields
#print axioms MicroCFTA.SourceCurrentCurriedDefaulting.counterexample_no_open
#check @MicroCFTA.SourceCurrentCurriedDefaulting.counterexample_no_open
#print axioms MicroCFTA.SourceCurrentCurriedDefaulting.counterexample_current
#check @MicroCFTA.SourceCurrentCurriedDefaulting.counterexample_current
#print axioms MicroCFTA.SourceCurrentCurriedDefaulting.counterexample_changed
#check @MicroCFTA.SourceCurrentCurriedDefaulting.counterexample_changed

namespace MicroCFTA.CurrentCurriedDefaultingIndependent
open InternedConstructorTemplates
open SourceCurriedDefaulting (leaf)
open SourceCurrentCurriedDefaulting

/-- The TypeDomain marker takes precedence even when head defaulting would reject. -/
theorem any_overrides_head_rejection (edges : List (EdgeValue String Guard))
    (present : edges.any (leaf "?any") = true)
    (opened : edges.any (leaf "?") = true) (blocked : edges.any (leaf "?nodefault") = true) :
    narrowHeads edges ≠ SourceCurriedDefaulting.narrowHeads edges := by
  rw [SourceCurriedDefaulting.narrow_no_default edges opened blocked]
  obtain ⟨marker, member, marked⟩ := List.any_eq_true.mp present
  have survives := (narrow_any_member edges present marker).mpr ⟨member, marked⟩
  intro same
  rw [same] at survives
  cases survives

/-- Filtering keeps two occurrences of the same actual shared-heap marker record. -/
theorem duplicate_occurrences :
    narrowHeads [markerFirst.1, integerSecond.1, markerFirst.1] = [markerFirst.1, markerFirst.1] := rfl

/-- An actually built nonleaf with the marker name does not trigger the marker branch. -/
theorem physical_nonleaf :
    let nonleaf := run (makeEdge "?any" () [.empty]) integerSecond.2
    narrowHeads [nonleaf.1, integerSecond.1] = [nonleaf.1, integerSecond.1] := rfl

#print axioms any_overrides_head_rejection
#check @any_overrides_head_rejection
#print axioms duplicate_occurrences
#check @duplicate_occurrences
#print axioms physical_nonleaf
#check @physical_nonleaf
end MicroCFTA.CurrentCurriedDefaultingIndependent
