import MicroCFTA.SourceCurriedDefaulting

/-!
# Current local filtering of curried type markers

The TypeDomain marker takes precedence over head defaulting. Filtering
retains the complete physical rows in their original order. Agreement with
the earlier filter requires absence of the TypeDomain marker. Domain-map
construction, kind checking, GHC instance pruning, and synthesis correctness
remain separate.
-/
namespace MicroCFTA.SourceCurrentCurriedDefaulting
open InternedConstructorTemplates
open SourceCurriedDefaulting (leaf)

/-- Follow the TypeDomain marker before the source head-defaulting guards. -/
def narrowHeads (edges : List (EdgeValue String Guard)) : List (EdgeValue String Guard) :=
  if edges.any (leaf "?any") then edges.filter (leaf "?any")
  else if !(edges.any (leaf "?")) then edges
  else if edges.any (leaf "?nodefault") then []
  else edges.filter (leaf "List")

/-- An undetermined TypeDomain keeps only its original marker leaves. -/
theorem narrow_any (edges : List (EdgeValue String Guard))
    (present : edges.any (leaf "?any") = true) : narrowHeads edges = edges.filter (leaf "?any") := by
  simp only [narrowHeads, present, ↓reduceIte]

/-- The historical filter agrees when no TypeDomain marker is present. -/
theorem agrees_without_any (edges : List (EdgeValue String Guard))
    (absent : edges.any (leaf "?any") = false) : narrowHeads edges = SourceCurriedDefaulting.narrowHeads edges := by
  simp only [narrowHeads, absent, Bool.false_eq_true, ↓reduceIte, SourceCurriedDefaulting.narrowHeads]

/-- Without either open marker, every physical row remains. -/
theorem narrow_no_open (edges : List (EdgeValue String Guard))
    (noAny : edges.any (leaf "?any") = false) (noOpen : edges.any (leaf "?") = false) :
    narrowHeads edges = edges := by
  rw [agrees_without_any edges noAny, SourceCurriedDefaulting.narrow_no_open edges noOpen]

/-- Head rejection requires the TypeDomain marker to be absent. -/
theorem narrow_no_default (edges : List (EdgeValue String Guard))
    (noAny : edges.any (leaf "?any") = false) (opened : edges.any (leaf "?") = true)
    (blocked : edges.any (leaf "?nodefault") = true) : narrowHeads edges = [] := by
  rw [agrees_without_any edges noAny, SourceCurriedDefaulting.narrow_no_default edges opened blocked]

/-- Defaultable heads keep the original List leaves after the TypeDomain check. -/
theorem narrow_list (edges : List (EdgeValue String Guard))
    (noAny : edges.any (leaf "?any") = false) (opened : edges.any (leaf "?") = true)
    (allowed : edges.any (leaf "?nodefault") = false) : narrowHeads edges = edges.filter (leaf "List") := by
  rw [agrees_without_any edges noAny, SourceCurriedDefaulting.narrow_list edges opened allowed]

/-- TypeDomain filtering retains exactly the original matching occurrences. -/
theorem narrow_any_member (edges : List (EdgeValue String Guard))
    (present : edges.any (leaf "?any") = true) (edge : EdgeValue String Guard) :
    edge ∈ narrowHeads edges ↔ edge ∈ edges ∧ leaf "?any" edge = true := by
  rw [narrow_any edges present, List.mem_filter]

/-- Filtering retains complete records, source order, and duplicate occurrences. -/
theorem narrow_sublist (edges : List (EdgeValue String Guard)) : (narrowHeads edges).Sublist edges := by
  cases present : edges.any (leaf "?any") with
  | true => rw [narrow_any edges present]; exact List.filter_sublist
  | false => rw [agrees_without_any edges present]; exact SourceCurriedDefaulting.narrow_sublist edges

/-- Repeating the current local filter makes no additional change. -/
theorem narrow_idempotent (edges : List (EdgeValue String Guard)) : narrowHeads (narrowHeads edges) = narrowHeads edges := by
  cases present : edges.any (leaf "?any") with
  | true =>
      have remains : (edges.filter (leaf "?any")).any (leaf "?any") = true := by
        obtain ⟨edge, member, marker⟩ := List.any_eq_true.mp present
        exact List.any_eq_true.mpr ⟨edge, List.mem_filter.mpr ⟨member, marker⟩, marker⟩
      rw [narrow_any edges present, narrow_any _ remains]
      simp only [List.filter_filter, Bool.and_self]
  | false =>
      have absent : (SourceCurriedDefaulting.narrowHeads edges).any (leaf "?any") = false := by
        rw [List.any_eq_false]
        intro edge member
        exact (List.any_eq_false.mp present) edge ((SourceCurriedDefaulting.narrow_sublist edges).subset member)
      rw [agrees_without_any edges present, agrees_without_any _ absent, SourceCurriedDefaulting.narrow_idempotent]

/-- The first fixture leaf is built in the empty physical constructor heap. -/
def markerFirst := run (makeEdge "?any" () []) empty

/-- The second leaf is built in the actual heap returned by the first request. -/
def integerSecond := run (makeEdge "Int" () []) markerFirst.2

/-- Two complete physical rows witness the changed no-open-marker law. -/
def counterexample : List (EdgeValue String Unit) := [markerFirst.1, integerSecond.1]

/-- The fixture contains actual distinct sequentially allocated leaf records. -/
theorem counterexample_fields : markerFirst.1.entry.key.symbol = "?any" ∧
    integerSecond.1.entry.key.symbol = "Int" ∧ markerFirst.1.entry.identity = 0 ∧
    integerSecond.1.entry.identity = 1 := by decide

/-- This source-built list has no historical open marker. -/
theorem counterexample_no_open : counterexample.any (leaf "?") = false := by decide

/-- The current filter selects the TypeDomain marker from the actual shared heap. -/
theorem counterexample_current : narrowHeads counterexample = [markerFirst.1] := rfl

/-- Absence of the old open marker does not imply identity for the current filter. -/
theorem counterexample_changed : narrowHeads counterexample ≠ SourceCurriedDefaulting.narrowHeads counterexample := by
  rw [counterexample_current, SourceCurriedDefaulting.narrow_no_open counterexample counterexample_no_open]
  intro same
  have lengths := congrArg List.length same
  change 1 = 2 at lengths
  contradiction

end MicroCFTA.SourceCurrentCurriedDefaulting
