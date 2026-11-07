import MicroCFTA.SourceSizedPreprocessing

/-!
# Annotation erasure before canonical sorting

The source plain count table erases all original annotations before it
sorts the rows. Canonical graph refinement and row comparison inspect
labels and children. They do not inspect annotations.

Erasing annotations therefore retains every canonical class and every
sorted transition position. True-guard interpretation gives the same
automaton whether erasure precedes or follows canonical sorting.
This module uses the existing finite Input carrier. It does not prove
native storage or execution resource bounds.
-/
namespace MicroCFTA.SourceSizedAnnotationErasure
open Language SourceSizedDecided SourceSizedPreprocessing

/-- Replace one annotation by Unit without changing its label or child sequence. -/
def eraseRow (row : Row State Symbol Payload) : Row State Symbol Unit :=
  ⟨row.label, row.children, ()⟩

/-- Retain the original finite carrier and erase every original row annotation. -/
def eraseInput (input : Input State Symbol Payload) : Input State Symbol Unit where
  root := input.root
  states := input.states
  complete := input.complete
  distinct := input.distinct
  rows state := (input.rows state).map eraseRow

/-- Canonical graph preparation does not inspect original annotations. -/
theorem graph_eraseInput (input : Input State Symbol Payload) :
    graph (eraseInput input) = graph input := by
  simp only [graph, eraseInput, List.map_map, Function.comp_def, eraseRow]

/-- Every canonical row comparison key survives annotation erasure exactly. -/
theorem rowKey_eraseRow (classes : State → Nat) (row : Row State Symbol Payload) :
    rowKey classes (eraseRow row) = rowKey classes row := rfl

/-- Stable sorting at fixed canonical classes commutes with annotation erasure. -/
theorem sortRows_eraseInput [Ord Symbol] (input : Input State Symbol Payload)
    (classes : State → Nat) (state : State) :
    sortRows (eraseInput input) classes state = (sortRows input classes state).map eraseRow := by
  symm
  apply List.map_mergeSort
  intro first _ second _
  simp only [rowKey_eraseRow]

/-- Computed canonical sorting retains the same positions after annotation erasure. -/
theorem sortedRows_eraseInput [DecidableEq Symbol] [Ord Symbol]
    (input : Input State Symbol Payload) (state : State) :
    sortedRows (eraseInput input) state = (sortedRows input state).map eraseRow := by
  unfold sortedRows
  rw [graph_eraseInput]
  exact sortRows_eraseInput input _ state

/-- Erasing annotations leaves true-guard row interpretation unchanged. -/
theorem automaton_eraseRows (rows : State → List (Row State Symbol Payload)) :
    automaton (fun state => (rows state).map eraseRow) (fun _ _ => true) =
      automaton rows (fun _ _ => true) := by
  funext state
  simp only [automaton, List.map_map, Function.comp_def, eraseRow, Row.edge]
  rfl

/-- Erasing before the actual canonical sort gives the same plain counting automaton. -/
theorem sorted_automaton [DecidableEq Symbol] [Ord Symbol] (input : Input State Symbol Payload) :
    automaton (sortedRows (eraseInput input)) (fun _ _ => true) =
      automaton (sortedRows input) (fun _ _ => true) := by
  have rowsEqual : sortedRows (eraseInput input) =
      fun state => (sortedRows input state).map eraseRow := funext (sortedRows_eraseInput input)
  rw [rowsEqual]
  exact automaton_eraseRows (sortedRows input)

end MicroCFTA.SourceSizedAnnotationErasure
