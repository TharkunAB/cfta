import MicroCFTA.SourceSizedReference
import MicroCFTA.CanonicalClasses
import MicroCFTA.SourceCyclicAutomaton

/-!
# Finite preprocessing for the explicit Sized graph

The graph carrier is the validated finite state domain. It contains every
child state. Canonical refinement sees every original row. Row sorting then
uses arity, symbol, and the canonical classes of the ordered children.
Guards stay attached to their rows. This is the source `sortedRows` boundary;
it does not pass through the interned constructor or trim the graph.
-/

namespace MicroCFTA.SourceSizedRows

open Language RecursiveSize Std
attribute [local instance] lexOrd

/-- The finite validated state domain and its original guarded rows. -/
structure Input (State Symbol : Type) where
  nodes : List State
  complete : ∀ state, state ∈ nodes
  distinct : nodes.Nodup
  rows : Automaton State Symbol

/-- Canonical refinement reads arity and symbol, without erasing stored guards. -/
def graph (input : Input State Symbol) : CanonicalClasses.Graph State (Nat × Symbol) where
  nodes := input.nodes
  complete := input.complete
  distinct := input.distinct
  rows state := (input.rows state).map fun edge => ((edge.children.length, edge.label), edge.children)

/-- The source row key includes all children in their original order. -/
def rowKey (classes : State → Nat) (edge : Edge State Symbol) : (Nat × Symbol) × List Nat :=
  ((edge.children.length, edge.label), edge.children.map classes)

/-- Sort original rows by the completed canonical table. -/
def sortedRows [Ord Symbol] (input : Input State Symbol) (classes : State → Nat) :
    Automaton State Symbol :=
  fun state => (input.rows state).mergeSort fun first second =>
    (compare (rowKey classes first) (rowKey classes second)).isLE

/-- Run canonical refinement before sorting the original graph rows. -/
def prepare [DecidableEq Symbol] [Ord Symbol] (input : Input State Symbol) :
    Option (Automaton State Symbol) :=
  (CanonicalClasses.canonical (graph input)).map (sortedRows input)

/-- Finite canonical preprocessing completes for every validated graph. -/
theorem prepare_complete [DecidableEq Symbol] [Ord Symbol] (input : Input State Symbol) :
    ∃ output, prepare input = some output := by
  obtain ⟨classes, complete⟩ := CanonicalClasses.canonical_terminates (graph input)
  exact ⟨sortedRows input classes, by simp [prepare, complete]⟩

/-- Row sorting changes only order, including rows with equal keys. -/
theorem sortedRows_perm [Ord Symbol] (input : Input State Symbol) (classes : State → Nat)
    (state : State) : (sortedRows input classes state).Perm (input.rows state) :=
  List.mergeSort_perm _ _

/-- The prepared rows have the exact original constrained language. -/
theorem prepare_language [DecidableEq Symbol] [Ord Symbol] (input : Input State Symbol)
    (output : Automaton State Symbol) (finished : prepare input = some output)
    (state : State) (term : Term Symbol) :
    Accepts output state term ↔ Accepts input.rows state term := by
  unfold prepare at finished
  obtain ⟨classes, _, same⟩ := Option.map_eq_some_iff.mp finished
  subst output
  exact SourceCyclicAutomaton.permutation_language input.rows (sortedRows input classes)
    (sortedRows_perm input classes) state term

/-- Every finite size query after canonical preprocessing is exact. -/
theorem prepared_class_exact [DecidableEq Symbol] [Ord Symbol] (input : Input State Symbol)
    (output : Automaton State Symbol) (finished : prepare input = some output)
    (size : Nat) (state : State) (term : Term Symbol) :
    term ∈ SourceSizedReference.classes output size state ↔
      Accepts input.rows state term ∧ nodeSize term = size := by
  rw [SourceSizedReference.mem_classes_iff, prepare_language input output finished]

/-- Preprocessing and exact finite classes require no successful interned construction. -/
theorem exact_classes_exist [DecidableEq Symbol] [Ord Symbol] (input : Input State Symbol) :
    ∃ output, prepare input = some output ∧
      ∀ size state, (SourceSizedReference.classes output size state).Nodup ∧
        ∀ term, term ∈ SourceSizedReference.classes output size state ↔
          Accepts input.rows state term ∧ nodeSize term = size := by
  obtain ⟨output, finished⟩ := prepare_complete input
  exact ⟨output, finished, fun size state =>
    ⟨SourceSizedReference.classes_nodup output size state,
      prepared_class_exact input output finished size state⟩⟩

end MicroCFTA.SourceSizedRows
