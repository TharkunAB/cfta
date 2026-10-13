import MicroCFTA.SourceCyclicRows

/-!
# Colliding custom keys retain source order

Distinct leaf symbols can have the same user-supplied key. Their arities
and child-class lists also agree. The source stable sort therefore retains
their input order. Canonical numbering does not resolve these ties.
-/
namespace MicroCFTA.SourceCyclicRowsKeyTies
open Language

/-- Two distinct constants appear in one source order. -/
def first : Automaton Unit Nat := fun _ => [⟨0, [], fun _ => true⟩, ⟨1, [], fun _ => true⟩]

/-- The same constant language appears in the opposite source order. -/
def second : Automaton Unit Nat := fun _ => [⟨1, [], fun _ => true⟩, ⟨0, [], fun _ => true⟩]

/-- Every class assignment leaves both constant alternatives tied. -/
theorem first_sort (classes : Unit → Nat) :
    SourceDenseRowsCanonical.sortRows first (fun _ => (0 : Nat)) classes = first := by
  funext state
  simp [SourceDenseRowsCanonical.sortRows, SourceDenseRowsCanonical.transitionKey, first, List.mergeSort]

theorem second_sort (classes : Unit → Nat) :
    SourceDenseRowsCanonical.sortRows second (fun _ => (0 : Nat)) classes = second := by
  funext state
  simp [SourceDenseRowsCanonical.sortRows, SourceDenseRowsCanonical.transitionKey, second, List.mergeSort]

theorem first_terms : RecursiveSize.enumerate first 1 () = [Term.node 0 [], Term.node 1 []] := by
  simp [RecursiveSize.enumerate, first, RecursiveSize.forests, RecursiveSize.emptyForests]

theorem second_terms : RecursiveSize.enumerate second 1 () = [Term.node 1 [], Term.node 0 []] := by
  simp [RecursiveSize.enumerate, second, RecursiveSize.forests, RecursiveSize.emptyForests]

/-- A language-preserving input permutation can change rank zero under a colliding order key. -/
theorem tied_ranks :
    (∀ term, Accepts first () term ↔ Accepts second () term) ∧
      (RecursiveSize.enumerate (SourceDenseRowsCanonical.sortRows first (fun _ => (0 : Nat)) (fun _ => 0)) 1 ()) =
        [Term.node 0 [], Term.node 1 []] ∧
      (RecursiveSize.enumerate (SourceDenseRowsCanonical.sortRows second (fun _ => (0 : Nat)) (fun _ => 0)) 1 ()) =
        [Term.node 1 [], Term.node 0 []] := by
  refine ⟨?_, by rw [first_sort, first_terms], by rw [second_sort, second_terms]⟩
  intro term
  apply SourceCyclicAutomaton.permutation_language second first
  intro state
  exact List.Perm.swap _ _ []

/-- The first selected term changes while each decoder still has two distinct members. -/
theorem first_rank_differs :
    Decoder.decode (RecursiveSize.compileAt first 1 ()) 0 = some (.node 0 []) ∧
      Decoder.decode (RecursiveSize.compileAt second 1 ()) 0 = some (.node 1 []) ∧
      RecursiveSize.countAt first 1 () = 2 ∧ RecursiveSize.countAt second 1 () = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Decoder.decode_correct, RecursiveSize.values_compileAt]
    simp [first_terms]
  · rw [Decoder.decode_correct, RecursiveSize.values_compileAt]
    simp [second_terms]
  · rw [RecursiveSize.countAt_correct]
    simp [first_terms]
  · rw [RecursiveSize.countAt_correct]
    simp [second_terms]

end MicroCFTA.SourceCyclicRowsKeyTies
