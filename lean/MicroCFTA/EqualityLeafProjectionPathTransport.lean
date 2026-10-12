import MicroCFTA.EqualityLeafProjectionPathInputs
import MicroCFTA.EqualityLeafProjectionClosedWorkers

/-!
# Closed path projection through actual source rows

Each completed selected child projection obtains a finite represented raw
leaf. Later proof preparation preserves all earlier source results. The
ordered projected row list therefore supplies exact ordinary-union inputs.
-/
namespace MicroCFTA.EqualityLeafProjectionPathTransport
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionPathWorker EqualityLeafProjectionPathInputs
open EqualityLeafProjectionClosedWorkers (optional_bind_closed work_grows)
open EqualityRawLeafInventory (Leaf)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)
open EqualityLeafProjectionSyntax (Path)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- A completed actual endpoint projection has a finite represented raw leaf. -/
def Transport (initial : List (SourceGuards.Guard FullSyntax.Formula)) (symbols : Nat) (path : Path) : Prop :=
  ∀ state, Facts state → ∀ value, Input (build (initial := initial) (symbols := symbols)) path state value →
    ∀ result, run (read path value) state = (some result, state) →
      ∃ after, ∃ leaf : Leaf initial symbols, Facts after ∧ Grows state after ∧ Represents build (.leaf leaf) after result

/-- Completed source mapMaybe projections retain their exact original result order. -/
theorem rows_transport (path : Path) (transport : Transport initial symbols path) (index : Nat)
    (edges : List (EdgeValue (Fin symbols) ConstraintKey)) (state : State (Fin symbols) ConstraintKey)
    (facts : Facts state)
    (inputs : ∀ edge ∈ edges, ∀ child, edge.children[index]? = some child → Input (build (initial := initial)) path state child)
    (values : List (Value (Fin symbols) ConstraintKey))
    (closed : run (rows (read path) index edges) state = (some values, state)) :
    ∃ after, ∃ pairs : List (Leaf initial symbols × Value (Fin symbols) ConstraintKey),
      Facts after ∧ Grows state after ∧ pairs.map Prod.snd = values ∧
        ∀ pair ∈ pairs, Represents build (.leaf pair.1) after pair.2 := by
  induction edges generalizing state values with
  | nil =>
      have empty : [] = values := Option.some.inj (congrArg Prod.fst closed)
      exact ⟨state, [], facts, grows_refl state, empty, by simp⟩
  | cons edge rest ih =>
      simp only [rows] at closed
      split at closed
      · exact ih state facts (fun edge member => inputs edge (by simp [member])) values closed
      · rename_i child selected
        obtain ⟨value, firstClosed, remaining⟩ := optional_bind_closed _ _ state facts.coherent.valid values closed
        obtain ⟨tail, restClosed, returned⟩ := optional_bind_closed _ _ state facts.coherent.valid values remaining
        have order : value :: tail = values := Option.some.inj (congrArg Prod.fst returned)
        obtain ⟨middle, leaf, middleFacts, growth, represented⟩ :=
          transport state facts child (inputs edge (by simp) child selected) value firstClosed
        have tailReplay := work_grows (rows (read path) index rest) state middle facts.coherent.valid (some tail) restClosed growth
        have tailInputs : ∀ edge ∈ rest, ∀ child, edge.children[index]? = some child → Input (build (initial := initial)) path middle child := by
          intro edge member child selected
          exact input_grows build path state middle facts.coherent.valid growth child (inputs edge (by simp [member]) child selected)
        obtain ⟨after, pairs, afterFacts, later, same, tailRepresented⟩ := ih middle middleFacts tailInputs tail tailReplay
        refine ⟨after, (leaf, value) :: pairs, afterFacts, grows_trans growth later, ?_, ?_⟩
        · simpa only [List.map_cons, same] using order
        · intro pair member
          rcases List.mem_cons.mp member with equal | member
          · subst pair
            exact EqualityLeafProjectionRepresentation.grows build (.leaf leaf) middle after middleFacts.coherent.valid later value represented
          · exact tailRepresented pair member

end MicroCFTA.EqualityLeafProjectionPathTransport
