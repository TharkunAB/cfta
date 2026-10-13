import MicroCFTA.SourceSizedFiniteKeys

/-!
# Actual dense canonical sorting on an explicit finite row map

Sized.sortedRows numbers the original Map.keys for canonical refinement.
It sorts and returns the original transitions. This module derives exact
row equality with the finite public input, including tied transitions.
-/
namespace MicroCFTA.SourceSizedFiniteKeys
open Language SourceSizedDecided SourceDenseRows Std
attribute [local instance] lexOrd

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]
  [DecidableEq Symbol] [Ord Symbol] [TransOrd Symbol] [LawfulEqOrd Symbol]
  (table : Table State Symbol Payload) (root : State)
  (success : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
    .ok (interpreted table (fun _ _ => true)))

/-- The actual numbered graph is used only for canonical refinement. -/
def denseClasses : Fin (SourceDenseRows.keys table).length → Nat :=
  (CanonicalClasses.canonical (SourceDenseRowsCanonical.denseGraph (SourceDenseRows.keys table)
    (automaton (input table root success).rows (fun _ _ => true)) id)).getD (fun _ => 0)

/-- Every declared original state reads exactly its canonical finite-carrier class. -/
theorem dense_at_number (state : Member (SourceDenseRows.keys table)) :
    denseClasses table root success (number (SourceDenseRows.keys table) state) =
      ((CanonicalClasses.canonical (SourceSizedPreprocessing.graph (input table root success))).getD (fun _ => 0)) state := by
  unfold denseClasses
  rw [canonical_numbering table root success]
  cases CanonicalClasses.canonical (SourceSizedPreprocessing.graph (input table root success)) <;>
    simp [unnumber_number]

/-- The source partial Map lookup has a value at every validated child key. -/
def classOf (state : State) : Nat :=
  if present : state ∈ SourceDenseRows.keys table then
    denseClasses table root success (number (SourceDenseRows.keys table) ⟨state, present⟩)
  else 0

/-- The unused outside-key default cannot affect any stored transition. -/
theorem classOf_member (state : Member (SourceDenseRows.keys table)) :
    classOf table root success state.val =
      ((CanonicalClasses.canonical (SourceSizedPreprocessing.graph (input table root success))).getD (fun _ => 0)) state := by
  unfold classOf
  rw [dite_eq_left state.property]
  exact dense_at_number table root success state

/-- The source sort retains original states, symbols, constraints, and repeated rows. -/
def nativeSorted : State → List (Row State Symbol Payload) :=
  fun state => (lookup table state).mergeSort fun first second =>
    (compare (SourceSizedPreprocessing.rowKey (classOf table root success) first)
      (SourceSizedPreprocessing.rowKey (classOf table root success) second)).isLE

/-- Exact row keys follow from the derived numbered-map roundtrips. -/
theorem rowKey_forget (edge : Row (Member (SourceDenseRows.keys table)) Symbol Payload) :
    SourceSizedPreprocessing.rowKey (classOf table root success) (forget edge) =
      SourceSizedPreprocessing.rowKey
        ((CanonicalClasses.canonical (SourceSizedPreprocessing.graph (input table root success))).getD (fun _ => 0)) edge := by
  simp only [SourceSizedPreprocessing.rowKey, forget, List.length_map, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro child _
  exact classOf_member table root success child

/-- Actual dense source sorting equals the finite public worker row for row. -/
theorem sorted_readback (state : Member (SourceDenseRows.keys table)) :
    (SourceSizedPreprocessing.sortedRows (input table root success) state).map forget =
      nativeSorted table root success state.val := by
  unfold SourceSizedPreprocessing.sortedRows SourceSizedPreprocessing.sortRows nativeSorted
  rw [←rows_readback table (validated_closed table root success) state]
  change List.map forget ((restricted table _ state).mergeSort _) =
    ((restricted table _ state).map forget).mergeSort _
  apply List.map_mergeSort
  intro first _ second _
  rw [rowKey_forget table root success first, rowKey_forget table root success second]

/-- Full guarded first-occurrence class order agrees with the actual original-state sorted rows. -/
theorem sorted_classes_exact (holds : Payload → Term Symbol → Bool)
    (state : Member (SourceDenseRows.keys table)) (size : Nat) :
    SourceSizedReference.classes
      (automaton (SourceSizedPreprocessing.sortedRows (input table root success)) holds) size state =
      SourceSizedReference.classes (automaton (nativeSorted table root success) holds) size state.val := by
  symm
  apply SourceDenseRowsRestrict.guarded_classes_rename _ _ Subtype.val
  intro current
  rw [automaton, ←sorted_readback table root success current]
  simp only [List.map_map, automaton, Function.comp_def]
  rfl

end MicroCFTA.SourceSizedFiniteKeys
