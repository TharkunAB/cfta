import MicroCFTA.SourceFTAValidation
import MicroCFTA.SourceSizedFiniteKeys

/-!
# Finite Sized input under current structural validation

Current explicit FTAs can use one symbol at several arities. Structural
validation supplies the root and child key proofs. The existing finite
restriction and dense canonical sort then retain every original row.
The older ranked-alphabet validation boundary remains separate.
-/
namespace MicroCFTA.SourceSizedStructuralKeys
open Language SourceSizedDecided SourceDenseRows SourceSizedFiniteKeys Std
attribute [local instance] lexOrd

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]

/-- Successful structural validation derives raw child membership independently of guards. -/
theorem validated_closed (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) : Closed table := by
  have valid := (SourceFTAValidation.validateRows_exact root _).mp success
  intro state edge member child childIn
  have present : edge.edge (fun _ _ => true) ∈ FTAValidation.rowFor (interpreted table (fun _ _ => true)) state := by
    rw [interpreted_lookup]
    exact List.mem_map.mpr ⟨edge, member, rfl⟩
  obtain ⟨edges, row, found⟩ := (FTAValidation.rowFor_exact _ _ _).mp present
  have inEdges : edge.edge (fun _ _ => true) ∈ FTAValidation.edges (interpreted table (fun _ _ => true)) :=
    List.mem_flatMap.mpr ⟨(state, edges), row, found⟩
  apply (mem_keys table child).mpr
  rw [← interpreted_keys table (fun _ _ => true)]
  exact valid.2 _ inEdges child childIn

/-- Successful validation derives the initial state's finite key membership. -/
theorem validated_root (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) : root ∈ SourceDenseRows.keys table := by
  apply (mem_keys table root).mpr
  rw [← interpreted_keys table (fun _ _ => true)]
  exact ((SourceFTAValidation.validateRows_exact root _).mp success).1

/-- Declared roots and closed raw children derive current structural validation. -/
theorem validation_of_closed (table : Table State Symbol Payload) (root : State)
    (present : root ∈ SourceDenseRows.keys table) (closed : Closed table) :
    SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)) := by
  apply (SourceFTAValidation.validateRows_exact root _).mpr
  constructor
  · rw [interpreted_keys]
    exact (mem_keys table root).mp present
  · intro edge member child childIn
    obtain ⟨⟨state, outgoing⟩, row, edgeIn⟩ := List.mem_flatMap.mp member
    have found := (FTAValidation.rowFor_exact _ state edge).mpr ⟨outgoing, row, edgeIn⟩
    rw [interpreted_lookup] at found
    obtain ⟨raw, rawIn, rfl⟩ := List.mem_map.mp found
    rw [interpreted_keys]
    exact (mem_keys table child).mp (closed state raw rawIn child childIn)

/-- Build every finite-domain public input field from a successful explicit FTA validation. -/
def input (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) :
    SourceSizedPreprocessing.Input (Member (SourceDenseRows.keys table)) Symbol Payload where
  root := ⟨root, validated_root table root success⟩
  states := (SourceDenseRows.keys table).attach
  complete := member_complete _
  distinct := member_nodup _ (keys_nodup table)
  rows := restricted table (validated_closed table root success)

/-- The finite public input accepts exactly the source root language under arbitrary guards. -/
theorem input_language (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (holds : Payload → Term Symbol → Bool) (term : Term Symbol) :
    Accepts (automaton (input table root success).rows holds) (input table root success).root term ↔
      Accepts (automaton (lookup table) holds) root term :=
  accepts_exact table _ holds _ term

/-- Complete dense numbering computes exactly the canonical classes used by the finite public input. -/
theorem canonical_numbering [DecidableEq Symbol] [Ord Symbol] [TransOrd Symbol] [LawfulEqOrd Symbol]
    (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) :
    CanonicalClasses.canonical (SourceDenseRowsCanonical.denseGraph (SourceDenseRows.keys table)
      (automaton (input table root success).rows (fun _ _ => true)) id) =
      (CanonicalClasses.canonical (SourceSizedPreprocessing.graph (input table root success))).map
        (fun classes index => classes (unnumber (SourceDenseRows.keys table) index)) := by
  have same : SourceDenseRowsCanonical.sourceGraph (SourceDenseRows.keys table) (keys_nodup table)
      (automaton (input table root success).rows (fun _ _ => true)) id =
      SourceSizedPreprocessing.graph (input table root success) := by
    unfold SourceDenseRowsCanonical.sourceGraph SourceSizedPreprocessing.graph
    simp only [automaton, List.map_map, Function.comp_def, Row.edge, id_eq]
    rfl
  rw [←same]
  exact SourceDenseRowsCanonical.canonical_numbering _ (keys_nodup table) _ id

variable [DecidableEq Symbol] [Ord Symbol] [TransOrd Symbol] [LawfulEqOrd Symbol]
  (table : Table State Symbol Payload) (root : State)
  (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
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

omit [TransOrd Symbol] [LawfulEqOrd Symbol] in
/-- The computed dense canonical sort permutes each original alternative list. -/
theorem nativeSorted_perm (state : State) :
    (nativeSorted table root success state).Perm (lookup table state) :=
  List.mergeSort_perm _ _

omit [TransOrd Symbol] [LawfulEqOrd Symbol] in
/-- Guard interpretation retains that permutation without a row-order premise. -/
theorem sorted_automaton_perm (holds : Payload → Term Symbol → Bool) (state : State) :
    (automaton (nativeSorted table root success) holds state).Perm
      (FTAValidation.rowFor (interpreted table holds) state) := by
  rw [interpreted_lookup]
  exact (nativeSorted_perm table root success state).map _

end MicroCFTA.SourceSizedStructuralKeys
