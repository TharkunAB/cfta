import MicroCFTA.KeyedNaryFields
import MicroCFTA.KeyedSourceUnfolding

/-!
# Complete callback inverse of a mutually recursive key family

Each key uses its actual value count and independent member-term selector.
The grouped minimum and guard checks justify the full class equations.
A family occurrence consumes the source AtKey and Family boundary.
-/
namespace MicroCFTA.KeyedNaryInverse
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveCallbackDistinct
open RecursiveFieldBounds KeyedNaryFields
open KeyedNaryAlignment (valueProgram sourceWrap sourceTermProgram)

/-- All keys pass the actual grouped minimum and body guard checks. -/
def Guarded (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Body Key Root Symbol Root) : Prop :=
  ∀ key, KeyedSource.guarded (valueProgram program key)
    (KeyedSource.minima keys complete (valueProgram program)) = true

/-- Counts come from the value index for the selected key. -/
def rootCounts (program : Key → Body Key Root Symbol Root) (key : Key) (size : Nat) : Nat :=
  Decoder.count (KeyedSource.family (valueProgram program) size key).members.plan

/-- The independent term index returns the complete key member boundary. -/
def rootSelect (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (key : Key) (position : Position) : Option (EngineTerm Symbol) :=
  Decoder.decode (KeyedSource.family (sourceTermProgram code program) position.size key).members.plan position.rank

/-- Each key retains its own forward fields before any recursive callback is supplied. -/
def rootField (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (callbacks : Key → Callback Symbol) (key : Key) : Finite Symbol :=
  ⟨rootCounts program key, rootSelect code program key, callbacks key⟩

/-- Every term selector has exactly the interval of its corresponding value count. -/
theorem root_indexed (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (callbacks : Key → Callback Symbol) (key : Key) : FiniteIndex (rootField code program callbacks key) := by
  intro position
  change (∃ term, rootSelect code program key position = some term) ↔ position.rank < rootCounts program key position.size
  rw [rootCounts, ← (KeyedNaryAlignment.class_counts (sourceWrap code) program position.size key).2]
  constructor
  · rintro ⟨term, selected⟩; exact SamplerReplay.decoded_bound _ _ _ selected
  · intro within; exact Decoder.decode_exists _ _ within

/-- The per-key field table is the independently compiled source term class. -/
theorem root_class (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (callbacks : Key → Callback Symbol) (key : Key) (size : Nat) :
    finiteClass (rootField code program callbacks key) size =
      KeyedSource.languageClass (sourceTermProgram code program) size key := by
  apply List.ext_getElem?
  intro rank
  apply Option.ext
  intro term
  rw [finite_lookup _ (root_indexed code program callbacks key) ⟨size, rank⟩ term]
  simp only [rootField, rootSelect, Decoder.decode_correct, KeyedSource.family_values]

/-- The simultaneous field environment contains exactly the actual keyed term classes. -/
theorem root_environment (code : Key → Nat) (program : Key → Body Key Root Symbol Root)
    (callbacks : Key → Callback Symbol) :
    (fun key => finiteClass (rootField code program callbacks key)) =
      fun key size => KeyedSource.languageClass (sourceTermProgram code program) size key := by
  funext key size
  exact root_class code program callbacks key size

/-- Each actual member selector is its compiled body selector under the exact source key wrapper. -/
theorem selector_knot [DecidableEq Symbol] (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (callbacks : LeafCallbacks Symbol) (program : Key → Body Key Root Symbol Root)
    (accepted : Guarded keys complete program) (rootCallbacks : Key → Callback Symbol)
    (key : Key) (position : Position) :
    rootSelect code program key position =
      ((compile callbacks (rootField code program rootCallbacks) (program key)).select position).map
        (KeyedTermBoundary.atKeyTerm (code key)) := by
  rw [RecursiveNaryInverse.select_class _ (compiled_indexed callbacks _ (root_indexed code program rootCallbacks) (program key)),
    compiled_classes callbacks _ (root_indexed code program rootCallbacks) (program key) position.size,
    root_environment]
  rw [rootSelect, Decoder.decode_correct, KeyedSource.family_values,
    KeyedSourceUnfolding.languageClass_unfold keys complete (sourceTermProgram code program)
      (KeyedNaryAlignment.family_guards keys complete (sourceWrap code) program accepted).2]
  simp only [sourceTermProgram, KeyedNaryAlignment.termProgram, sourceWrap, KeyedSource.values, List.getElem?_map]

/-- The simultaneous source count equations follow from the complete ordered classes. -/
theorem count_knot [DecidableEq Symbol] (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (callbacks : LeafCallbacks Symbol) (program : Key → Body Key Root Symbol Root)
    (accepted : Guarded keys complete program) (rootCallbacks : Key → Callback Symbol) (key : Key) (size : Nat) :
    rootCounts program key size = (compile callbacks (rootField code program rootCallbacks) (program key)).counts size := by
  have aligned := congrArg List.length
    (compiled_classes callbacks _ (root_indexed code program rootCallbacks) (program key) size)
  rw [finite_length, root_environment] at aligned
  rw [rootCounts, ← (KeyedNaryAlignment.class_counts (sourceWrap code) program size key).2, KeyedSource.family_count]
  change (KeyedSource.languageClass (sourceTermProgram code program) size key).length = _
  rw [KeyedSourceUnfolding.languageClass_unfold keys complete (sourceTermProgram code program)
      (KeyedNaryAlignment.family_guards keys complete (sourceWrap code) program accepted).2]
  simp only [sourceTermProgram, KeyedNaryAlignment.termProgram, KeyedSource.values, List.length_map]
  exact aligned.symm

/-- Every family boundary spends one fuel unit before it enters the selected key's body. -/
def fuelPositions [DecidableEq Symbol] (code : Key → Nat) (callbacks : LeafCallbacks Symbol)
    (program : Key → Body Key Root Symbol Root) : Nat → Key → Callback Symbol
  | 0 => fun _ _ _ => []
  | fuel + 1 => fun key => KeyedTermBoundary.positions (code key)
      (compile callbacks (rootField code program (fuelPositions code callbacks program fuel)) (program key))

/-- The whole actual root field equals the source member wrapper around its compiled body. -/
theorem field_succ [DecidableEq Symbol] (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (callbacks : LeafCallbacks Symbol) (program : Key → Body Key Root Symbol Root)
    (accepted : Guarded keys complete program) (fuel : Nat) (key : Key) :
    rootField code program (fuelPositions code callbacks program (fuel + 1)) key =
      KeyedTermBoundary.field (code key)
        (compile callbacks (rootField code program (fuelPositions code callbacks program fuel)) (program key)) := by
  simp only [rootField, KeyedTermBoundary.field]
  congr 1
  · funext size
    exact count_knot keys complete code callbacks program accepted (fuelPositions code callbacks program fuel) key size
  · funext position
    exact selector_knot keys complete code callbacks program accepted (fuelPositions code callbacks program fuel) key position

/-- The requested forest height gives enough fuel simultaneously for every key's inverse. -/
theorem fuel_exact [DecidableEq Symbol] (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (callbacks : LeafCallbacks Symbol) (program : Key → Body Key Root Symbol Root)
    (accepted : Guarded keys complete program) (leaves : ∀ key, LeavesExact callbacks (program key))
    (fuel : Nat) : ∀ key, ExactBelow fuel (rootField code program (fuelPositions code callbacks program fuel) key) := by
  induction fuel with
  | zero =>
      intro key view wanted bound position
      constructor
      · simp [rootField, fuelPositions]
      · rintro ⟨term, selected, projected⟩
        change rootSelect code program key position = some term at selected
        rw [selector_knot keys complete code callbacks program accepted (fuelPositions code callbacks program 0) key position] at selected
        obtain ⟨child, _, rfl⟩ := Option.map_eq_some_iff.mp selected
        have present := (KeyedTermBoundary.unwrap_some (code key) wanted child).mpr
          (projected.symm.trans (KeyedTermBoundary.project_member _ _ view))
        have descent := KeyedTermBoundary.unwrap_height (code key) wanted child present
        omega
  | succ fuel ih =>
      intro key
      rw [field_succ keys complete code callbacks program accepted fuel key]
      apply KeyedTermBoundary.field_exact_below
      exact compiled_exact_below callbacks _ (root_indexed code program _) fuel ih (program key) (leaves key)

/-- All fuel-bounded candidates retain the selected key's actual counted interval. -/
theorem fuel_bounded [DecidableEq Symbol] (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (callbacks : LeafCallbacks Symbol) (program : Key → Body Key Root Symbol Root)
    (accepted : Guarded keys complete program) (leaves : ∀ key, LeavesBounded callbacks (program key)) (fuel : Nat) :
    ∀ key, RecursiveNaryChoice.Bounded (rootField code program (fuelPositions code callbacks program fuel) key) := by
  induction fuel with
  | zero => intro key view wanted row member; simp [rootField, fuelPositions] at member
  | succ fuel ih =>
      intro key
      rw [field_succ keys complete code callbacks program accepted fuel key]
      exact KeyedTermBoundary.field_bounded _ _ (compiled_bounded callbacks _ ih (program key) (leaves key))

/-- Every key retains source candidate order at every fuel amount. -/
theorem fuel_ordered [DecidableEq Symbol] (code : Key → Nat) (callbacks : LeafCallbacks Symbol)
    (program : Key → Body Key Root Symbol Root) (leaves : ∀ key, LeavesOrdered callbacks (program key)) (fuel : Nat) :
    ∀ key view wanted, (fuelPositions code callbacks program fuel key view wanted).Pairwise (fun a b => before a b) := by
  induction fuel with
  | zero => intro key view wanted; exact List.Pairwise.nil
  | succ fuel ih =>
      intro key
      exact KeyedTermBoundary.field_ordered _ _ (compiled_ordered callbacks _ ih (program key) (leaves key))

/-- Every key retains distinct valid positions for both checked flags. -/
theorem fuel_distinct [DecidableEq Symbol] (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (callbacks : LeafCallbacks Symbol) (program : Key → Body Key Root Symbol Root)
    (accepted : Guarded keys complete program) (bounded : ∀ key, LeavesBounded callbacks (program key))
    (distinct : ∀ key, LeavesDistinct callbacks (program key)) (fuel : Nat) :
    ∀ key, RecursiveNaryChoice.Unique (rootField code program (fuelPositions code callbacks program fuel) key) := by
  induction fuel with
  | zero => intro key view wanted; exact List.Pairwise.nil
  | succ fuel ih =>
      intro key
      rw [field_succ keys complete code callbacks program accepted fuel key]
      exact KeyedTermBoundary.field_distinct _ _ (compiled_distinct callbacks _
        (fuel_bounded keys complete code callbacks program accepted bounded fuel) ih (program key) (bounded key) (distinct key))

/-- The inverse uses only the finite requested forest to select its recursion bound. -/
def positions [DecidableEq Symbol] (code : Key → Nat) (callbacks : LeafCallbacks Symbol)
    (program : Key → Body Key Root Symbol Root) (key : Key) : Callback Symbol :=
  fun view wanted => fuelPositions code callbacks program (forestHeight wanted) key view wanted

/-- Complete checked candidates are exactly the selected key's decoder preimages. -/
theorem positions_exact [DecidableEq Symbol] (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (callbacks : LeafCallbacks Symbol) (program : Key → Body Key Root Symbol Root)
    (accepted : Guarded keys complete program) (leaves : ∀ key, LeavesExact callbacks (program key))
    (key : Key) (view : View) (wanted : List (EngineTerm Symbol)) (position : Position) :
    (position, true) ∈ positions code callbacks program key view wanted ↔
      ∃ term, rootSelect code program key position = some term ∧ project view term = wanted :=
  fuel_exact keys complete code callbacks program accepted leaves (forestHeight wanted) key view wanted (Nat.le_refl _) position

/-- Both checked flags stay inside the actual per-key value-count interval. -/
theorem positions_bounded [DecidableEq Symbol] (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (callbacks : LeafCallbacks Symbol) (program : Key → Body Key Root Symbol Root)
    (accepted : Guarded keys complete program) (leaves : ∀ key, LeavesBounded callbacks (program key))
    (key : Key) (view : View) (wanted : List (EngineTerm Symbol)) (row : Checked)
    (member : row ∈ positions code callbacks program key view wanted) : row.1.rank < rootCounts program key row.1.size :=
  fuel_bounded keys complete code callbacks program accepted leaves (forestHeight wanted) key view wanted row member

/-- Complete per-key candidate lists keep source order. -/
theorem positions_ordered [DecidableEq Symbol] (code : Key → Nat) (callbacks : LeafCallbacks Symbol)
    (program : Key → Body Key Root Symbol Root) (leaves : ∀ key, LeavesOrdered callbacks (program key))
    (key : Key) (view : View) (wanted : List (EngineTerm Symbol)) :
    (positions code callbacks program key view wanted).Pairwise (fun a b => before a b) :=
  fuel_ordered code callbacks program leaves (forestHeight wanted) key view wanted

/-- Per-key candidates cannot repeat a source position before replay filtering. -/
theorem positions_distinct [DecidableEq Symbol] (keys : List Key) (complete : ∀ key, key ∈ keys)
    (code : Key → Nat) (callbacks : LeafCallbacks Symbol) (program : Key → Body Key Root Symbol Root)
    (accepted : Guarded keys complete program) (bounded : ∀ key, LeavesBounded callbacks (program key))
    (distinct : ∀ key, LeavesDistinct callbacks (program key))
    (key : Key) (view : View) (wanted : List (EngineTerm Symbol)) :
    Distinct (positions code callbacks program key view wanted) :=
  fuel_distinct keys complete code callbacks program accepted bounded distinct (forestHeight wanted) key view wanted

end MicroCFTA.KeyedNaryInverse
