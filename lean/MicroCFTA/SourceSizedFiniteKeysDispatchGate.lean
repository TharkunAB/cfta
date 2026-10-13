import MicroCFTA.SourceSizedFiniteKeysCanonical
import MicroCFTA.SourceRowsMinimumShape
import MicroCFTA.SourceCyclicRowsNativeGate

/-!
# Actual finite-map product minima in Sized dispatch

The raw product inventory contains exactly pairs of original table keys.
The source minimum recurrence terminates on this inventory even when the
state type is infinite. Its entries equal the finite-carrier product
minima through derived ordered readback and exact intersection language.
-/
namespace MicroCFTA.SourceSizedFiniteKeysDispatch
open Language RecursiveSize SourceSizedDecided SourceSizedFiniteKeys SourceSizedDispatcher
open SourceSizedPreprocessing SymbolicGraphView SourceDenseRows

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]

/-- A nonempty raw lookup must have an original declared table key. -/
theorem lookup_key (table : SourceSizedFiniteKeys.Table State Symbol Payload) (state : State)
    (row : Row State Symbol Payload) (member : row ∈ lookup table state) : state ∈ keys table := by
  obtain ⟨entry, present, found⟩ := List.mem_flatMap.mp member
  split at found
  next same => exact (mem_keys table state).mpr (List.mem_map.mpr ⟨entry, present, same⟩)
  next different => simp at found

variable [DecidableEq Symbol] [Ord Symbol] [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol]
  (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
  (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
    .ok (interpreted table (fun _ _ => true)))

/-- The actual source canonical rows recover every finite-carrier interpreted row in order. -/
theorem sorted_ordered (holds : Payload → Term Symbol → Bool) (state : Member (keys table)) :
    automaton (nativeSorted table root valid) holds state.val =
      (automaton (sortedRows (input table root valid)) holds state).map (renameEdge Subtype.val) := by
  rw [SourceSizedDecided.automaton, ← sorted_readback table root valid state]
  simp only [List.map_map, SourceSizedDecided.automaton, Function.comp_def]
  rfl

omit [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol] in
/-- Canonical source sorting cannot introduce rows outside the finite map key set. -/
theorem sorted_supported (holds : Payload → Term Symbol → Bool) :
    SourceRowsMinimum.Supported (automaton (nativeSorted table root valid) holds) (keys table) := by
  intro state edge member
  obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
  apply lookup_key table state row
  exact (List.mergeSort_perm _ _).mem_iff.mp present

omit [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol] in
/-- The finite raw synchronous product needs only the declared key pairs. -/
theorem product_supported : SourceRowsMinimum.Supported
    (Language.intersect (ordinaryRows (nativeSorted table root valid)) (ordinaryRows (nativeSorted table root valid)))
    (SourceSizedDispatchGraph.pairs (keys table)) := by
  intro pair edge member
  obtain ⟨first, firstIn, second, secondIn, _, _, _⟩ := (mem_intersect_iff _ _ pair.1 pair.2 edge).mp member
  have left := sorted_supported table root valid (fun _ _ => true) pair.1 first firstIn
  have right := sorted_supported table root valid (fun _ _ => true) pair.2 second secondIn
  exact List.mem_flatMap.mpr ⟨pair.1, left, List.mem_map.mpr ⟨pair.2, right, rfl⟩⟩

/-- Two finite-carrier states and their original identities have the same complete product language. -/
theorem product_language (left right : Member (keys table)) (term : Term Symbol) :
    Accepts (Language.intersect (ordinaryRows (sortedRows (input table root valid)))
      (ordinaryRows (sortedRows (input table root valid)))) (left, right) term ↔
    Accepts (Language.intersect (ordinaryRows (nativeSorted table root valid))
      (ordinaryRows (nativeSorted table root valid))) (left.val, right.val) term := by
  rw [accepts_intersect_iff, accepts_intersect_iff]
  have exactState := fun state => (rowsCorrespond_exact
    (ordinaryRows (sortedRows (input table root valid))) (ordinaryRows (nativeSorted table root valid)) Subtype.val
    (SourceCyclicRowsNativeGate.copied_of_ordered _ _ _ (sorted_ordered table root valid (fun _ _ => true))) state term).symm
  exact and_congr (exactState left) (exactState right)

/-- The polymorphic source recurrence equals the prior recurrence on a complete finite type. -/
theorem finite_minimum_eq [DecidableEq Finite]
    (A : Automaton Finite Alphabet) (plain : Decoder.Plain A)
    (states : List Finite) (complete : ∀ state, state ∈ states) (state : Finite) :
    SourceRowsMinimum.minimumSizes A states state = MinimumSize.minimumSizes A states complete state := by
  have support : SourceRowsMinimum.Supported A states := fun state _ _ => complete state
  cases found : SourceRowsMinimum.minimumSizes A states state with
  | none =>
    exact ((MinimumSize.minimumSizes_none_iff A plain states complete state).mpr
      ((SourceRowsMinimum.none_iff A plain states support state).mp found)).symm
  | some size =>
    exact ((MinimumSize.minimumSizes_correct A plain states complete state size).mpr
      ((SourceRowsMinimum.correct A plain states support state size).mp found)).symm

/-- Each actual raw pair minimum equals the finite public callback minimum exactly. -/
theorem minimum_eq (left right : Member (keys table)) :
    SourceRowsMinimum.minimumSizes
      (Language.intersect (ordinaryRows (nativeSorted table root valid)) (ordinaryRows (nativeSorted table root valid)))
      (SourceSizedDispatchGraph.pairs (keys table)) (left.val, right.val) =
    MinimumSize.minimumSizes
      (Language.intersect (ordinaryRows (sortedRows (input table root valid))) (ordinaryRows (sortedRows (input table root valid))))
      (SourceSizedDispatchGraph.pairs (input table root valid).states)
      (SourceSizedDispatchGraph.pairs_complete (input table root valid).states (input table root valid).complete) (left, right) := by
  have leftPlain := AutomatonAmbiguity.intersect_plain (ordinaryRows (sortedRows (input table root valid))) (ordinary_plain _)
  have rightPlain := AutomatonAmbiguity.intersect_plain (ordinaryRows (nativeSorted table root valid)) (ordinary_plain _)
  have same := SourceRowsMinimumShape.minimum_language _ _ leftPlain rightPlain
    (SourceSizedDispatchGraph.pairs (input table root valid).states) (SourceSizedDispatchGraph.pairs (keys table))
    (fun state _ _ => SourceSizedDispatchGraph.pairs_complete _ (input table root valid).complete state)
    (product_supported table root valid) (left, right) (left.val, right.val) (product_language table root valid left right)
  rw [← same]
  exact finite_minimum_eq _ leftPlain _ _ _

/-- The source gate reads membership in the actual finite product minimum map. -/
def overlap (left right : State) : Bool :=
  (SourceRowsMinimum.minimumSizes
    (Language.intersect (ordinaryRows (nativeSorted table root valid)) (ordinaryRows (nativeSorted table root valid)))
    (SourceSizedDispatchGraph.pairs (keys table)) (left, right)).isSome

/-- All finite source child pairs have the same exact callback result. -/
theorem overlap_eq (left right : Member (keys table)) : overlap table root valid left.val right.val =
    SourceSizedDispatchGraph.overlap (ordinaryRows (sortedRows (input table root valid)))
      (input table root valid).states (input table root valid).complete left right := by
  exact congrArg Option.isSome (minimum_eq table root valid left right)

/-- The actual source tails scan reads the finite raw map in key order. -/
def unambiguous : Bool :=
  !((keys table).any fun state => AutomatonAmbiguity.ambiguous (overlap table root valid)
    (ordinaryRows (nativeSorted table root valid) state))

/-- The complete source ambiguity gate equals the gate used by finite public dispatch. -/
theorem unambiguous_eq : unambiguous table root valid =
    SourceSizedDispatchGraph.unambiguousRows (ordinaryRows (sortedRows (input table root valid)))
      (input table root valid).states (input table root valid).complete := by
  have mapped : (keys table).attach.map Subtype.val = keys table := by simp
  unfold unambiguous SourceSizedDispatchGraph.unambiguousRows
  conv => lhs; rw [← mapped]
  simp only [List.any_map, Function.comp_def]
  apply congrArg Bool.not
  apply congrArg (fun predicate => (keys table).attach.any predicate)
  funext state
  simp only [ordinaryRows]
  rw [sorted_ordered table root valid (fun _ _ => true), SourceCyclicRowsNativeGate.ambiguous_rename]
  congr 1
  exact funext fun left => funext fun right => overlap_eq table root valid left right

omit [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol] in
/-- The actual raw product minimum worker reaches its fixed table after finitely many sweeps. -/
theorem gate_finite : ∃ fuel,
    MinimumSize.sweeps
      (Language.intersect (ordinaryRows (nativeSorted table root valid)) (ordinaryRows (nativeSorted table root valid)))
      (SourceSizedDispatchGraph.pairs (keys table)) fuel (fun _ => none) =
    SourceRowsMinimum.minimumSizes
      (Language.intersect (ordinaryRows (nativeSorted table root valid)) (ordinaryRows (nativeSorted table root valid)))
      (SourceSizedDispatchGraph.pairs (keys table)) := by
  exact ⟨_, (SourceRowsMinimum.terminates _ _).choose_spec.1⟩

end MicroCFTA.SourceSizedFiniteKeysDispatch
