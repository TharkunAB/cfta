import MicroCFTA.SourceSizedGroupedMinimum

/-!
# The actual minimum-presence gate on every output key

The source index reads no body when its key has no computed minimum.
The finite input for the minimum pass comes from actual preparation.
Undeclared keys have no rows. Every absent minimum therefore gives empty
classes at every size. No caller supplies productivity or gate correctness.
-/
namespace MicroCFTA.SourceSizedGroupedMinimumIndex
open Language RecursiveSize SourceSizedDecided SourceSizedFiniteKeys SourceDenseRows
open SourceSizedGroupedMinimum SourceSizedPrefixComputedMinimum

variable {State Symbol Formula : Type}
  [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol] [Ord Symbol]

/-- Read the actual computed minimum at declared keys and none outside the map. -/
def minimum (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) : Option Nat :=
  if present : key ∈ keys output then
    minimumNat (preparedInput original root output success) ⟨key, present⟩
  else none

/-- The source Map.member test reads presence in that computed minimum table. -/
def known (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) : Bool :=
  (minimum original root output success key).isSome

omit [Ord (List State)] [DecidableEq Symbol] [Ord Symbol] in
private theorem lookup_outside (table : Table State Symbol Payload) (state : State)
    (outside : state ∉ keys table) : lookup table state = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row member
  obtain ⟨entry, entryIn, produced⟩ := List.mem_flatMap.mp member
  by_cases same : entry.1 = state
  · exact outside ((mem_keys table state).mpr (List.mem_map.mpr ⟨entry, entryIn, same⟩))
  · simp [same] at produced

omit [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol] [Ord Symbol] in
private theorem classes_empty_of_rows_empty
    (rows : State → List (Row State Symbol (List (List Nat)))) (state : State)
    (empty : rows state = []) (size : Nat) : SourceSizedGroupedClasses.classes rows size state = [] := by
  cases size with
  | zero => exact SourceSizedGroupedClasses.classes_zero rows state
  | succ remaining =>
      rw [SourceSizedGroupedClasses.classes_succ, empty]
      rfl

/-- A declared lookup is exactly the minimum iteration on its derived finite key. -/
theorem minimum_declared (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (present : key ∈ keys output) :
    minimum original root output success key =
      minimumNat (preparedInput original root output success) ⟨key, present⟩ := by
  simp only [minimum, present, dite_true]

/-- Every absent computed key has no grouped member at any requested node count. -/
theorem minimum_none_iff (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output) (key : List State) :
    minimum original root output success key = none ↔
      ∀ size, SourceSizedGroupedClasses.classes (lookup output) size key = [] := by
  by_cases present : key ∈ keys output
  · rw [minimum_declared original root output success key present]
    simpa only [SourceSizedGroupedClasses.run_eq_classes] using
      prepared_minimumNat_none_iff original root output success ⟨key, present⟩
  · have empty := lookup_outside output key present
    simp only [minimum, present, dite_false, true_iff]
    exact classes_empty_of_rows_empty (lookup output) key empty

/-- A present computed minimum is attained and is no larger than every grouped member. -/
theorem minimum_is_least (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (size : Nat) (found : minimum original root output success key = some size) :
    (∃ term, term ∈ SourceSizedGroupedClasses.classes (lookup output) size key) ∧
      ∀ requested term, term ∈ SourceSizedGroupedClasses.classes (lookup output) requested key → size ≤ requested := by
  by_cases present : key ∈ keys output
  · rw [minimum_declared original root output success key present] at found
    simpa only [SourceSizedGroupedClasses.run_eq_classes] using
      prepared_minimumNat_is_least original root output success ⟨key, present⟩ size found
  · simp [minimum, present] at found

/-- Actual computed term minima are strictly positive. -/
theorem minimum_positive (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (size : Nat) (found : minimum original root output success key = some size) :
    0 < size := by
  obtain ⟨term, member⟩ := (minimum_is_least original root output success key size found).1
  have sized := ((SourceSizedGroupedClasses.prepared_run_iff original root output success size key term).mp
    (by simpa only [SourceSizedGroupedClasses.run_eq_classes] using member)).2
  have positive := nodeSize_pos term
  omega

/-- The actual false minimum-presence gate derives all empty class facts internally. -/
theorem known_false_empty (original : Table State Symbol (SourceSymbolicIndex.Constraint Formula))
    (root : State) (output : SourceSizedConjunctionWorklist.Stored State Symbol)
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (key : List State) (absent : known original root output success key = false) (size : Nat) :
    SourceSizedGroupedClasses.classes (lookup output) size key = [] := by
  cases read : minimum original root output success key with
  | none => exact (minimum_none_iff original root output success key).mp read size
  | some value => simp [known, read] at absent

end MicroCFTA.SourceSizedGroupedMinimumIndex
