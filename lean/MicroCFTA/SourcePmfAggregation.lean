import MicroCFTA.Probability
import MicroCFTA.CanonicalClasses

/-!
# Source PMF map aggregation

`Query.pmf`, `Query.pmfAtSize`, and `Sampler.exactPmfAtSize` use
`Map.fromListWith (+)` followed by ascending map readback. This module
models finite map insertion explicitly. Equal output values share one key.
Their masses add; their replay ranks and generator members remain distinct.
-/
namespace MicroCFTA.SourcePmfAggregation
open Probability

/-- Insert a map key or add the new mass to its existing mass. -/
def insert [DecidableEq Value] (mass : Rat) (value : Value) : Distribution Value → Distribution Value
  | [] => [(mass, value)]
  | (old, key) :: rest =>
      if value = key then (mass + old, key) :: rest else (old, key) :: insert mass value rest

/-- The source fromListWith worker processes entries from left to right. -/
def fromList [DecidableEq Value] (outcomes : Distribution Value) : Distribution Value :=
  outcomes.foldl (fun table entry => insert entry.1 entry.2 table) []

/-- Read the finite map in ascending output-key order. -/
def aggregate [DecidableEq Value] [Ord Value] (outcomes : Distribution Value) : Distribution Value :=
  (fromList outcomes).mergeSort fun first second => (compare first.2 second.2).isLE

/-- Public PMF rows put the value before its rational mass. -/
def pmf [DecidableEq Value] [Ord Value] (outcomes : Distribution Value) : List (Value × Rat) :=
  (aggregate outcomes).map fun entry => (entry.2, entry.1)

/-- Swapping public PMF columns recovers the aggregated probability distribution. -/
theorem pmf_distribution [DecidableEq Value] [Ord Value] (outcomes : Distribution Value) :
    (pmf outcomes).map Prod.swap = aggregate outcomes := by
  simp [pmf, List.map_map, Function.comp_def]

/-- A map insertion adds exactly its mass to every event containing its key. -/
theorem event_insert [DecidableEq Value] (event : Value → Bool) (mass : Rat) (value : Value)
    (table : Distribution Value) :
    eventMass event (insert mass value table) =
      (if event value then mass else 0) + eventMass event table := by
  induction table with
  | nil => simp [insert, eventMass]
  | cons entry rest ih =>
      obtain ⟨old, key⟩ := entry
      by_cases same : value = key
      · subst key
        cases verdict : event value <;> simp [insert, eventMass, verdict, Rat.add_assoc, Rat.zero_add]
      · simp only [insert, ite_eq_right same, eventMass, ih]
        simp [Rat.add_left_comm]

/-- A source fold adds the input event mass to its initial finite map. -/
theorem event_fold [DecidableEq Value] (event : Value → Bool)
    (outcomes table : Distribution Value) :
    eventMass event (outcomes.foldl (fun table entry => insert entry.1 entry.2 table) table) =
      eventMass event table + eventMass event outcomes := by
  induction outcomes generalizing table with
  | nil => simp [eventMass, Rat.add_zero]
  | cons entry rest ih =>
      obtain ⟨mass, value⟩ := entry
      rw [List.foldl_cons, ih, event_insert]
      simp [eventMass, Rat.add_assoc, Rat.add_left_comm]

/-- Ascending finite map readback preserves the probability of every output event. -/
theorem event_aggregate [DecidableEq Value] [Ord Value] (event : Value → Bool)
    (outcomes : Distribution Value) : eventMass event (aggregate outcomes) = eventMass event outcomes := by
  unfold aggregate
  rw [eventMass_perm event (List.mergeSort_perm _ _)]
  simpa [fromList, eventMass, Rat.zero_add] using event_fold event outcomes []

/-- The certain event has exactly the total mass. -/
theorem event_true (outcomes : Distribution Value) : eventMass (fun _ => true) outcomes = total outcomes := by
  induction outcomes with
  | nil => rfl
  | cons entry rest ih => cases entry; simp [eventMass, total, ih]

/-- Combining duplicate output values changes neither total mass nor normalization. -/
theorem total_aggregate [DecidableEq Value] [Ord Value] (outcomes : Distribution Value) :
    total (aggregate outcomes) = total outcomes := by
  rw [← event_true, event_aggregate, event_true]

/-- Insertion adds one output key without removing any existing key. -/
theorem insert_keys [DecidableEq Value] (mass : Rat) (value key : Value) (table : Distribution Value) :
    key ∈ (insert mass value table).map Prod.snd ↔ key = value ∨ key ∈ table.map Prod.snd := by
  induction table with
  | nil => simp [insert]
  | cons entry rest ih =>
      obtain ⟨old, present⟩ := entry
      by_cases same : value = present
      · subst present
        simp [insert]
      · simp only [insert, ite_eq_right same, List.map_cons, List.mem_cons, ih, or_left_comm]

/-- A finite map insertion retains unique output keys. -/
theorem insert_unique [DecidableEq Value] (mass : Rat) (value : Value) (table : Distribution Value)
    (unique : (table.map Prod.snd).Nodup) : ((insert mass value table).map Prod.snd).Nodup := by
  induction table with
  | nil => simp [insert]
  | cons entry rest ih =>
      obtain ⟨old, key⟩ := entry
      obtain ⟨absent, later⟩ := List.nodup_cons.mp unique
      by_cases same : value = key
      · simp [insert, same, absent, later]
      · simp only [insert, ite_eq_right same, List.map_cons, List.nodup_cons]
        exact ⟨fun present => (insert_keys mass value key rest).mp present |>.elim
          (fun equal => same equal.symm) absent, ih later⟩

/-- The source left fold constructs a unique-key finite map. -/
theorem fold_unique [DecidableEq Value] (outcomes table : Distribution Value)
    (unique : (table.map Prod.snd).Nodup) :
    ((outcomes.foldl (fun table entry => insert entry.1 entry.2 table) table).map Prod.snd).Nodup := by
  induction outcomes generalizing table with
  | nil => exact unique
  | cons entry rest ih => exact ih _ (insert_unique entry.1 entry.2 table unique)

/-- Every reported output value occurs in exactly one PMF row. -/
theorem aggregate_unique [DecidableEq Value] [Ord Value] (outcomes : Distribution Value) :
    ((aggregate outcomes).map Prod.snd).Nodup :=
  ((List.mergeSort_perm _ _).map Prod.snd).nodup_iff.mpr (fold_unique outcomes [] (by simp))

/-- Inserting nonnegative mass into a nonnegative map preserves nonnegativity. -/
theorem insert_nonnegative [DecidableEq Value] (mass : Rat) (value : Value) (table : Distribution Value)
    (positive : 0 ≤ mass) (valid : Nonnegative table) : Nonnegative (insert mass value table) := by
  induction table with
  | nil => simpa [insert, Nonnegative] using positive
  | cons entry rest ih =>
      obtain ⟨old, key⟩ := entry
      have oldPositive := valid (old, key) (by simp)
      have tailPositive : Nonnegative rest := fun entry member => valid entry (by simp [member])
      by_cases same : value = key
      · simp only [insert, ite_eq_left same]
        intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact Rat.add_nonneg positive oldPositive
        · exact tailPositive entry member
      · simp only [insert, ite_eq_right same]
        intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact oldPositive
        · exact ih tailPositive entry member

/-- The source aggregation fold preserves nonnegative masses. -/
theorem fold_nonnegative [DecidableEq Value] (outcomes table : Distribution Value)
    (positive : Nonnegative outcomes) (valid : Nonnegative table) :
    Nonnegative (outcomes.foldl (fun table entry => insert entry.1 entry.2 table) table) := by
  induction outcomes generalizing table with
  | nil => exact valid
  | cons entry rest ih =>
      exact ih _ (fun other member => positive other (by simp [member]))
        (insert_nonnegative entry.1 entry.2 table (positive entry (by simp)) valid)

/-- Aggregated output probabilities are nonnegative whenever source occurrence masses are. -/
theorem aggregate_nonnegative [DecidableEq Value] [Ord Value] (outcomes : Distribution Value)
    (valid : Nonnegative outcomes) : Nonnegative (aggregate outcomes) := by
  intro entry member
  exact fold_nonnegative outcomes [] valid (by simp [Nonnegative]) entry
    ((List.mergeSort_perm _ _).mem_iff.mp member)

/-- Source PMF aggregation maps a probability law on occurrences to a probability law on values. -/
theorem aggregate_probability [DecidableEq Value] [Ord Value] (outcomes : Distribution Value)
    (valid : IsProbability outcomes) : IsProbability (aggregate outcomes) :=
  ⟨aggregate_nonnegative outcomes valid.1, (total_aggregate outcomes).trans valid.2⟩

/-- The map fold retains exactly the output keys of its initial map and input occurrences. -/
theorem fold_keys [DecidableEq Value] (outcomes table : Distribution Value) (value : Value) :
    value ∈ (outcomes.foldl (fun table entry => insert entry.1 entry.2 table) table).map Prod.snd ↔
      value ∈ table.map Prod.snd ∨ value ∈ outcomes.map Prod.snd := by
  induction outcomes generalizing table with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons, ih, insert_keys, List.map_cons, List.mem_cons]
      simp only [or_assoc, or_left_comm]

/-- PMF readback contains an output key exactly when the source occurrence stream contains it. -/
theorem aggregate_keys [DecidableEq Value] [Ord Value] (outcomes : Distribution Value) (value : Value) :
    value ∈ (aggregate outcomes).map Prod.snd ↔ value ∈ outcomes.map Prod.snd := by
  unfold aggregate
  rw [((List.mergeSort_perm _ _).map Prod.snd).mem_iff]
  simpa [fromList] using fold_keys outcomes [] value

/-- Public readback is ordered by the same output comparison as Map.toAscList. -/
theorem aggregate_ordered [DecidableEq Value] [Ord Value] [Std.TransOrd Value]
    (outcomes : Distribution Value) :
    (aggregate outcomes).Pairwise (fun first second => (compare first.2 second.2).isLE = true) := by
  apply List.pairwise_mergeSort
  · intro first second third a b
    exact Std.TransOrd.isLE_trans a b
  · intro first second
    have swap := Std.OrientedOrd.eq_swap (a := first.2) (b := second.2)
    cases one : compare first.2 second.2 <;> cases two : compare second.2 first.2 <;> simp_all

/-- Read one stored map mass, with zero for an absent value. -/
def lookup [DecidableEq Value] (value : Value) : Distribution Value → Rat
  | [] => 0
  | (mass, key) :: rest => if key = value then mass else lookup value rest

/-- An absent output value has no occurrence mass. -/
theorem absent_mass [DecidableEq Value] (value : Value) (outcomes : Distribution Value)
    (absent : value ∉ outcomes.map Prod.snd) :
    eventMass (fun key => decide (key = value)) outcomes = 0 := by
  induction outcomes with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨mass, key⟩ := entry
      have different : key ≠ value := by intro same; exact absent (by simp [same])
      have tailAbsent : value ∉ rest.map Prod.snd := fun member => absent (by simp [member])
      simp [eventMass, different, ih tailAbsent, Rat.zero_add]

/-- A unique-key finite map lookup is its complete mass for the requested output. -/
theorem lookup_mass [DecidableEq Value] (value : Value) (table : Distribution Value)
    (unique : (table.map Prod.snd).Nodup) :
    lookup value table = eventMass (fun key => decide (key = value)) table := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨mass, key⟩ := entry
      obtain ⟨absent, later⟩ := List.nodup_cons.mp unique
      by_cases same : key = value
      · subst key
        simp [lookup, eventMass, absent_mass value rest absent, Rat.add_zero]
      · simp [lookup, eventMass, same, ih later, Rat.zero_add]

/-- Each Map.fromListWith result is the sum of every occurrence of that output value. -/
theorem lookup_aggregate [DecidableEq Value] [Ord Value] (outcomes : Distribution Value) (value : Value) :
    lookup value (aggregate outcomes) = eventMass (fun key => decide (key = value)) outcomes := by
  rw [lookup_mass value _ (aggregate_unique outcomes), event_aggregate]

/-- Four equiprobable replay members can give only two outputs with unequal PMF masses. -/
theorem duplicate_output_example :
    pmf ([(1 / 4, 0), (1 / 4, 0), (1 / 4, 1), (1 / 4, 0)] : Distribution Nat) =
      [(0, 3 / 4), (1, 1 / 4)] := by
  cbv

end MicroCFTA.SourcePmfAggregation
