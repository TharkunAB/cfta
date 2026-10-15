import Std

/-!
# Finite signed child maps for the required-path trie

The source stores `Needed` children in an `IntMap`. This model uses its
ascending entries. It retains signed keys and the exact alter operation.
It does not model the native Patricia tree or machine integer arithmetic.
-/
namespace MicroCFTA.SourceEqualityNeededMap

/-- Read a child from the finite entry list. -/
def lookup (key : Int) : List (Int × α) → Option α
  | [] => none
  | (index, value) :: rest => if key = index then some value else lookup key rest

/-- Apply the source `IntMap.alter` operation that always retains its key. -/
def alter (key : Int) (change : Option α → α) : List (Int × α) → List (Int × α)
  | [] => [(key, change none)]
  | (index, value) :: rest =>
      if key < index then (key, change none) :: (index, value) :: rest
      else if key = index then (index, change (some value)) :: rest
      else (index, value) :: alter key change rest

/-- Ascending entries have one value for each key. -/
def Ascending (entries : List (Int × α)) : Prop :=
  entries.Pairwise (fun left right => left.1 < right.1)

/-- A key absent from the entries has no lookup value. -/
theorem lookup_none (key : Int) (entries : List (Int × α))
    (absent : ∀ index value, (index, value) ∈ entries → key ≠ index) : lookup key entries = none := by
  induction entries with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨index, value⟩ := pair
      rw [lookup, ite_eq_right (absent index value (by simp))]
      exact ih (fun index value member => absent index value (by simp [member]))

/-- Alter changes exactly the selected child value. -/
theorem lookup_alter (key query : Int) (change : Option α → α) (entries : List (Int × α))
    (ordered : Ascending entries) :
    lookup query (alter key change entries) =
      if query = key then some (change (lookup key entries)) else lookup query entries := by
  induction entries with
  | nil => simp [alter, lookup]
  | cons pair rest ih =>
      obtain ⟨index, value⟩ := pair
      have order := List.pairwise_cons.mp ordered
      by_cases earlier : key < index
      · have missing : lookup key ((index, value) :: rest) = none := by
          apply lookup_none
          intro next child member
          rcases List.mem_cons.mp member with same | member
          · cases same; omega
          · have later := order.1 (next, child) member
            dsimp at later
            omega
        rw [alter, ite_eq_left earlier, lookup]
        by_cases same : query = key
        · subst query
          rw [ite_eq_left rfl, ite_eq_left rfl, missing]
        · rw [ite_eq_right same, ite_eq_right same]
      · by_cases same : key = index
        · subst index
          by_cases atHead : query = key
          · subst query; simp [alter, lookup]
          · simp [alter, lookup, atHead]
        · simp only [alter, ite_eq_right earlier, ite_eq_right same, lookup]
          by_cases atHead : query = index
          · subst query
            simp [Ne.symm same]
          · simp only [ite_eq_right atHead]
            rw [ih order.2]

/-- An altered entry either has the selected key or is an unchanged entry. -/
theorem alter_origin (key : Int) (change : Option α → α) (entries : List (Int × α))
    (entry : Int × α) (member : entry ∈ alter key change entries) :
    entry.1 = key ∨ entry ∈ entries := by
  induction entries with
  | nil => simp [alter] at member; subst entry; exact Or.inl rfl
  | cons pair rest ih =>
      obtain ⟨index, value⟩ := pair
      simp only [alter] at member
      split at member
      · rcases List.mem_cons.mp member with rfl | member
        · exact Or.inl rfl
        · exact Or.inr member
      · split at member
        · rcases List.mem_cons.mp member with rfl | member
          · rename_i same; exact Or.inl same.symm
          · exact Or.inr (List.mem_cons_of_mem _ member)
        · rcases List.mem_cons.mp member with rfl | member
          · exact Or.inr (by simp)
          · rcases ih member with same | original
            · exact Or.inl same
            · exact Or.inr (List.mem_cons_of_mem _ original)

/-- Alter retains ascending order, including insertion before the first larger key. -/
theorem alter_ascending (key : Int) (change : Option α → α) (entries : List (Int × α))
    (ordered : Ascending entries) : Ascending (alter key change entries) := by
  induction entries with
  | nil => simp [alter, Ascending]
  | cons pair rest ih =>
      obtain ⟨index, value⟩ := pair
      have order := List.pairwise_cons.mp ordered
      by_cases earlier : key < index
      · rw [alter, ite_eq_left earlier]
        apply List.pairwise_cons.mpr
        refine ⟨?_, ordered⟩
        intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact earlier
        · have later := order.1 entry member
          dsimp at later ⊢
          omega
      · by_cases same : key = index
        · subst index
          simpa [alter, earlier, Ascending, List.pairwise_cons] using order
        · rw [alter, ite_eq_right earlier, ite_eq_right same]
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih order.2⟩
          intro entry member
          rcases alter_origin key change rest entry member with selected | original
          · dsimp
            rw [selected]
            omega
          · exact order.1 entry original

/-- A successful lookup returns an actual entry. -/
theorem lookup_mem (key : Int) (entries : List (Int × α)) (value : α)
    (found : lookup key entries = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => simp [lookup] at found
  | cons pair rest ih =>
      obtain ⟨index, child⟩ := pair
      simp only [lookup] at found
      split at found
      · cases found; simp_all
      · exact List.mem_cons_of_mem _ (ih found)

/-- Ascending keys make lookup complete for every entry. -/
theorem lookup_of_mem (key : Int) (entries : List (Int × α)) (value : α)
    (ordered : Ascending entries) (member : (key, value) ∈ entries) :
    lookup key entries = some value := by
  induction entries with
  | nil => simp at member
  | cons pair rest ih =>
      obtain ⟨index, child⟩ := pair
      rcases List.mem_cons.mp member with same | member
      · cases same; simp [lookup]
      · have order := List.pairwise_cons.mp ordered
        have bound := order.1 (key, value) member
        dsimp at bound
        rw [lookup, ite_eq_right (by omega)]
        exact ih order.2 member

/-- Alter preserves a property of every child when its replacement has that property. -/
theorem alter_all (key : Int) (change : Option α → α) (entries : List (Int × α))
    (property : α → Prop) (before : ∀ index value, (index, value) ∈ entries → property value)
    (after : property (change (lookup key entries))) (ordered : Ascending entries) :
    ∀ index value, (index, value) ∈ alter key change entries → property value := by
  intro index value member
  have ordered' := alter_ascending key change entries ordered
  have found := lookup_of_mem index (alter key change entries) value ordered' member
  rw [lookup_alter key index change entries ordered] at found
  split at found
  · cases found; exact after
  · exact before index value (lookup_mem index entries value found)

end MicroCFTA.SourceEqualityNeededMap
