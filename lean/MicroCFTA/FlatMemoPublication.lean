import MicroCFTA.FlatMemoGrowth

/-!
# Publication phases and stale-reader rechecks

The logical publication step exposes a complete slot record at once.
The native implementation must justify this step with its value/key writes
and atomic first-key release/acquire operations. These theorems do not
verify raw GHC array primitives, memory barriers, or thunk scheduling.
-/
namespace MicroCFTA.FlatMemoPublication
open FlatMemoProbe FlatMemoTable

/-- Source integer triples keep their sentinel-sensitive first component explicit. -/
structure Key where
  first : Int
  second : Int
  third : Int
deriving DecidableEq

/-- Source callers supply a nonnegative first key. -/
def ValidKey (key : Key) : Prop := 0 ≤ key.first

/-- The documented first-key precondition excludes the empty-slot sentinel. -/
theorem valid_not_sentinel (key : Key) (valid : ValidKey key) : key.first ≠ -1 := by
  unfold ValidKey at valid
  omega

/-- The publication protocol has an empty marker, staged payload, and visible complete record. -/
inductive Phase (Value : Type) where
  | empty
  | prepared (key : Key) (value : Value)
  | published (key : Key) (value : Value)

/-- A reader ignores the staged payload until the first key publishes it. -/
def observe : Phase Value → Option (Key × Value)
  | .empty | .prepared .. => none
  | .published key value => if key.first = -1 then none else some (key, value)

/-- Writing the first key is the abstract atomic publication of the staged record. -/
def publish : Phase Value → Phase Value
  | .prepared key value => .published key value
  | state => state

/-- A reader before publication cannot observe partial second/third keys or the value. -/
theorem prepared_hidden (key : Key) (value : Value) : observe (.prepared key value) = none := rfl

/-- Under the caller contract, publication reveals the complete requested record. -/
theorem publication_exact (key : Key) (value : Value) (valid : ValidKey key) :
    observe (publish (.prepared key value)) = some (key, value) := by
  simp [publish, observe, valid_not_sentinel key valid]

/-- Publishing the reserved first-key sentinel remains invisible to the source reader. -/
theorem sentinel_invisible (second third : Int) (value : Value) :
    observe (publish (.prepared ⟨-1, second, third⟩ value)) = none := by
  simp [publish, observe]

/-- A lock-free hit returns its snapshot's value; a miss rechecks the locked current arrays. -/
def lookupOrInsert [DecidableEq K] (oldHash : K → Fin oldCapacity) (old : Slots oldCapacity K Value)
    (currentHash : K → Fin currentCapacity) (current : Slots currentCapacity K Value) (key : K) (candidate : Value) :
    Option (Value × Slots currentCapacity K Value) :=
  match search old key (order (oldHash key)) with
  | .present _ value => some (value, current)
  | .empty _ | .exhausted => FlatMemoTable.insert currentHash current key candidate

/-- Stale successful reads and locked miss rechecks both retain the current table's first winner. -/
theorem lookupOrInsert_correct [DecidableEq K]
    (oldHash : K → Fin oldCapacity) (old : Slots oldCapacity K Value) (oldTable : Cache.Table K Value)
    (oldValid : Represents oldHash old oldTable)
    (currentHash : K → Fin currentCapacity) (current : Slots currentCapacity K Value) (table : Cache.Table K Value)
    (currentValid : Represents currentHash current table) (growth : Cache.Extends oldTable table)
    (key : K) (candidate : Value) (half : 2 * occupied current ≤ currentCapacity) :
    ∃ result after, lookupOrInsert oldHash old currentHash current key candidate = some (result, after) ∧
      Represents currentHash after (Cache.keepFirst table key candidate) ∧ Cache.keepFirst table key candidate key = some result := by
  cases found : search old key (order (oldHash key)) with
  | present index value =>
      have original := oldValid.sound index key value (search_present old key _ index value found)
      have retained := growth key value original
      exact ⟨value, current, by simp only [lookupOrInsert, found],
        by simpa only [Cache.keepFirst, retained] using currentValid, Cache.keepFirst_existing retained candidate⟩
  | empty index | exhausted =>
      obtain ⟨result, after, inserted⟩ := insert_complete currentHash current key candidate half
      have checked := insert_correct currentHash current table currentValid key candidate result after inserted
      exact ⟨result, after, by simpa only [lookupOrInsert, found] using inserted, checked⟩

/-- A stale miss cannot replace a value installed before the locked recheck. -/
theorem locked_recheck_winner [DecidableEq K] (hash : K → Fin capacity) (slots : Slots capacity K Value)
    (table : Cache.Table K Value) (valid : Represents hash slots table) (key : K) (winner candidate result : Value)
    (present : table key = some winner) (after : Slots capacity K Value)
    (done : FlatMemoTable.insert hash slots key candidate = some (result, after)) : result = winner := by
  have returned := (insert_correct hash slots table valid key candidate result after done).2
  exact Option.some.inj (returned.symm.trans (Cache.keepFirst_existing present candidate))

/-- Reads from different times still stop when their complete records extend to one half-full retained array. -/
theorem observed_probe_complete [DecidableEq K] (observed final : Slots capacity K Value)
    (retained : Cache.Extends observed final) (start : Fin capacity) (key : K)
    (half : 2 * occupied final ≤ capacity) : search observed key (order start) ≠ .exhausted := by
  obtain ⟨index, empty⟩ := half_full_vacancy final (by have := start.isLt; omega) half
  have notSeen : observed index = none := by
    cases found : observed index with
    | none => rfl
    | some value => have impossible := (retained index value found).symm.trans empty; cases impossible
  exact search_complete observed key (order start) ⟨index, order_contains start index, notSeen⟩

/-- Per-slot reads need only retain complete winners; they need not form one atomic whole-array snapshot. -/
theorem observed_lookupOrInsert_correct [DecidableEq K]
    (oldHash : K → Fin oldCapacity) (observed : Slots oldCapacity K Value)
    (currentHash : K → Fin currentCapacity) (current : Slots currentCapacity K Value) (table : Cache.Table K Value)
    (currentValid : Represents currentHash current table)
    (visible : ∀ index key value, observed index = some (key, value) → table key = some value)
    (key : K) (candidate : Value) (half : 2 * occupied current ≤ currentCapacity) :
    ∃ result after, lookupOrInsert oldHash observed currentHash current key candidate = some (result, after) ∧
      Represents currentHash after (Cache.keepFirst table key candidate) ∧ Cache.keepFirst table key candidate key = some result := by
  cases found : search observed key (order (oldHash key)) with
  | present index value =>
      have retained := visible index key value (search_present observed key _ index value found)
      exact ⟨value, current, by simp only [lookupOrInsert, found],
        by simpa only [Cache.keepFirst, retained] using currentValid, Cache.keepFirst_existing retained candidate⟩
  | empty index | exhausted =>
      obtain ⟨result, after, inserted⟩ := insert_complete currentHash current key candidate half
      have checked := insert_correct currentHash current table currentValid key candidate result after inserted
      exact ⟨result, after, by simpa only [lookupOrInsert, found] using inserted, checked⟩

end MicroCFTA.FlatMemoPublication
