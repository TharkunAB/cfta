import MicroCFTA.FlatMemoProbe

/-!
# Physical flat-table insertion refines first-writer memoization

The placement invariant excludes an empty slot before each resident key on
its probe path. Complete slot records represent the abstract memo table.
Insertion writes only the first empty slot and preserves the old winners.
-/
namespace MicroCFTA.FlatMemoTable
open FlatMemoProbe

/-- Every resident key has an occupied probe prefix, and slots represent exactly the abstract table. -/
structure Represents (hash : Key → Fin capacity) (slots : Slots capacity Key Value) (table : Cache.Table Key Value) : Prop where
  sound : ∀ index key value, slots index = some (key, value) → table key = some value
  complete : ∀ key value, table key = some value → ∃ index, slots index = some (key, value)
  placed : ∀ index key value, slots index = some (key, value) →
    ∃ before after, order (hash key) = before ++ index :: after ∧ ∀ prior ∈ before, slots prior ≠ none

/-- Empty slot arrays represent the empty memo table. -/
theorem empty_represents (hash : Key → Fin capacity) : Represents hash (fun _ => none) (fun _ : Key => (none : Option Value)) := by
  constructor <;> intros <;> contradiction

/-- Occupied probe prefixes reach the requested key, or an earlier slot with the same stored winner. -/
theorem search_existing [DecidableEq Key] (slots : Slot → Option (Key × Value))
    (table : Cache.Table Key Value) (sound : ∀ index key value, slots index = some (key, value) → table key = some value)
    (key : Key) (value : Value) (present : table key = some value)
    (index : Slot) (stored : slots index = some (key, value)) (before after : List Slot)
    (occupied : ∀ prior ∈ before, slots prior ≠ none) :
    ∃ found, search slots key (before ++ index :: after) = .present found value := by
  induction before with
  | nil => exact ⟨index, by simp [search, stored]⟩
  | cons prior rest ih =>
      cases current : slots prior with
      | none => exact False.elim (occupied prior List.mem_cons_self current)
      | some pair =>
          obtain ⟨other, output⟩ := pair
          by_cases same : other = key
          · subst other
            have equal : output = value := Option.some.inj ((sound prior key output current).symm.trans present)
            subst output
            exact ⟨prior, by simp [search, current]⟩
          · obtain ⟨found, tail⟩ := ih (fun prior member => occupied prior (List.mem_cons_of_mem _ member))
            exact ⟨found, by simpa only [List.cons_append, search, current, same, ↓reduceIte] using tail⟩

/-- Every represented memo entry is found with its exact stored value. -/
theorem Represents.lookup [DecidableEq Key] (hash : Key → Fin capacity) (slots : Slots capacity Key Value)
    (table : Cache.Table Key Value) (valid : Represents hash slots table) (key : Key) (value : Value)
    (present : table key = some value) : ∃ index, search slots key (order (hash key)) = .present index value := by
  obtain ⟨index, stored⟩ := valid.complete key value present
  obtain ⟨before, after, path, occupied⟩ := valid.placed index key value stored
  rw [path]
  exact search_existing slots table valid.sound key value present index stored before after occupied

/-- Replacing an empty slot by a complete record never creates an empty probe prefix. -/
theorem put_occupied [DecidableEq Slot] (slots : Slot → Option Entry) (index prior : Slot) (entry : Entry)
    (occupied : slots prior ≠ none) : Cache.put slots index entry prior ≠ none := by
  by_cases same : prior = index
  · simp [Cache.put, same]
  · simpa [Cache.put, same] using occupied

/-- A physical write to the first empty probe slot implements an abstract fresh-key insertion. -/
theorem write_represents [DecidableEq Key] (hash : Key → Fin capacity) (slots : Slots capacity Key Value)
    (table : Cache.Table Key Value) (valid : Represents hash slots table) (key : Key) (value : Value)
    (index : Fin capacity) (empty : slots index = none) (missing : table key = none)
    (before after : List (Fin capacity)) (path : order (hash key) = before ++ index :: after)
    (occupied : ∀ prior ∈ before, slots prior ≠ none) :
    Represents hash (Cache.put slots index (key, value)) (Cache.put table key value) := by
  have growth : Cache.Extends table (Cache.put table key value) := by
    simpa only [Cache.keepFirst, missing] using Cache.keepFirst_extends table key value
  constructor
  · intro position query output stored
    by_cases same : position = index
    · subst position
      have equal : (key, value) = (query, output) := by simpa [Cache.put] using stored
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      simp [Cache.put]
    · exact growth query output (valid.sound position query output (by simpa [Cache.put, same] using stored))
  · intro query output present
    by_cases same : query = key
    · subst query
      have equal : value = output := by simpa [Cache.put] using present
      subst output
      exact ⟨index, by simp [Cache.put]⟩
    · obtain ⟨position, stored⟩ := valid.complete query output (by simpa [Cache.put, same] using present)
      have different : position ≠ index := by intro equal; subst position; simp [empty] at stored
      exact ⟨position, by simpa [Cache.put, different] using stored⟩
  · intro position query output stored
    by_cases same : position = index
    · subst position
      have equal : (key, value) = (query, output) := by simpa [Cache.put] using stored
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact ⟨before, after, path, fun prior member => put_occupied slots index prior (key, value) (occupied prior member)⟩
    · obtain ⟨pref, suffix, path, occupied⟩ := valid.placed position query output (by simpa [Cache.put, same] using stored)
      exact ⟨pref, suffix, path, fun prior member => put_occupied slots index prior (key, value) (occupied prior member)⟩

/-- Under the writer lock, an existing key wins and a missing key fills its first empty slot. -/
def insert [DecidableEq Key] (hash : Key → Fin capacity) (slots : Slots capacity Key Value)
    (key : Key) (candidate : Value) : Option (Value × Slots capacity Key Value) :=
  match search slots key (order (hash key)) with
  | .present _ value => some (value, slots)
  | .empty index => some (candidate, Cache.put slots index (key, candidate))
  | .exhausted => none

/-- A represented physical insertion retains every first writer and returns that exact abstract winner. -/
theorem insert_correct [DecidableEq Key] (hash : Key → Fin capacity) (slots : Slots capacity Key Value)
    (table : Cache.Table Key Value) (valid : Represents hash slots table) (key : Key) (candidate result : Value)
    (after : Slots capacity Key Value) (done : insert hash slots key candidate = some (result, after)) :
    Represents hash after (Cache.keepFirst table key candidate) ∧ Cache.keepFirst table key candidate key = some result := by
  cases found : search slots key (order (hash key)) with
  | exhausted => simp [insert, found] at done
  | present index value =>
      have equal : value = result ∧ slots = after := by simpa [insert, found] using done
      rcases equal with ⟨rfl, rfl⟩
      have present := valid.sound index key value (search_present slots key _ index value found)
      exact ⟨by simpa only [Cache.keepFirst, present] using valid, Cache.keepFirst_existing present candidate⟩
  | empty index =>
      have equal : candidate = result ∧ Cache.put slots index (key, candidate) = after := by simpa [insert, found] using done
      rcases equal with ⟨rfl, rfl⟩
      have missing : table key = none := by
        cases present : table key with
        | none => rfl
        | some value =>
            obtain ⟨other, there⟩ := valid.lookup hash slots table key value present
            rw [found] at there
            cases there
      obtain ⟨empty, before, rest, path, occupied⟩ := search_empty slots key _ index found
      exact ⟨by simpa only [Cache.keepFirst, missing] using write_represents hash slots table valid key candidate index empty missing before rest path occupied,
        by simp [Cache.keepFirst, missing, Cache.put]⟩

/-- A positive half-full table always completes physical insertion. -/
theorem insert_complete [DecidableEq Key] (hash : Key → Fin capacity) (slots : Slots capacity Key Value)
    (key : Key) (candidate : Value) (half : 2 * occupied slots ≤ capacity) :
    ∃ result after, insert hash slots key candidate = some (result, after) := by
  have complete := (half_full_probe slots (hash key) key half).1
  cases found : search slots key (order (hash key)) with
  | exhausted => exact False.elim (complete found)
  | present index value => exact ⟨value, slots, by simp [insert, found]⟩
  | empty index => exact ⟨candidate, Cache.put slots index (key, candidate), by simp [insert, found]⟩

end MicroCFTA.FlatMemoTable
