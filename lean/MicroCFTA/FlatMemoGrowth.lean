import MicroCFTA.FlatMemoTable

/-!
# Flat-table rebuild preserves memo winners

Physical insertion adds at most one occupied slot. Copying a finite source
inventory into a sufficiently large empty array completes and represents
the same abstract table. The raw array allocation and publication remain
implementation correspondence boundaries.
-/
namespace MicroCFTA.FlatMemoGrowth
open FlatMemoProbe FlatMemoTable

/-- Filling one empty index in a distinct finite inventory adds exactly one occupied slot. -/
theorem filter_write [DecidableEq Slot] (slots : Slot → Option Entry) (index : Slot) (entry : Entry)
    (indices : List Slot) (distinct : indices.Nodup) (member : index ∈ indices) (empty : slots index = none) :
    (indices.filter fun position => (Cache.put slots index entry position).isSome).length =
      (indices.filter fun position => (slots position).isSome).length + 1 := by
  induction indices with
  | nil => cases member
  | cons first rest ih =>
      have distinct := List.nodup_cons.mp distinct
      by_cases same : first = index
      · subst first
        have tail : (rest.filter fun position => (Cache.put slots index entry position).isSome) =
            rest.filter fun position => (slots position).isSome := by
          apply List.filter_congr
          intro position member
          have different : position ≠ index := by intro same; subst position; exact distinct.1 member
          simp [Cache.put, different]
        simp [Cache.put, empty, ← tail]
      · have included : index ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        have tail := ih distinct.2 included
        have current : Cache.put slots index entry first = slots first := by simp [Cache.put, same]
        simp only [List.filter_cons, current]
        split <;> simp_all <;> omega

/-- A physical write to an empty slot increases published occupancy by one. -/
theorem occupied_write (slots : Slots capacity Key Value) (index : Fin capacity) (key : Key) (value : Value)
    (empty : slots index = none) : occupied (Cache.put slots index (key, value)) = occupied slots + 1 :=
  filter_write slots index (key, value) (List.finRange capacity) (List.nodup_finRange _) (List.mem_finRange _) empty

/-- Every completed physical insertion adds at most one occupied slot. -/
theorem insert_count [DecidableEq Key] (hash : Key → Fin capacity) (slots : Slots capacity Key Value)
    (key : Key) (candidate result : Value) (after : Slots capacity Key Value)
    (done : insert hash slots key candidate = some (result, after)) : occupied after ≤ occupied slots + 1 := by
  cases found : search slots key (order (hash key)) with
  | exhausted => simp [FlatMemoTable.insert, found] at done
  | present index value =>
      have equal : value = result ∧ slots = after := by simpa [FlatMemoTable.insert, found] using done
      rw [← equal.2]
      omega
  | empty index =>
      have equal : candidate = result ∧ Cache.put slots index (key, candidate) = after := by simpa [FlatMemoTable.insert, found] using done
      rw [← equal.2, occupied_write slots index key candidate (search_empty slots key _ index found).1]
      exact Nat.le_refl _

/-- Any vacant physical table completes one insertion, independent of its current load threshold. -/
theorem insert_with_room [DecidableEq Key] (hash : Key → Fin capacity) (slots : Slots capacity Key Value)
    (key : Key) (candidate : Value) (room : occupied slots < capacity) :
    ∃ result after, insert hash slots key candidate = some (result, after) := by
  obtain ⟨index, empty⟩ := vacancy slots room
  have complete := search_complete slots key (order (hash key)) ⟨index, order_contains _ _, empty⟩
  cases found : search slots key (order (hash key)) with
  | exhausted => exact False.elim (complete found)
  | present index value => exact ⟨value, slots, by simp [FlatMemoTable.insert, found]⟩
  | empty index => exact ⟨candidate, Cache.put slots index (key, candidate), by simp [FlatMemoTable.insert, found]⟩

/-- Copy source records in inventory order through actual linear-probe insertion. -/
def copy [DecidableEq Key] (hash : Key → Fin capacity) :
    List (Key × Value) → Slots capacity Key Value → Option (Slots capacity Key Value)
  | [], slots => some slots
  | (key, value) :: rest, slots =>
      (insert hash slots key value).bind fun result => copy hash rest result.2

/-- Enough initial space completes every copy and bounds final occupancy by the source inventory length. -/
theorem copy_complete [DecidableEq Key] (hash : Key → Fin capacity) (entries : List (Key × Value))
    (slots : Slots capacity Key Value) (room : occupied slots + entries.length ≤ capacity) :
    ∃ after, copy hash entries slots = some after ∧ occupied after ≤ occupied slots + entries.length := by
  induction entries generalizing slots with
  | nil => exact ⟨slots, rfl, by simp⟩
  | cons entry rest ih =>
      obtain ⟨key, value⟩ := entry
      obtain ⟨result, middle, done⟩ := insert_with_room hash slots key value (by simp only [List.length_cons] at room; omega)
      have count := insert_count hash slots key value result middle done
      obtain ⟨after, tail, afterCount⟩ := ih middle (by simp only [List.length_cons] at room; omega)
      exact ⟨after, by simp only [copy, done, Option.bind_some, tail], by simp only [List.length_cons]; omega⟩

/-- Completed physical copying refines the existing abstract first-writer update sequence. -/
theorem copy_represents [DecidableEq Key] (hash : Key → Fin capacity) (entries : List (Key × Value))
    (slots after : Slots capacity Key Value) (table : Cache.Table Key Value) (valid : Represents hash slots table)
    (done : copy hash entries slots = some after) : Represents hash after (Cache.updates table entries) := by
  induction entries generalizing slots table with
  | nil => cases done; exact valid
  | cons entry rest ih =>
      obtain ⟨key, value⟩ := entry
      cases first : insert hash slots key value with
      | none => simp [copy, first] at done
      | some result =>
          obtain ⟨output, middle⟩ := result
          exact ih middle (Cache.keepFirst table key value)
            (insert_correct hash slots table valid key value output middle first).1
            (by simpa only [copy, first, Option.bind_some] using done)

/-- Abstract copying stores no value absent from the original memo table. -/
theorem updates_sound [DecidableEq Key] (original current : Cache.Table Key Value)
    (entries : List (Key × Value))
    (before : ∀ key value, current key = some value → original key = some value)
    (source : ∀ entry ∈ entries, original entry.1 = some entry.2) :
    ∀ key value, Cache.updates current entries key = some value → original key = some value := by
  induction entries generalizing current with
  | nil => exact before
  | cons entry rest ih =>
      apply ih (Cache.keepFirst current entry.1 entry.2) ?_ (fun entry member => source entry (List.mem_cons_of_mem _ member))
      intro key value present
      cases existing : current entry.1 with
      | some prior => exact before key value (by simpa [Cache.keepFirst, existing] using present)
      | none =>
          by_cases same : key = entry.1
          · subst key
            have equal : entry.2 = value := by simpa [Cache.keepFirst, existing, Cache.put] using present
            exact equal ▸ source entry List.mem_cons_self
          · exact before key value (by simpa [Cache.keepFirst, existing, Cache.put, same] using present)

/-- Every copied key becomes present, whether it wins the first insertion or finds an earlier winner. -/
theorem updates_present [DecidableEq Key] (current : Cache.Table Key Value) (entries : List (Key × Value))
    (key : Key) (value : Value) (member : (key, value) ∈ entries) : ∃ output, Cache.updates current entries key = some output := by
  induction entries generalizing current with
  | nil => cases member
  | cons entry rest ih =>
      rcases List.mem_cons.mp member with equal | member
      · subst entry
        obtain ⟨output, present⟩ := Cache.keepFirst_present current key value
        exact ⟨output, Cache.updates_extend _ rest key output present⟩
      · exact ih (Cache.keepFirst current entry.1 entry.2) member

/-- Copying precisely the source memo inventory into an empty abstract table preserves every winner. -/
theorem updates_exact [DecidableEq Key] (original : Cache.Table Key Value) (entries : List (Key × Value))
    (source : ∀ entry ∈ entries, original entry.1 = some entry.2)
    (covered : ∀ key value, original key = some value → (key, value) ∈ entries) :
    Cache.updates (fun _ => none) entries = original := by
  funext key
  have sound := updates_sound original (fun _ => none) entries (by intros; contradiction) source
  cases old : original key with
  | none =>
      cases found : Cache.updates (fun _ => none) entries key with
      | none => rfl
      | some value => have impossible := (sound key value found).symm.trans old; cases impossible
  | some value =>
      obtain ⟨output, present⟩ := updates_present (fun _ => none) entries key value (covered key value old)
      have equal := Option.some.inj ((sound key output present).symm.trans old)
      simpa only [equal] using present

/-- A successful rebuild of all source slots preserves the complete abstract memo table. -/
theorem rebuild_exact [DecidableEq Key] (oldHash : Key → Fin oldCapacity) (slots : Slots oldCapacity Key Value)
    (table : Cache.Table Key Value) (valid : Represents oldHash slots table)
    (newHash : Key → Fin newCapacity) (after : Slots newCapacity Key Value)
    (done : copy newHash ((List.finRange oldCapacity).filterMap slots) (fun _ => none) = some after) :
    Represents newHash after table := by
  have copied := copy_represents newHash ((List.finRange oldCapacity).filterMap slots) (fun _ => none) after
    (fun _ => none) (empty_represents newHash) done
  have exactTable := updates_exact table ((List.finRange oldCapacity).filterMap slots)
    (by intro entry member; obtain ⟨index, _, stored⟩ := List.mem_filterMap.mp member; exact valid.sound index entry.1 entry.2 stored)
    (by intro key value present; obtain ⟨index, stored⟩ := valid.complete key value present; exact List.mem_filterMap.mpr ⟨index, List.mem_finRange _, stored⟩)
  simpa only [exactTable] using copied

/-- Doubling a half-full table completes the exact source-slot copy and retains every memo winner. -/
theorem grow_complete [DecidableEq Key] (oldHash : Key → Fin capacity) (slots : Slots capacity Key Value)
    (table : Cache.Table Key Value) (valid : Represents oldHash slots table)
    (half : 2 * occupied slots ≤ capacity) (newHash : Key → Fin (2 * capacity)) :
    ∃ after, copy newHash ((List.finRange capacity).filterMap slots) (fun _ => none) = some after ∧
      Represents newHash after table ∧ occupied after ≤ occupied slots := by
  have count : ((List.finRange capacity).filterMap slots).length = occupied slots := by
    simp only [List.length_filterMap_eq_countP, occupied, List.countP_eq_length_filter]
  have initial : occupied (fun _ : Fin (2 * capacity) => (none : Option (Key × Value))) = 0 := by
    simp [occupied]
  obtain ⟨after, done, bound⟩ := copy_complete newHash ((List.finRange capacity).filterMap slots) (fun _ => none)
    (by rw [initial, count]; omega)
  exact ⟨after, done, rebuild_exact oldHash slots table valid newHash after done, by simpa only [initial, count, Nat.zero_add] using bound⟩

/-- The growing insertion branch preserves the half-full invariant and exact first-writer result. -/
theorem grow_insert_complete [DecidableEq Key] (oldHash : Key → Fin capacity) (slots : Slots capacity Key Value)
    (table : Cache.Table Key Value) (valid : Represents oldHash slots table)
    (positive : 0 < capacity) (half : 2 * occupied slots ≤ capacity) (newHash : Key → Fin (2 * capacity))
    (key : Key) (candidate : Value) :
    ∃ grown result after,
      copy newHash ((List.finRange capacity).filterMap slots) (fun _ => none) = some grown ∧
      insert newHash grown key candidate = some (result, after) ∧
      Represents newHash after (Cache.keepFirst table key candidate) ∧
      Cache.keepFirst table key candidate key = some result ∧ 2 * occupied after ≤ 2 * capacity := by
  obtain ⟨grown, copied, represented, count⟩ := grow_complete oldHash slots table valid half newHash
  obtain ⟨result, after, inserted⟩ := insert_with_room newHash grown key candidate (by omega)
  have checked := insert_correct newHash grown table represented key candidate result after inserted
  have afterCount := insert_count newHash grown key candidate result after inserted
  exact ⟨grown, result, after, copied, inserted, checked.1, checked.2, by omega⟩

/-- The nongrowing insertion branch preserves the half-full invariant under the source load test. -/
theorem insert_half_full [DecidableEq Key] (hash : Key → Fin capacity) (slots : Slots capacity Key Value)
    (key : Key) (candidate result : Value) (after : Slots capacity Key Value)
    (room : 2 * (occupied slots + 1) ≤ capacity)
    (done : insert hash slots key candidate = some (result, after)) : 2 * occupied after ≤ capacity := by
  have count := insert_count hash slots key candidate result after done
  omega

end MicroCFTA.FlatMemoGrowth
