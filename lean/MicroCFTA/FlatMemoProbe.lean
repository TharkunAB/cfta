import MicroCFTA.Cache

/-!
# Bounded linear probing for the flat memo table

Slots contain complete published key/value records or are empty. Probing
visits the suffix from the hash slot and then the prefix. Atomic publication,
machine arithmetic, and raw array reads remain implementation boundaries.
-/
namespace MicroCFTA.FlatMemoProbe

/-- A fixed-capacity published slot array with three-part keys abstracted by `Key`. -/
abbrev Slots (capacity : Nat) (Key Value : Type) := Fin capacity → Option (Key × Value)

/-- Visit each slot once, starting at the key's hash slot and wrapping at capacity. -/
def order (start : Fin capacity) : List (Fin capacity) :=
  (List.finRange capacity).drop start.val ++ (List.finRange capacity).take start.val

/-- One complete wrap contains exactly the physical capacity's number of slots. -/
theorem order_length (start : Fin capacity) : (order start).length = capacity := by
  simp only [order, List.length_append, List.length_drop, List.length_take, List.length_finRange]
  omega

/-- Every physical slot occurs in one complete linear-probe wrap. -/
theorem order_contains (start index : Fin capacity) : index ∈ order start := by
  have original : index ∈ (List.finRange capacity).take start.val ++ (List.finRange capacity).drop start.val := by
    simpa only [List.take_append_drop] using List.mem_finRange index
  exact List.mem_append.mpr (List.mem_append.mp original).symm

/-- A probe either finds an exact key, finds an empty insertion slot, or exhausts its bounded traversal. -/
inductive Found (Slot Value : Type) where
  | present (slot : Slot) (value : Value)
  | empty (slot : Slot)
  | exhausted

/-- Read complete published slots in order, stopping at the first key or empty slot. -/
def search [DecidableEq Key] (slots : Slot → Option (Key × Value)) (key : Key) : List Slot → Found Slot Value
  | [] => .exhausted
  | index :: rest => match slots index with
    | none => .empty index
    | some (stored, value) => if stored = key then .present index value else search slots key rest

/-- Count the slot reads performed by the same bounded search. -/
def reads [DecidableEq Key] (slots : Slot → Option (Key × Value)) (key : Key) : List Slot → Nat
  | [] => 0
  | index :: rest => match slots index with
    | none => 1
    | some (stored, _) => if stored = key then 1 else 1 + reads slots key rest

/-- Every bounded search reads at most the number of supplied slots. -/
theorem reads_le [DecidableEq Key] (slots : Slot → Option (Key × Value)) (key : Key) (pending : List Slot) :
    reads slots key pending ≤ pending.length := by
  induction pending with
  | nil => exact Nat.le_refl _
  | cons index rest ih =>
      cases current : slots index with
      | none => simp [reads, current]
      | some pair =>
          obtain ⟨stored, value⟩ := pair
          simp only [reads, current, List.length_cons]
          split <;> omega

/-- A search can exhaust only when every inspected slot is occupied. -/
theorem exhausted_occupied [DecidableEq Key] (slots : Slot → Option (Key × Value)) (key : Key)
    (pending : List Slot) (exhausted : search slots key pending = .exhausted) :
    ∀ index ∈ pending, slots index ≠ none := by
  induction pending with
  | nil => simp
  | cons index rest ih =>
      cases current : slots index with
      | none => simp [search, current] at exhausted
      | some pair =>
          by_cases same : pair.1 = key
          · simp [search, current, same] at exhausted
          · have tail : search slots key rest = .exhausted := by simpa only [search, current, same, ↓reduceIte] using exhausted
            intro found member
            rcases List.mem_cons.mp member with rfl | member
            · simp [current]
            · exact ih tail found member

/-- An empty slot in the supplied traversal prevents exhaustion. -/
theorem search_complete [DecidableEq Key] (slots : Slot → Option (Key × Value)) (key : Key)
    (pending : List Slot) (vacant : ∃ index ∈ pending, slots index = none) : search slots key pending ≠ .exhausted := by
  intro exhausted
  obtain ⟨index, member, empty⟩ := vacant
  exact exhausted_occupied slots key pending exhausted index member empty

/-- Count occupied published slots in the fixed-capacity array. -/
def occupied (slots : Slots capacity Key Value) : Nat :=
  ((List.finRange capacity).filter fun index => (slots index).isSome).length

/-- Any occupancy below capacity supplies a physical empty slot. -/
theorem vacancy (slots : Slots capacity Key Value) (room : occupied slots < capacity) : ∃ index, slots index = none := by
  have shorter : ((List.finRange capacity).filter fun index => (slots index).isSome).length < (List.finRange capacity).length := by
    simpa only [occupied, List.length_finRange] using room
  obtain ⟨index, _, empty⟩ := List.length_filter_lt_length_iff_exists.mp shorter
  exact ⟨index, by simpa using empty⟩

/-- A positive half-full table always has an empty slot. -/
theorem half_full_vacancy (slots : Slots capacity Key Value) (positive : 0 < capacity)
    (half : 2 * occupied slots ≤ capacity) : ∃ index, slots index = none :=
  vacancy slots (by omega)

/-- Half-full published arrays complete every probe within one capacity-sized wrap. -/
theorem half_full_probe [DecidableEq Key] (slots : Slots capacity Key Value) (start : Fin capacity) (key : Key)
    (half : 2 * occupied slots ≤ capacity) :
    search slots key (order start) ≠ .exhausted ∧ reads slots key (order start) ≤ capacity := by
  obtain ⟨index, empty⟩ := half_full_vacancy slots (by have := start.isLt; omega) half
  exact ⟨search_complete slots key (order start) ⟨index, order_contains start index, empty⟩,
    by simpa only [order_length] using reads_le slots key (order start)⟩

/-- A found key reads the value from that exact published slot. -/
theorem search_present [DecidableEq Key] (slots : Slot → Option (Key × Value)) (key : Key)
    (pending : List Slot) (index : Slot) (value : Value) (found : search slots key pending = .present index value) :
    slots index = some (key, value) := by
  induction pending with
  | nil => cases found
  | cons current rest ih =>
      cases currentSlot : slots current with
      | none => simp [search, currentSlot] at found
      | some pair =>
          by_cases same : pair.1 = key
          · have equal : current = index ∧ pair.2 = value := by simpa [search, currentSlot, same, Found.present.injEq] using found
            rcases equal with ⟨rfl, rfl⟩
            have pairEq : pair = (key, pair.2) := Prod.ext same rfl
            exact currentSlot.trans (congrArg some pairEq)
          · exact ih (by simpa only [search, currentSlot, same, ↓reduceIte] using found)

/-- The first empty result splits the traversal after an occupied prefix. -/
theorem search_empty [DecidableEq Key] (slots : Slot → Option (Key × Value)) (key : Key)
    (pending : List Slot) (index : Slot) (found : search slots key pending = .empty index) :
    slots index = none ∧ ∃ before after, pending = before ++ index :: after ∧ ∀ prior ∈ before, slots prior ≠ none := by
  induction pending with
  | nil => cases found
  | cons current rest ih =>
      cases currentSlot : slots current with
      | none =>
          have equal : current = index := by simpa [search, currentSlot, Found.empty.injEq] using found
          subst current
          exact ⟨currentSlot, [], rest, rfl, by simp⟩
      | some pair =>
          by_cases same : pair.1 = key
          · simp [search, currentSlot, same] at found
          · obtain ⟨empty, before, after, tail, occupied⟩ := ih (by simpa only [search, currentSlot, same, ↓reduceIte] using found)
            refine ⟨empty, current :: before, after, by simp only [List.cons_append, tail], ?_⟩
            intro prior member
            rcases List.mem_cons.mp member with rfl | member
            · simp [currentSlot]
            · exact occupied prior member

end MicroCFTA.FlatMemoProbe
