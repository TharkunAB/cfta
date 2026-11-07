import MicroCFTA.SourceSizedDeterminizationHolderOrder

/-!
# Incremental holder insertion in the source schedule

`deterministicRows.go` builds singleton entries from each fresh subset.
`fromListWith (<>)` prepends the new singleton to its stored bucket.
The outer union appends that bucket to the earlier holder list.
This value view retains the actual insertion order and repeated entries.
It does not specify the native map's storage representation.
-/
namespace MicroCFTA.SourceSizedDeterminizationHolderInsertion

variable {State Key : Type} [DecidableEq State]

/-- Prepend one source singleton entry at its owner. -/
def insert (holding : State → List Key) (entry : State × Key) (state : State) : List Key :=
  if state = entry.1 then entry.2 :: holding state else holding state

/-- Insert the singleton entries from left to right. -/
def fromEntries : List (State × Key) → (State → List Key) → State → List Key
  | [], holding => holding
  | entry :: entries, holding => fromEntries entries (insert holding entry)

/-- Singleton insertion retains the old bucket and the new matching entry. -/
theorem mem_insert (holding : State → List Key) (entry : State × Key) (state : State) (key : Key) :
    key ∈ insert holding entry state ↔ key ∈ holding state ∨ (state = entry.1 ∧ key = entry.2) := by
  by_cases same : state = entry.1 <;> simp [insert, same, or_comm]

/-- A holder bucket contains precisely its old entries and matching new entries. -/
theorem mem_fromEntries (entries : List (State × Key)) (holding : State → List Key)
    (state : State) (key : Key) :
    key ∈ fromEntries entries holding state ↔
      key ∈ holding state ∨ ∃ entry ∈ entries, state = entry.1 ∧ key = entry.2 := by
  induction entries generalizing holding with
  | nil => simp [fromEntries]
  | cons entry entries ih =>
    rw [fromEntries, ih, mem_insert]
    constructor
    · rintro ((old | matched) | ⟨other, present, matched⟩)
      · exact Or.inl old
      · exact Or.inr ⟨entry, by simp, matched⟩
      · exact Or.inr ⟨other, List.mem_cons_of_mem entry present, matched⟩
    · rintro (old | ⟨other, present, matched⟩)
      · exact Or.inl (Or.inl old)
      · rcases List.mem_cons.mp present with same | tail
        · subst other
          exact Or.inl (Or.inr matched)
        · exact Or.inr ⟨other, tail, matched⟩

/-- Enumerate fresh subsets, then enumerate the states in each subset. -/
def entries (fresh : List (List State)) : List (State × List State) :=
  fresh.flatMap fun key => key.map fun state => (state, key)

omit [DecidableEq State] in
/-- Each singleton entry records one fresh subset and one of its states. -/
theorem mem_entries (fresh : List (List State)) (state : State) (key : List State) :
    (state, key) ∈ entries fresh ↔ key ∈ fresh ∧ state ∈ key := by
  simp only [entries, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨other, present, owner, inside, same⟩
    have keyEq : other = key := congrArg Prod.snd same
    have stateEq : owner = state := congrArg Prod.fst same
    subst other
    subst owner
    exact ⟨present, inside⟩
  · rintro ⟨present, inside⟩
    exact ⟨key, present, state, inside, rfl⟩

/-- Build the new holder map with the source singleton insertion schedule. -/
def freshHolders (fresh : List (List State)) : State → List (List State) :=
  fromEntries (entries fresh) (fun _ => [])

/-- The fresh bucket contains exactly fresh subsets that contain the queried state. -/
theorem mem_freshHolders (fresh : List (List State)) (state : State) (key : List State) :
    key ∈ freshHolders fresh state ↔ key ∈ fresh ∧ state ∈ key := by
  rw [freshHolders, mem_fromEntries]
  simp only [List.not_mem_nil, false_or]
  constructor
  · rintro ⟨entry, present, stateEq, keyEq⟩
    have same : entry = (state, key) := Prod.ext stateEq.symm keyEq.symm
    rw [same] at present
    exact (mem_entries fresh state key).mp present
  · intro member
    exact ⟨(state, key), (mem_entries fresh state key).mpr member, rfl, rfl⟩

/-- Append the new holder bucket after the earlier holder bucket. -/
def update (holding : State → List (List State)) (fresh : List (List State))
    (state : State) : List (List State) :=
  holding state ++ freshHolders fresh state

/-- Literal incremental insertion retains the recomputed holder membership. -/
theorem update_membership (holding : State → List (List State)) (known fresh : List (List State))
    (same : ∀ state key,
      key ∈ holding state ↔ key ∈ SourceSizedDeterminizationRun.holders known state)
    (state : State) (key : List State) :
    key ∈ update holding fresh state ↔
      key ∈ SourceSizedDeterminizationRun.holders (known ++ fresh) state := by
  simp only [update, List.mem_append, mem_freshHolders, same state key,
    SourceSizedDeterminizationRun.mem_holders]
  constructor
  · rintro (⟨present, inside⟩ | ⟨present, inside⟩)
    · exact ⟨Or.inl present, inside⟩
    · exact ⟨Or.inr present, inside⟩
  · rintro ⟨present | present, inside⟩
    · exact Or.inl ⟨present, inside⟩
    · exact Or.inr ⟨present, inside⟩

end MicroCFTA.SourceSizedDeterminizationHolderInsertion
