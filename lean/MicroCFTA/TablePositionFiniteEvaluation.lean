import MicroCFTA.TablePositionCountBound
import MicroCFTA.SourceSizedTableEvaluation
import MicroCFTA.SourceRowsMinimum

/-!
# Finite tables for optimized bottom-up ranking

A finite count inventory contains every state key and every size through the
input term's node count. Each count has a finite source evaluation. The term
worker then uses finite child maps and finite count lookups only. It returns
the exact original bottom-up rank, including failure for an unaccepted term.
The state type itself can be infinite.
-/
namespace MicroCFTA.TablePositionFiniteEvaluation
open Language RecursiveSize SizedRank TablePositionCountBound

variable {State Symbol Key Value : Type}

/-- Read the first matching entry of a finite table. -/
def read [DecidableEq Key] : List (Key × Value) → Key → Option Value
  | [], _ => none
  | entry :: rest, key => if entry.1 = key then some entry.2 else read rest key

/-- A present key has its value when all matching entries agree. -/
theorem read_present [DecidableEq Key] (entries : List (Key × Value)) (key : Key) (value : Value)
    (present : (key, value) ∈ entries)
    (same : ∀ entry ∈ entries, entry.1 = key → entry.2 = value) : read entries key = some value := by
  induction entries with
  | nil => cases present
  | cons entry rest ih =>
      by_cases matchKey : entry.1 = key
      · simp only [read, matchKey, ↓reduceIte, same entry (by simp) matchKey]
      · have later : (key, value) ∈ rest := by
          rcases List.mem_cons.mp present with first | later
          · exact False.elim (matchKey (congrArg Prod.fst first).symm)
          · exact later
        simpa only [read, matchKey, ↓reduceIte] using ih later (fun item member => same item (by simp [member]))

/-- A table made from a key list reads back its value at every listed key. -/
theorem read_map [DecidableEq Key] (keys : List Key) (values : Key → Value) (key : Key) (present : key ∈ keys) :
    read (keys.map (fun key => (key, values key))) key = some (values key) := by
  apply read_present _ key (values key) (List.mem_map.mpr ⟨key, present, rfl⟩)
  intro entry member same
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  exact congrArg values same

/-- An absent key has no stored value. -/
theorem read_absent [DecidableEq Key] (entries : List (Key × Value)) (key : Key)
    (absent : ∀ entry ∈ entries, entry.1 ≠ key) : read entries key = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simp only [read, absent entry (by simp), ↓reduceIte]
      exact ih (fun item member => absent item (by simp [member]))

/-- The finite count inventory includes size zero and every requested state key. -/
def counts (A : Automaton State Symbol) (keys : List State) (bound : Nat) :
    List ((Nat × State) × Nat) :=
  (List.range (bound + 1)).flatMap fun size => keys.map fun state => ((size, state), countAt A size state)

/-- Count lookup has a finite-table implementation with zero outside the inventory. -/
def countLookup [DecidableEq State] (entries : List ((Nat × State) × Nat)) (size : Nat) (state : State) : Nat :=
  (read entries (size, state)).getD 0

/-- Every listed count is exactly the original source count query. -/
theorem counts_member (A : Automaton State Symbol) (keys : List State) (bound : Nat)
    (entry : (Nat × State) × Nat) (member : entry ∈ counts A keys bound) :
    entry.1.1 ≤ bound ∧ entry.1.2 ∈ keys ∧ entry.2 = countAt A entry.1.1 entry.1.2 := by
  obtain ⟨size, sizeIn, present⟩ := List.mem_flatMap.mp member
  obtain ⟨state, stateIn, rfl⟩ := List.mem_map.mp present
  exact ⟨by change size ≤ bound; have fits := List.mem_range.mp sizeIn; omega, stateIn, rfl⟩

/-- Missing row keys have zero count at every size. -/
theorem count_outside (A : Automaton State Symbol) (keys : List State)
    (supported : SourceRowsMinimum.Supported A keys) (state : State) (absent : state ∉ keys) (size : Nat) :
    countAt A size state = 0 := by
  have empty : A state = [] := List.eq_nil_iff_forall_not_mem.mpr (fun transition member => absent (supported state transition member))
  cases size <;> simp [countAt, empty]

/-- The finite count table agrees with all source count reads through the term bound. -/
theorem counts_exact [DecidableEq State] (A : Automaton State Symbol) (keys : List State)
    (supported : SourceRowsMinimum.Supported A keys) (bound size : Nat) (within : size ≤ bound) (state : State) :
    countLookup (counts A keys bound) size state = countAt A size state := by
  by_cases present : state ∈ keys
  · have found : ((size, state), countAt A size state) ∈ counts A keys bound := by
      exact List.mem_flatMap.mpr ⟨size, List.mem_range.mpr (by omega), List.mem_map.mpr ⟨state, present, rfl⟩⟩
    have same : read (counts A keys bound) (size, state) = some (countAt A size state) := by
      apply read_present _ _ _ found
      intro entry member equal
      have actual := (counts_member A keys bound entry member).2.2
      simpa only [equal] using actual
    simp only [countLookup, same, Option.getD_some]
  · have missing : read (counts A keys bound) (size, state) = none := by
      apply read_absent
      intro entry member equal
      have keyIn := (counts_member A keys bound entry member).2.1
      rw [congrArg Prod.snd equal] at keyIn
      exact present keyIn
    simp only [countLookup, missing, Option.getD_none, count_outside A keys supported state present size]

/-- A finite inventory evaluates each original count recurrence before rank lookup. -/
inductive CountsEvaluation (A : Automaton State Symbol) : List ((Nat × State) × Nat) → Prop where
  | nil : CountsEvaluation A []
  | cons (query : Nat × State) (value : Nat) (rest : List ((Nat × State) × Nat))
      (head : SourceSizedTableEvaluation.Evaluation A (query.1 + 1) query.1 query.2 value (compileAt A query.1 query.2))
      (tail : CountsEvaluation A rest) : CountsEvaluation A ((query, value) :: rest)

/-- Every finite inventory has completed count derivations, including cyclic graphs. -/
theorem counts_finite (A : Automaton State Symbol) (keys : List State) (bound : Nat) :
    CountsEvaluation A (counts A keys bound) := by
  have complete : ∀ entries : List ((Nat × State) × Nat),
      (∀ entry ∈ entries, entry.2 = countAt A entry.1.1 entry.1.2) → CountsEvaluation A entries := by
    intro entries
    induction entries with
    | nil => intro _; exact .nil
    | cons entry rest ih =>
        intro same
        apply CountsEvaluation.cons
        · rw [same entry (by simp)]
          exact SourceSizedTableEvaluation.finite_bound A entry.1.1 entry.1.2
        · exact ih (fun item member => same item (by simp [member]))
  exact complete _ (fun entry member => (counts_member A keys bound entry member).2.2)

/-- A finite child map treats both absent entries and explicit failure as no rank. -/
def positionLookup [DecidableEq State] (entries : List (State × Option Position)) (state : State) : Option Position :=
  (read entries state).join

/-- Evaluate each finite child map once, then visit the actual finite state keys. -/
def evaluate [DecidableEq State] [DecidableEq Symbol] (A : Automaton State Symbol)
    (countTable : List ((Nat × State) × Nat)) (keys : List State) : Term Symbol → List (State × Option Position)
  | .node symbol terms =>
      let childMaps := terms.map (evaluate A countTable keys)
      let tables := childMaps.map positionLookup
      keys.map fun state => (state, row (countLookup countTable) symbol tables (A state))

/-- Finite map execution has the exact explicit-callback bottom-up result at every state. -/
theorem evaluate_exact [DecidableEq State] [DecidableEq Symbol] (A : Automaton State Symbol)
    (keys : List State) (supported : SourceRowsMinimum.Supported A keys)
    (countTable : List ((Nat × State) × Nat)) (term : Term Symbol) :
    positionLookup (evaluate A countTable keys term) = positions A (countLookup countTable) term := by
  induction term using Term.rec
    (motive_2 := fun terms => (terms.map (evaluate A countTable keys)).map positionLookup =
      terms.map (positions A (countLookup countTable))) with
  | node symbol terms ih =>
      funext state
      rw [evaluate]
      simp only [ih]
      by_cases present : state ∈ keys
      · simp only [positionLookup, read_map keys _ state present, Option.join_some, positions]
      · have missing : read (keys.map (fun state => (state,
            row (countLookup countTable) symbol (terms.map (positions A (countLookup countTable))) (A state)))) state = none := by
          apply read_absent
          intro entry member same
          obtain ⟨key, keyIn, rfl⟩ := List.mem_map.mp member
          exact present (same ▸ keyIn)
        have empty : A state = [] := List.eq_nil_iff_forall_not_mem.mpr (fun transition member => present (supported state transition member))
        simp only [positionLookup, missing, Option.join_none, positions, empty, row]
  | nil => rfl
  | cons term terms ih ihs => simp only [List.map_cons, ih, ihs]

/-- A finite count inventory and finite child maps return the actual optimized rank. -/
theorem finite_rank [DecidableEq State] [DecidableEq Symbol] (A : Automaton State Symbol)
    (keys : List State) (supported : SourceRowsMinimum.Supported A keys) (term : Term Symbol) :
    CountsEvaluation A (counts A keys (nodeSize term)) ∧
      positionLookup (evaluate A (counts A keys (nodeSize term)) keys term) = TablePosition.positionsOf A term := by
  refine ⟨counts_finite A keys (nodeSize term), ?_⟩
  rw [evaluate_exact A keys supported]
  rw [positions_congr A (countLookup (counts A keys (nodeSize term))) (countAt A) (nodeSize term)
    (fun size within state => counts_exact A keys supported _ size within state) term (Nat.le_refl _)]
  exact positions_actual A term

end MicroCFTA.TablePositionFiniteEvaluation
