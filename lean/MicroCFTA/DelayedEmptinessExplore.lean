import MicroCFTA.ConservativeEmptinessExplore

/-!
# Reached worklist traces with delayed requirements

Each reached task is forced before the empty, budget, seen-key, and closure
tests. An admitted value is exposed only after these tests. Exposure returns
delayed tasks. The trace stores the original forced value and ordered task
rows, then visits those tasks before the remaining worklist. No constructor
assumes that an arbitrary force or exposure completes.
-/
namespace MicroCFTA.DelayedEmptinessExplore
open ConservativeEmptinessExplore (Item)

/-- Each admitted key retains its original forced value and delayed row tasks. -/
structure Entry (Task Value : Type) where
  key : Int
  value : Value
  rows : List (List Task)

/-- The logical table retains complete entries in insertion order. -/
abbrev Table (Task Value : Type) := List (Entry Task Value)

variable {Task Value : Type}

/-- Read the first original entry stored under a key. -/
def lookup (key : Int) : Table Task Value → Option (Entry Task Value)
  | [] => none
  | entry :: rest => if key = entry.key then some entry else lookup key rest

/-- Actual lookup absence is exactly absence from the stored key list. -/
theorem lookup_none_iff (key : Int) (seen : Table Task Value) :
    lookup key seen = none ↔ key ∉ seen.map Entry.key := by
  induction seen with
  | nil => simp [lookup]
  | cons entry rest ih =>
      by_cases same : key = entry.key <;> simp [lookup, same, ih]

/-- Run the source tests in order after forcing the head task. -/
def skip (budget : Nat) (seen : Table Task Value) (key : Int) (closed : Bool) : Bool :=
  budget == 0 || (lookup key seen).isSome || !closed

/-- Admission derives positive budget, a fresh key, and the closed flag. -/
theorem admitted (budget : Nat) (seen : Table Task Value) (key : Int) (closed : Bool)
    (fresh : skip budget seen key closed = false) :
    0 < budget ∧ lookup key seen = none ∧ closed = true := by
  simp only [skip, Bool.or_eq_false_iff, Bool.not_eq_false', beq_eq_false_iff_ne] at fresh
  refine ⟨by omega, ?_, fresh.2⟩
  cases found : lookup key seen with
  | none => rfl
  | some entry => simp [found] at fresh

variable {Heap : Type}

/-- A reached finite trace retains each actual force, exposure, and returned heap. -/
inductive Trace (force : Task → Heap → Value → Heap → Prop)
    (expose : Value → Heap → List (List Task) → Heap → Prop) (encode : Value → Item) :
    Nat → Table Task Value → List Task → Heap → Table Task Value → Heap → Prop where
  | done : Trace force expose encode budget seen [] heap seen heap
  | empty (forced : force task before value forcedHeap) (encoded : encode value = .empty)
      (rest : Trace force expose encode budget seen pending forcedHeap final after) :
      Trace force expose encode budget seen (task :: pending) before final after
  | skipped (forced : force task before value forcedHeap) (encoded : encode value = .resident key closed)
      (skipped : skip budget seen key closed = true)
      (rest : Trace force expose encode budget seen pending forcedHeap final after) :
      Trace force expose encode budget seen (task :: pending) before final after
  | admit {task : Task} {before : Heap} {value : Value} {forcedHeap : Heap} {key : Int} {closed : Bool}
      {budget : Nat} {seen : Table Task Value} {rows : List (List Task)} {exposedHeap : Heap}
      {pending : List Task} {final : Table Task Value} {after : Heap}
      (forced : force task before value forcedHeap) (encoded : encode value = .resident key closed)
      (fresh : skip budget seen key closed = false) (exposed : expose value forcedHeap rows exposedHeap)
      (rest : Trace force expose encode (budget - 1) (⟨key, value, rows⟩ :: seen)
        (rows.flatten ++ pending) exposedHeap final after) :
      Trace force expose encode budget seen (task :: pending) before final after

variable {force : Task → Heap → Value → Heap → Prop}
variable {expose : Value → Heap → List (List Task) → Heap → Prop} {encode : Value → Item}

/-- A completed trace retains old entries, unique keys, and a budget-bounded prefix of actual admissions. -/
theorem Trace.effects (trace : Trace force expose encode budget seen pending before final after) :
    (∀ key entry, lookup key seen = some entry → lookup key final = some entry) ∧
    ((seen.map Entry.key).Nodup → (final.map Entry.key).Nodup) ∧
    ∃ added, final = added ++ seen ∧ added.length ≤ budget := by
  induction trace with
  | done => exact ⟨fun _ _ found => found, fun unique => unique, [], rfl, by simp⟩
  | empty forced encoded rest ih => exact ih
  | skipped forced encoded skipped rest ih => exact ih
  | @admit task before value forcedHeap key closed budget seen rows exposedHeap pending final after
      forced encoded fresh exposed rest ih =>
      obtain ⟨retained, unique, added, storedPrefix, bound⟩ := ih
      have admission := admitted budget seen key closed fresh
      refine ⟨?_, ?_, added ++ [⟨key, value, rows⟩], ?_, ?_⟩
      · intro oldKey entry found
        apply retained oldKey entry
        by_cases same : oldKey = key
        · subst oldKey
          rw [admission.2.1] at found
          cases found
        · simpa only [lookup, same, ↓reduceIte] using found
      · intro original
        apply unique
        simp only [List.map_cons, List.nodup_cons]
        exact ⟨(lookup_none_iff key seen).mp admission.2.1, original⟩
      · simpa only [List.append_assoc, List.singleton_append] using storedPrefix
      · simp only [List.length_append, List.length_singleton]
        omega

/-- Every original lookup retains the same complete entry, including its delayed task rows. -/
theorem Trace.retains (trace : Trace force expose encode budget seen pending before final after)
    (key : Int) (entry : Entry Task Value) (found : lookup key seen = some entry) : lookup key final = some entry :=
  trace.effects.1 key entry found

/-- A fresh-key worklist never adds a second occurrence of an existing key. -/
theorem Trace.keys_nodup (trace : Trace force expose encode budget seen pending before final after)
    (unique : (seen.map Entry.key).Nodup) : (final.map Entry.key).Nodup := trace.effects.2.1 unique

/-- Each new entry in the returned prefix comes from one reached admission. -/
theorem Trace.admitted_prefix (trace : Trace force expose encode budget seen pending before final after) :
    ∃ added, final = added ++ seen ∧ added.length ≤ budget := trace.effects.2.2

/-- Initial budget bounds the number of new retained entries. -/
theorem Trace.length_le (trace : Trace force expose encode budget seen pending before final after) :
    final.length ≤ seen.length + budget := by
  obtain ⟨added, rfl, bound⟩ := trace.admitted_prefix
  simp only [List.length_append]
  omega

/-- Every initially queued task has a force receipt in the reached trace, even after budget exhaustion. -/
theorem Trace.pending_forced (trace : Trace force expose encode budget seen pending before final after) :
    ∀ task ∈ pending, ∃ leafBefore value leafAfter, force task leafBefore value leafAfter := by
  induction trace with
  | done => intro task impossible; cases impossible
  | empty forced encoded rest ih =>
      intro task member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, _, _, forced⟩
      · exact ih task member
  | skipped forced encoded skipped rest ih =>
      intro task member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, _, _, forced⟩
      · exact ih task member
  | admit forced encoded fresh exposed rest ih =>
      intro task member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, _, _, forced⟩
      · exact ih task (List.mem_append_right _ member)

/-- Every new stored entry retains its actual force, closed-key test, and delayed exposure receipts. -/
theorem Trace.entry_origin (trace : Trace force expose encode budget seen pending before final after)
    (key : Int) (entry : Entry Task Value) (found : lookup key final = some entry) :
    lookup key seen = some entry ∨
      ∃ task leafBefore forcedHeap exposedHeap, force task leafBefore entry.value forcedHeap ∧
        encode entry.value = .resident entry.key true ∧ expose entry.value forcedHeap entry.rows exposedHeap := by
  induction trace with
  | done => exact Or.inl found
  | empty forced encoded rest ih => exact ih found
  | skipped forced encoded skipped rest ih => exact ih found
  | @admit task before value forcedHeap admittedKey closed budget seen rows exposedHeap pending final after
      forced encoded fresh exposed rest ih =>
      rcases ih found with old | entered
      · by_cases same : key = admittedKey
        · subst key
          have identical : (⟨admittedKey, value, rows⟩ : Entry Task Value) = entry := by
            simpa only [lookup, ↓reduceIte, Option.some.injEq] using old
          subst entry
          refine Or.inr ⟨task, before, forcedHeap, exposedHeap, forced, ?_, exposed⟩
          simpa only [(admitted budget seen admittedKey closed fresh).2.2] using encoded
        · exact Or.inl (by simpa only [lookup, same, ↓reduceIte] using old)
      · exact Or.inr entered

/-- Every delayed task in a newly admitted row is forced before the reached trace finishes. -/
theorem Trace.new_rows_forced (trace : Trace force expose encode budget seen pending before final after)
    (key : Int) (entry : Entry Task Value) (found : lookup key final = some entry) :
    lookup key seen = some entry ∨
      ∀ task ∈ entry.rows.flatten, ∃ leafBefore value leafAfter, force task leafBefore value leafAfter := by
  induction trace with
  | done => exact Or.inl found
  | empty forced encoded rest ih => exact ih found
  | skipped forced encoded skipped rest ih => exact ih found
  | @admit task before value forcedHeap admittedKey closed budget seen rows exposedHeap pending final after
      forced encoded fresh exposed rest ih =>
      rcases ih found with old | entered
      · by_cases same : key = admittedKey
        · subst key
          have identical : (⟨admittedKey, value, rows⟩ : Entry Task Value) = entry := by
            simpa only [lookup, ↓reduceIte, Option.some.injEq] using old
          subst entry
          exact Or.inr (fun child member => rest.pending_forced child (List.mem_append_left _ member))
        · exact Or.inl (by simpa only [lookup, same, ↓reduceIte] using old)
      · exact Or.inr entered

/-- Empty budget retains the table, but the trace still forces every queued task. -/
theorem Trace.zero_budget (trace : Trace force expose encode 0 seen pending before final after) : final = seen := by
  obtain ⟨added, storedPrefix, bound⟩ := trace.admitted_prefix
  have empty : added = [] := List.length_eq_zero_iff.mp (by omega)
  simpa only [empty, List.nil_append] using storedPrefix

end MicroCFTA.DelayedEmptinessExplore
