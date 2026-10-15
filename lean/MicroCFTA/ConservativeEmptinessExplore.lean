import Std

/-!
# Finite exploration for conservative emptiness rows

This is the worklist schedule from main a22b2ad4. Each supplied row list is
already a completed finite value. The budget counts new admitted keys. It
does not bound source exposure, projection, intersection, or thunk demands.
Natural budgets model the source countdown from 1000 without negative values.
-/
namespace MicroCFTA.ConservativeEmptinessExplore

/-- A completed item distinguishes the empty node from a key with its closure test. -/
inductive Item where
  | empty
  | resident (key : Int) (closed : Bool)
  deriving DecidableEq, Repr

/-- Each finite row lists all of its completed requirements. -/
abbrev Rows := List (List Item)

/-- A finite table retains the rows stored under each admitted physical key. -/
abbrev Table := List (Int × Rows)

/-- Read the first stored row list for the requested key. -/
def lookup (key : Int) : Table → Option Rows
  | [] => none
  | (other, rows) :: rest => if key = other then some rows else lookup key rest

/-- Absence from the table is exactly absence from its finite key list. -/
theorem lookup_none_iff (key : Int) (seen : Table) :
    lookup key seen = none ↔ key ∉ seen.map Prod.fst := by
  induction seen with
  | nil => simp [lookup]
  | cons first rest ih =>
      rcases first with ⟨other, rows⟩
      by_cases same : key = other <;> simp [lookup, same, ih]

/-- Skip in source order: no budget, an existing key, or an open input. -/
def skip (budget : Nat) (seen : Table) (key : Int) (closed : Bool) : Bool :=
  budget == 0 || (lookup key seen).isSome || !closed

/-- An admitted item has positive budget and a key absent from the current table. -/
theorem admitted (budget : Nat) (seen : Table) (key : Int) (closed : Bool)
    (fresh : skip budget seen key closed = false) :
    0 < budget ∧ lookup key seen = none ∧ closed = true := by
  simp only [skip, Bool.or_eq_false_iff, Bool.not_eq_false', beq_eq_false_iff_ne] at fresh
  refine ⟨by omega, ?_, fresh.2⟩
  cases found : lookup key seen with
  | none => rfl
  | some rows => simp [found] at fresh

/-- Drain the actual worklist and insert only new closed keys with remaining budget. -/
def explore (supply : Int → Rows) (budget : Nat) (seen : Table) (pending : List Item) : Table :=
  match pending with
  | [] => seen
  | .empty :: rest => explore supply budget seen rest
  | .resident key closed :: rest =>
      if skip budget seen key closed then explore supply budget seen rest
      else explore supply (budget - 1) ((key, supply key) :: seen) ((supply key).flatten ++ rest)
termination_by (budget, pending.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have positive := (admitted budget seen key closed (Bool.eq_false_iff.mpr (by assumption))).1
    omega

/-- Exploration retains old reads, preserves unique keys, and respects the admission budget. -/
theorem explore_correct (supply : Int → Rows) (budget : Nat) (seen : Table) (pending : List Item) :
    (∀ key rows, lookup key seen = some rows → lookup key (explore supply budget seen pending) = some rows) ∧
    ((seen.map Prod.fst).Nodup → ((explore supply budget seen pending).map Prod.fst).Nodup) ∧
    (explore supply budget seen pending).length ≤ seen.length + budget := by
  rw [explore.eq_def]
  cases pending with
  | nil =>
      simp only
      exact ⟨fun _ _ found => found, fun unique => unique, by omega⟩
  | cons first rest =>
      cases first with
      | empty => exact explore_correct supply budget seen rest
      | resident key closed =>
          by_cases skipped : skip budget seen key closed = true
          · simpa only [skipped, ↓reduceIte] using explore_correct supply budget seen rest
          · simp only [skipped, Bool.false_eq_true, ↓reduceIte]
            have fresh := admitted budget seen key closed (Bool.eq_false_iff.mpr skipped)
            obtain ⟨retained, unique, bound⟩ := explore_correct supply (budget - 1)
              ((key, supply key) :: seen) ((supply key).flatten ++ rest)
            refine ⟨?_, ?_, ?_⟩
            · intro oldKey rows found
              apply retained oldKey rows
              by_cases same : oldKey = key
              · subst oldKey
                rw [fresh.2.1] at found
                cases found
              · simpa only [lookup, same, ↓reduceIte] using found
            · intro original
              apply unique
              simp only [List.map_cons, List.nodup_cons]
              exact ⟨(lookup_none_iff key seen).mp fresh.2.1, original⟩
            · simp only [List.length_cons] at bound
              omega
termination_by (budget, pending.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    omega

/-- Every previously stored key retains its exact original rows. -/
theorem retains (supply : Int → Rows) (budget : Nat) (seen : Table) (pending : List Item)
    (key : Int) (rows : Rows) (found : lookup key seen = some rows) :
    lookup key (explore supply budget seen pending) = some rows :=
  (explore_correct supply budget seen pending).1 key rows found

/-- A table with unique keys never admits the same key twice. -/
theorem keys_nodup (supply : Int → Rows) (budget : Nat) (seen : Table) (pending : List Item)
    (unique : (seen.map Prod.fst).Nodup) : ((explore supply budget seen pending).map Prod.fst).Nodup :=
  (explore_correct supply budget seen pending).2.1 unique

/-- At most one row entry is added for each unit of initial budget. -/
theorem length_le (supply : Int → Rows) (budget : Nat) (seen : Table) (pending : List Item) :
    (explore supply budget seen pending).length ≤ seen.length + budget :=
  (explore_correct supply budget seen pending).2.2

/-- Exhaustion still drains queued items and returns the exact original table. -/
theorem zero_budget (supply : Int → Rows) (seen : Table) (pending : List Item) :
    explore supply 0 seen pending = seen := by
  induction pending with
  | nil => simp [explore]
  | cons first rest ih =>
      cases first <;> simpa [explore, skip] using ih

end MicroCFTA.ConservativeEmptinessExplore
