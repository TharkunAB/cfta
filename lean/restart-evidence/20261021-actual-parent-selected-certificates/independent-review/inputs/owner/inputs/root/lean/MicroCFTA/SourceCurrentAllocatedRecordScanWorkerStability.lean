import MicroCFTA.SourceCurrentAllocatedRecordScanWorker
import MicroCFTA.SourceCurrentAllocatedScanWorkerStability

/-!
# Successful bound stability with original class records

Increasing the five stage bounds retains every selected record occurrence,
the stopped class, and the complete checked state and fourth memo.
The conjunction budget stays fixed. Repeated paths need no uniqueness law.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecordScanWorkerStability
open Language EqualityNormalize InternedConstructorTemplates SourceEqualityClassOrder
open SourceCurrentAllocatedRecordScanWorker
open SourceCurrentAllocatedScanWorker (gate query decision)
open SourceCurrentAllocatedScanWorkerStability
  (bind_done_iff gate_done_stable query_done_stable decision_done_stable)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Successful selection retains the literal input record before the returned records. -/
theorem select_done_iff (record : Record) (first : Outcome Result width)
    (result : Result) (after : Checked width) (saved : Memo) :
    select record first = .done result after saved ↔
      ∃ rest, first = .done rest after saved ∧ result = (rest.1, record :: rest.2) := by
  cases first with
  | done value state memo =>
      obtain ⟨stopped, selected⟩ := value
      constructor
      · intro actual; cases actual; exact ⟨(stopped, selected), rfl, rfl⟩
      · rintro ⟨_, same, returned⟩; cases same; cases returned; rfl
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, impossible, _⟩; cases impossible

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)]

/-- Larger stage bounds retain the original records and exact whole scan return. -/
theorem scan_done_stable {g s p h n G S P H N budget : Nat} {values : List (Value Symbol Guard)}
    {records : List Record} {before after : Checked width} {memo saved : Memo} {result : Result}
    (actual : scan g s p h n budget values records before memo = .done result after saved)
    (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughN : n ≤ N) :
    scan G S P H N budget values records before memo = .done result after saved := by
  induction records generalizing before memo result after saved with
  | nil => exact actual
  | cons record records ih =>
      obtain ⟨primary, middle, current, first, remaining⟩ := (bind_done_iff _ _ result after saved).mp actual
      simp only [scan, gate_done_stable first enoughG, SourceCurrentAllocatedScanWorker.Outcome.bind]
      cases primary with
      | false =>
          obtain ⟨rest, completed, returned⟩ := (select_done_iff record _ result after saved).mp remaining
          apply (select_done_iff record _ result after saved).mpr
          exact ⟨rest, ih completed, returned⟩
      | true =>
          obtain ⟨secondary, later, fourth, second, next⟩ := (bind_done_iff _ _ result after saved).mp remaining
          simp only [gate_done_stable second enoughS]
          cases secondary with
          | true => exact ih next
          | false =>
              obtain ⟨value, checked, queriedMemo, queried, decisionPhase⟩ := (bind_done_iff _ _ result after saved).mp next
              simp only [query_done_stable queried enoughP enoughH enoughN]
              obtain ⟨answer, reached, final, decided, continuation⟩ := (bind_done_iff _ _ result after saved).mp decisionPhase
              simp only [decision_done_stable decided enoughP enoughH]
              cases answer with
              | true => exact continuation
              | false => exact ih continuation

/-- Successful bounds identify all record occurrences, the checked state, and fourth memo. -/
theorem scan_done_unique {g s p h n G S P H N budget : Nat} {values : List (Value Symbol Guard)}
    {records : List Record} {before after later : Checked width} {memo saved current : Memo} {first second : Result}
    (one : scan g s p h n budget values records before memo = .done first after saved)
    (two : scan G S P H N budget values records before memo = .done second later current) :
    first = second ∧ after = later ∧ saved = current := by
  have left := scan_done_stable one (Nat.le_max_left g G) (Nat.le_max_left s S)
    (Nat.le_max_left p P) (Nat.le_max_left h H) (Nat.le_max_left n N)
  have right := scan_done_stable two (Nat.le_max_right g G) (Nat.le_max_right s S)
    (Nat.le_max_right p P) (Nat.le_max_right h H) (Nat.le_max_right n N)
  exact SourceCurrentAllocatedScanWorker.Outcome.done.inj (left.symm.trans right)

end MicroCFTA.SourceCurrentAllocatedRecordScanWorkerStability
