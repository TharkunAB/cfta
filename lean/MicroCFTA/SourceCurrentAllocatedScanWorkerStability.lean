import MicroCFTA.SourceCurrentAllocatedScanWorker
import MicroCFTA.SourceCurrentAllocatedSeededWorkerStability
import MicroCFTA.SourceCurrentAllocatedConjunctionWorkerActual

/-!
# Successful bound stability for literal current class scanning

Five independent stage bounds can increase while the conjunction budget
stays fixed. Each successful prefix retains its exact checked state and
fourth memo. Different successful bounds identify the stopped class and
selected list as well as every returned state field.
-/
namespace MicroCFTA.SourceCurrentAllocatedScanWorkerStability
open Language EqualityNormalize InternedConstructorTemplates
open SourceCurrentAllocatedScanWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A successful bind exposes its exact returned prefix state and fourth memo. -/
theorem bind_done_iff (first : Outcome A width)
    (next : A → Checked width → Memo → Outcome B width) (result : B) (after : Checked width) (saved : Memo) :
    first.bind next = .done result after saved ↔
      ∃ value middle current, first = .done value middle current ∧ next value middle current = .done result after saved := by
  cases first with
  | done value state memo =>
      constructor
      · intro actual; exact ⟨value, state, memo, rfl, actual⟩
      · rintro ⟨_, _, _, same, actual⟩; cases same; exact actual
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, _, impossible, _⟩; cases impossible

/-- Selection adds the literal head occurrence without changing the returned state or memo. -/
theorem select_done_iff (paths : Class) (first : Outcome Result width)
    (result : Result) (after : Checked width) (saved : Memo) :
    first.select paths = .done result after saved ↔
      ∃ rest, first = .done rest after saved ∧ result = (rest.1, paths :: rest.2) := by
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

/-- More fuel preserves a supplied gate success and its complete checked return. -/
theorem gate_done_stable [DecidableEq (EdgeKey Symbol Guard)] {mode : Bool} {fuel larger : Nat} {values : List (Value Symbol Guard)}
    {paths : Class} {before after : Checked width} {memo saved : Memo} {answer : Bool}
    (actual : gate mode fuel values paths before memo = .done answer after saved) (enough : fuel ≤ larger) :
    gate mode larger values paths before memo = .done answer after saved := by
  cases mode with
  | false =>
      cases observed : SourceCurrentAllocatedGateWorker.secondary fuel values paths before with
      | done value state =>
          simp only [gate, Bool.false_eq_true, ite_false, observed] at actual
          simp only [gate, Bool.false_eq_true, ite_false,
            SourceCurrentAllocatedGateWorker.secondary_done_stable observed enough]
          exact actual
      | failed =>
          simp only [gate, Bool.false_eq_true, ite_false, observed] at actual
          cases actual
  | true =>
      cases observed : SourceCurrentAllocatedGateWorker.primary fuel values paths before with
      | done value state =>
          simp only [gate, ite_true, observed] at actual
          simp only [gate, ite_true,
            SourceCurrentAllocatedGateWorker.primary_done_stable observed enough]
          exact actual
      | failed =>
          simp only [gate, ite_true, observed] at actual
          cases actual

/-- Larger projection, read, and native bounds preserve a successful first-seeded phase. -/
theorem query_done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {p h n P H N : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : query p h n values paths before memo = .done result after saved)
    (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughN : n ≤ N) :
    query P H N values paths before memo = .done result after saved := by
  cases observed : SourceCurrentAllocatedSeededWorker.seeded p h n values (paths.map (List.map Int.ofNat)) before with
  | done value state =>
      simp only [query, observed] at actual
      simp only [query, SourceCurrentAllocatedSeededWorkerStability.seeded_done_stable observed enoughP enoughH enoughN]
      exact actual
  | failed => simp only [query, observed] at actual; cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Larger row bounds preserve the same completed fourth-memo phase at fixed budget. -/
theorem decision_done_stable {p h P H budget : Nat} {paths : Class} {value : Value Symbol Guard}
    {before after : Checked width} {memo saved : Memo} {answer : Bool}
    (actual : decision p h budget paths value before memo = .done answer after saved)
    (enoughP : p ≤ P) (enoughH : h ≤ H) :
    decision P H budget paths value before memo = .done answer after saved := by
  cases observed : SourceCurrentAllocatedConjunctionWorker.call p h budget value before memo with
  | done value state current =>
      simp only [decision, observed] at actual
      simp only [decision, SourceCurrentAllocatedConjunctionWorkerActual.call_done_stable observed enoughP enoughH]
      exact actual
  | failed => simp only [decision, observed] at actual; cases actual

/-- Larger stage bounds preserve every reached branch and the exact complete scan return. -/
theorem scan_done_stable {g s p h n G S P H N budget : Nat} {values : List (Value Symbol Guard)}
    {classes : Constraints} {before after : Checked width} {memo saved : Memo} {result : Result}
    (actual : scan g s p h n budget values classes before memo = .done result after saved)
    (enoughG : g ≤ G) (enoughS : s ≤ S) (enoughP : p ≤ P) (enoughH : h ≤ H) (enoughN : n ≤ N) :
    scan G S P H N budget values classes before memo = .done result after saved := by
  induction classes generalizing before memo result after saved with
  | nil => exact actual
  | cons paths classes ih =>
      obtain ⟨primary, middle, current, first, remaining⟩ := (bind_done_iff _ _ result after saved).mp actual
      simp only [scan, gate_done_stable first enoughG, Outcome.bind]
      cases primary with
      | false =>
          obtain ⟨rest, completed, returned⟩ := (select_done_iff paths _ result after saved).mp remaining
          apply (select_done_iff paths _ result after saved).mpr
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

/-- Successful bounds identify the stopped class, selected list, complete checked state, and fourth memo. -/
theorem scan_done_unique {g s p h n G S P H N budget : Nat} {values : List (Value Symbol Guard)}
    {classes : Constraints} {before after later : Checked width} {memo saved current : Memo} {first second : Result}
    (one : scan g s p h n budget values classes before memo = .done first after saved)
    (two : scan G S P H N budget values classes before memo = .done second later current) :
    first = second ∧ after = later ∧ saved = current := by
  have left := scan_done_stable one (Nat.le_max_left g G) (Nat.le_max_left s S)
    (Nat.le_max_left p P) (Nat.le_max_left h H) (Nat.le_max_left n N)
  have right := scan_done_stable two (Nat.le_max_right g G) (Nat.le_max_right s S)
    (Nat.le_max_right p P) (Nat.le_max_right h H) (Nat.le_max_right n N)
  exact Outcome.done.inj (left.symm.trans right)

end MicroCFTA.SourceCurrentAllocatedScanWorkerStability
