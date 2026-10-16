import MicroCFTA.SourceCurrentConjunctionWorker
import MicroCFTA.SourceCurrentConjunctionRowsWorkerStability

/-!
# Successful conjunction execution under larger lower-stage bounds

Projection and read bounds can increase after a literal success. The
algorithmic admission budget stays fixed. Ordered rows, returned physical
states, and completed memo entries remain exact. No heap or semantic
invariant is a premise of success preservation or uniqueness.
-/
namespace MicroCFTA.SourceCurrentConjunctionWorkerStability
open InternedConstructorTemplates
open SourceCurrentConjunctionWorker
open SourceCurrentConjunctionWorklist (closed)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Value Symbol Guard → Bool)

/-- More projection and read work preserves any successful complete worklist observation. -/
theorem explore_done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h largerP largerH budget : Nat} {table final : Table Symbol Formula}
    {pending : List (List (Value Symbol Guard))} {before after : Physical Symbol Formula}
    (actual : explore p h budget table pending before = .done final after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    explore largerP largerH budget table pending before = .done final after := by
  rw [explore.eq_def] at actual ⊢
  cases pending with
  | nil => exact actual
  | cons nodes rest =>
      cases impossible : nodes.any isEmpty with
      | true =>
          simp only [impossible, ite_true] at actual ⊢
          exact explore_done_stable actual enoughP enoughH
      | false =>
          simp only [impossible, Bool.false_eq_true, ite_false] at actual ⊢
          cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes with
          | true =>
              simp only [skipped, ite_true] at actual ⊢
              exact explore_done_stable actual enoughP enoughH
          | false =>
              simp only [skipped, Bool.false_eq_true, ite_false] at actual ⊢
              cases rows : SourceCurrentConjunctionRowsWorker.rows p h nodes before with
              | failed => simp only [rows] at actual; cases actual
              | done requirements middle =>
                  have stable := SourceCurrentConjunctionRowsWorkerStability.rows_done_stable rows enoughP enoughH
                  simp only [rows] at actual
                  simp only [stable]
                  exact explore_done_stable actual enoughP enoughH
termination_by (budget, pending.length)
decreasing_by
  all_goals first
    | apply Prod.Lex.right; simp_all
    | apply Prod.Lex.left
      have positive := (SourceCurrentConjunctionEmptinessTable.admitted SourceCurrentConjunctionRequirements.key
        SourceCurrentConjunctionWorklist.closed budget table nodes (by assumption)).1
      omega

/-- Larger lower-stage bounds preserve a successful decision and its full physical state. -/
theorem decision_done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {p h largerP largerH budget : Nat} {start : Value Symbol Guard} {before after : Physical Symbol Formula} {answer : Bool}
    (actual : decision p h budget start before = .done answer after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    decision largerP largerH budget start before = .done answer after := by
  cases admitted : closed start with
  | false => simpa only [decision, admitted, Bool.false_eq_true, ite_false] using actual
  | true =>
      cases explored : explore p h budget [] [[start]] before with
      | failed => simp only [decision, admitted, ite_true, explored, Outcome.bind] at actual; cases actual
      | done table current =>
          have stable := explore_done_stable explored enoughP enoughH
          simp only [decision, admitted, ite_true, explored, Outcome.bind] at actual
          simpa only [decision, admitted, ite_true, stable, Outcome.bind] using actual

/-- Two successful worklist bounds identify every stored row and both physical state components. -/
theorem explore_done_unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h otherP otherH budget : Nat} {table first second : Table Symbol Formula}
    {pending : List (List (Value Symbol Guard))} {before after later : Physical Symbol Formula}
    (one : explore p h budget table pending before = .done first after)
    (two : explore otherP otherH budget table pending before = .done second later) :
    first = second ∧ after = later := by
  have a := explore_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have b := explore_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  exact Outcome.done.inj (a.symm.trans b)

/-- Two successful decision bounds identify the Boolean and complete physical state. -/
theorem decision_done_unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {p h otherP otherH budget : Nat} {start : Value Symbol Guard} {before after later : Physical Symbol Formula}
    {first second : Bool}
    (one : decision p h budget start before = .done first after)
    (two : decision otherP otherH budget start before = .done second later) :
    first = second ∧ after = later := by
  have a := decision_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have b := decision_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  exact Outcome.done.inj (a.symm.trans b)

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

/-- Larger lower-stage bounds preserve completed hits and misses with the exact saved table. -/
theorem call_done_stable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq (Value ConcreteSymbol ConcreteGuard)]
    {p h largerP largerH budget : Nat} {memo saved : Memo} {query : Value ConcreteSymbol ConcreteGuard}
    {before after : Physical ConcreteSymbol FullSyntax.Formula} {answer : Bool}
    (actual : call p h budget memo query before = .done (answer, saved) after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    call largerP largerH budget memo query before = .done (answer, saved) after := by
  cases found : memo query.referenceOf with
  | some entry => obtain ⟨original, result⟩ := entry; simpa only [call, found] using actual
  | none =>
      cases done : decision p h budget query before with
      | failed => simp only [call, found, done, Outcome.bind] at actual; cases actual
      | done result current =>
          have stable := decision_done_stable done enoughP enoughH
          simp only [call, found, done, Outcome.bind] at actual
          simpa only [call, found, stable, Outcome.bind] using actual

/-- Successful calls at different bounds identify the answer, full state, and completed memo. -/
theorem call_done_unique [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq (Value ConcreteSymbol ConcreteGuard)]
    {p h otherP otherH budget : Nat} {memo saved current : Memo} {query : Value ConcreteSymbol ConcreteGuard}
    {before after later : Physical ConcreteSymbol FullSyntax.Formula} {first second : Bool}
    (one : call p h budget memo query before = .done (first, saved) after)
    (two : call otherP otherH budget memo query before = .done (second, current) later) :
    first = second ∧ after = later ∧ saved = current := by
  have a := call_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have b := call_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  have same := Outcome.done.inj (a.symm.trans b)
  exact ⟨congrArg Prod.fst same.1, same.2, congrArg Prod.snd same.1⟩

end MicroCFTA.SourceCurrentConjunctionWorkerStability
