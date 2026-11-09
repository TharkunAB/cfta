import MicroCFTA.SourceCurrentConjunctionSharedWorker
import MicroCFTA.SourceCurrentConjunctionSharedWorklistStability
import MicroCFTA.SourceCurrentConjunctionSharedWorklistReadExtensionality

/-!
# Exact successful shared calls at larger observation bounds

Larger bounds retain the same answer, complete private state and fourth memo.
Cached table reads use valid certificates for each actual execution. The
certificates need not be equal. These replay laws derive no sufficient bound
and require no readiness, costs or future completion premise.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerStability
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentConjunctionSharedWorker (Outcome)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Every successful decision retains its answer and complete private state at larger bounds. -/
theorem decision_done_stable {p h largerP largerH budget : Nat} {start : Node}
    {before : Physical} {after : WorkState} {answer : Bool}
    (actual : SourceCurrentConjunctionSharedWorker.decision p h budget start before = .done answer after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    SourceCurrentConjunctionSharedWorker.decision largerP largerH budget start before = .done answer after := by
  cases closed : SourceCurrentConjunctionWorklist.closed start with
  | false =>
      simpa only [SourceCurrentConjunctionSharedWorker.decision, closed, Bool.false_eq_true, ite_false] using actual
  | true =>
      cases explored : SourceCurrentConjunctionSharedWorklistRun.explore p h budget start before with
      | failed fault current =>
          simp only [SourceCurrentConjunctionSharedWorker.decision, closed, ite_true, explored] at actual
          cases actual
      | done event current =>
          have replayed := SourceCurrentConjunctionSharedWorklistStability.explore_done_stable
            explored enoughP enoughH
          have firstValid := SourceCurrentConjunctionSharedWorker.endpointCredits_valid p h budget start before
          have secondValid := SourceCurrentConjunctionSharedWorker.endpointCredits_valid largerP largerH budget start before
          rw [explored] at firstValid
          rw [replayed] at secondValid
          have same := SourceCurrentConjunctionSharedWorklistReadExtensionality.readTable_credit_eq
            (SourceCurrentConjunctionSharedWorker.endpointCredits p h budget start before)
            (SourceCurrentConjunctionSharedWorker.endpointCredits largerP largerH budget start before)
            current firstValid secondValid
          simp only [SourceCurrentConjunctionSharedWorker.decision, closed, ite_true, explored] at actual
          simp only [SourceCurrentConjunctionSharedWorker.decision, closed, ite_true, replayed]
          rw [← same]
          exact actual

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsWorker.Physical ConcreteSymbol FullSyntax.Formula
local notation "ConcreteState" => SourceCurrentConjunctionSharedWorklistStep.State ConcreteSymbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

/-- Every successful hit or miss retains its answer, entire state and fourth memo. -/
theorem call_done_stable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] {p h largerP largerH budget : Nat} {memo saved : Memo} {query : ConcreteNode}
    {before : ConcretePhysical} {after : ConcreteState} {answer : Bool}
    (actual : SourceCurrentConjunctionSharedWorker.call p h budget memo query before = .done (answer, saved) after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    SourceCurrentConjunctionSharedWorker.call largerP largerH budget memo query before = .done (answer, saved) after := by
  cases found : memo query.referenceOf with
  | some entry =>
      obtain ⟨original, result⟩ := entry
      simpa only [SourceCurrentConjunctionSharedWorker.call, found] using actual
  | none =>
      cases done : SourceCurrentConjunctionSharedWorker.decision p h budget query before with
      | failed fault current =>
          simp only [SourceCurrentConjunctionSharedWorker.call, found, done, Outcome.bind] at actual
          cases actual
      | done result current =>
          have stable := decision_done_stable done enoughP enoughH
          simp only [SourceCurrentConjunctionSharedWorker.call, found, done, Outcome.bind] at actual
          simpa only [SourceCurrentConjunctionSharedWorker.call, found, stable, Outcome.bind] using actual

/-- Any two successful call observations identify answer, private endpoint and completed memo. -/
theorem call_done_unique [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] {p h otherP otherH budget : Nat} {memo saved current : Memo} {query : ConcreteNode}
    {before : ConcretePhysical} {after later : ConcreteState} {first second : Bool}
    (one : SourceCurrentConjunctionSharedWorker.call p h budget memo query before = .done (first, saved) after)
    (two : SourceCurrentConjunctionSharedWorker.call otherP otherH budget memo query before = .done (second, current) later) :
    first = second ∧ after = later ∧ saved = current := by
  have a := call_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have b := call_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  have same := Outcome.done.inj (a.symm.trans b)
  exact ⟨congrArg Prod.fst same.1, same.2, congrArg Prod.snd same.1⟩

end MicroCFTA.SourceCurrentConjunctionSharedWorkerStability
