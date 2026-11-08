import MicroCFTA.SourceCurrentConjunctionTupleWorker
import MicroCFTA.SourceCurrentConjunctionRowsWorkerStability

/-!
# Successful physical tuple execution at larger lower-stage bounds

Every successful exposure retains its rows and physical state. The same raw
sample then selects the same admission branch. Positive admission retains
its actual tuple rows and equality allocations. The algorithmic tuple budget
stays fixed. These laws require no readiness or future completion premise.
They do not identify tuple execution with the earlier admission-counted run.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleWorkerStability
open InternedConstructorTemplates
open SourceCurrentConjunctionWorker (Physical Table Outcome)
open SourceCurrentConjunctionWorklist (closed)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Larger lower-stage bounds retain every successful raw-tuple admission. -/
theorem admission_done_stable {p h largerP largerH budget : Nat} {nodes : List Node}
    {before after : Physical Symbol Formula} {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before = .done result after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    SourceCurrentConjunctionTupleAdmission.run largerP largerH budget nodes before = .done result after := by
  cases read : SourceCurrentConjunctionRowsWorker.exposures h nodes before with
  | failed fault exposed =>
      simp only [SourceCurrentConjunctionTupleAdmission.run, read,
        SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual
      cases actual
  | done edges exposed =>
      have stable := SourceCurrentConjunctionRowsWorkerStability.exposures_done_stable read enoughH
      simp only [SourceCurrentConjunctionTupleAdmission.run, read, stable,
        SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual ⊢
      by_cases overflow : budget < (SourceCurrentConjunctionTupleBudget.sample budget
          (SourceCurrentConjunctionTuples.tuples edges)).length
      · simpa only [overflow, ↓reduceIte] using actual
      · simp only [overflow, ↓reduceIte] at actual ⊢
        cases sampled : SourceCurrentConjunctionTupleBudget.sample budget
            (SourceCurrentConjunctionTuples.tuples edges) with
        | nil => simpa only [sampled] using actual
        | cons first rest =>
            simp only [sampled] at actual ⊢
            cases processed : SourceCurrentConjunctionRowsWorker.tuples p h (first :: rest) exposed with
            | failed fault middle =>
                simp only [processed] at actual
                cases actual
            | done rows middle =>
                have retained := SourceCurrentConjunctionRowsWorkerStability.tuples_done_stable
                  processed enoughP enoughH
                simp only [processed] at actual
                simpa only [retained] using actual

/-- Different successful admission bounds identify the branch, rows, and physical state. -/
theorem admission_done_unique {p h otherP otherH budget : Nat} {nodes : List Node}
    {before after later : Physical Symbol Formula}
    {first second : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (one : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before = .done first after)
    (two : SourceCurrentConjunctionTupleAdmission.run otherP otherH budget nodes before = .done second later) :
    first = second ∧ after = later := by
  have a := admission_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have b := admission_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  exact SourceCurrentConjunctionRowsWorker.Outcome.done.inj (a.symm.trans b)

/-- Larger lower-stage bounds retain every successful complete tuple worklist. -/
theorem explore_done_stable {p h largerP largerH budget : Nat}
    {table final : Table Symbol Formula} {pending : List (List Node)} {before after : Physical Symbol Formula}
    (actual : SourceCurrentConjunctionTupleWorker.explore p h budget table pending before = .done final after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    SourceCurrentConjunctionTupleWorker.explore largerP largerH budget table pending before = .done final after := by
  induction budget using Nat.strongRecOn generalizing table pending before final after with
  | ind budget smaller =>
      induction pending generalizing table before with
      | nil => simpa only [SourceCurrentConjunctionTupleWorker.explore_nil] using actual
      | cons nodes rest tail =>
          cases impossible : nodes.any isEmpty with
          | true =>
              rw [SourceCurrentConjunctionTupleWorker.explore_empty p h budget table nodes rest before impossible] at actual
              rw [SourceCurrentConjunctionTupleWorker.explore_empty largerP largerH budget table nodes rest before impossible]
              exact tail actual
          | false =>
              cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes with
              | true =>
                  rw [SourceCurrentConjunctionTupleWorker.explore_skip p h budget table nodes rest before impossible skipped] at actual
                  rw [SourceCurrentConjunctionTupleWorker.explore_skip largerP largerH budget table nodes rest before impossible skipped]
                  exact tail actual
              | false =>
                  cases sampled : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before with
                  | failed fault middle =>
                      rw [SourceCurrentConjunctionTupleWorker.explore_admission_failed p h budget table nodes rest before middle
                        fault impossible skipped sampled] at actual
                      cases actual
                  | done result middle =>
                      have stable := admission_done_stable sampled enoughP enoughH
                      cases result with
                      | overflow =>
                          have positive := (SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes skipped).1
                          rw [SourceCurrentConjunctionTupleWorker.explore_overflow p h budget table nodes rest before middle
                            impossible skipped sampled] at actual
                          rw [SourceCurrentConjunctionTupleWorker.explore_overflow largerP largerH budget table nodes rest before middle
                            impossible skipped stable]
                          exact smaller 0 positive actual
                      | zero =>
                          rw [SourceCurrentConjunctionTupleWorker.explore_zero p h budget table nodes rest before middle
                            impossible skipped sampled] at actual
                          rw [SourceCurrentConjunctionTupleWorker.explore_zero largerP largerH budget table nodes rest before middle
                            impossible skipped stable]
                          exact tail actual
                      | positive predecessor requirements =>
                          have charge := SourceCurrentConjunctionTupleAdmission.positive_charge p h budget nodes before middle
                            predecessor requirements sampled
                          rw [SourceCurrentConjunctionTupleWorker.explore_positive p h budget table nodes rest before middle
                            predecessor requirements impossible skipped sampled] at actual
                          rw [SourceCurrentConjunctionTupleWorker.explore_positive largerP largerH budget table nodes rest before middle
                            predecessor requirements impossible skipped stable]
                          exact smaller (budget - (predecessor + 1)) (by omega) actual

/-- Different successful worklist bounds identify every returned entry and both physical fields. -/
theorem explore_done_unique {p h otherP otherH budget : Nat} {table first second : Table Symbol Formula}
    {pending : List (List Node)} {before after later : Physical Symbol Formula}
    (one : SourceCurrentConjunctionTupleWorker.explore p h budget table pending before = .done first after)
    (two : SourceCurrentConjunctionTupleWorker.explore otherP otherH budget table pending before = .done second later) :
    first = second ∧ after = later := by
  have a := explore_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have b := explore_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  exact Outcome.done.inj (a.symm.trans b)

/-- Larger lower-stage bounds retain the exact completed Boolean decision and physical state. -/
theorem decision_done_stable [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    {p h largerP largerH budget : Nat} {start : Node} {before after : Physical Symbol Formula} {answer : Bool}
    (actual : SourceCurrentConjunctionTupleWorker.decision p h budget start before = .done answer after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    SourceCurrentConjunctionTupleWorker.decision largerP largerH budget start before = .done answer after := by
  cases admitted : closed start with
  | false => simpa only [SourceCurrentConjunctionTupleWorker.decision, admitted, Bool.false_eq_true, ite_false] using actual
  | true =>
      cases explored : SourceCurrentConjunctionTupleWorker.explore p h budget [] [[start]] before with
      | failed =>
          simp only [SourceCurrentConjunctionTupleWorker.decision, admitted, ite_true, explored, Outcome.bind] at actual
          cases actual
      | done table current =>
          have stable := explore_done_stable explored enoughP enoughH
          simp only [SourceCurrentConjunctionTupleWorker.decision, admitted, ite_true, explored, Outcome.bind] at actual
          simpa only [SourceCurrentConjunctionTupleWorker.decision, admitted, ite_true, stable, Outcome.bind] using actual

/-- Different successful decision bounds identify the Boolean and complete physical state. -/
theorem decision_done_unique [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    {p h otherP otherH budget : Nat} {start : Node} {before after later : Physical Symbol Formula} {first second : Bool}
    (one : SourceCurrentConjunctionTupleWorker.decision p h budget start before = .done first after)
    (two : SourceCurrentConjunctionTupleWorker.decision otherP otherH budget start before = .done second later) :
    first = second ∧ after = later := by
  have a := decision_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have b := decision_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  exact Outcome.done.inj (a.symm.trans b)

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

/-- Larger lower-stage bounds retain completed hits and misses with the entire saved fourth memo. -/
theorem call_done_stable [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] {p h largerP largerH budget : Nat} {memo saved : Memo} {query : ConcreteNode}
    {before after : Physical ConcreteSymbol FullSyntax.Formula} {answer : Bool}
    (actual : SourceCurrentConjunctionTupleWorker.call p h budget memo query before = .done (answer, saved) after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    SourceCurrentConjunctionTupleWorker.call largerP largerH budget memo query before = .done (answer, saved) after := by
  cases found : memo query.referenceOf with
  | some entry =>
      obtain ⟨original, result⟩ := entry
      simpa only [SourceCurrentConjunctionTupleWorker.call, found] using actual
  | none =>
      cases done : SourceCurrentConjunctionTupleWorker.decision p h budget query before with
      | failed =>
          simp only [SourceCurrentConjunctionTupleWorker.call, found, done, Outcome.bind] at actual
          cases actual
      | done result current =>
          have stable := decision_done_stable done enoughP enoughH
          simp only [SourceCurrentConjunctionTupleWorker.call, found, done, Outcome.bind] at actual
          simpa only [SourceCurrentConjunctionTupleWorker.call, found, stable, Outcome.bind] using actual

/-- Different successful call bounds identify the answer, physical state, and completed fourth memo. -/
theorem call_done_unique [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] {p h otherP otherH budget : Nat} {memo saved current : Memo} {query : ConcreteNode}
    {before after later : Physical ConcreteSymbol FullSyntax.Formula} {first second : Bool}
    (one : SourceCurrentConjunctionTupleWorker.call p h budget memo query before = .done (first, saved) after)
    (two : SourceCurrentConjunctionTupleWorker.call otherP otherH budget memo query before = .done (second, current) later) :
    first = second ∧ after = later ∧ saved = current := by
  have a := call_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have b := call_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  have same := Outcome.done.inj (a.symm.trans b)
  exact ⟨congrArg Prod.fst same.1, same.2, congrArg Prod.snd same.1⟩

end MicroCFTA.SourceCurrentConjunctionTupleWorkerStability
