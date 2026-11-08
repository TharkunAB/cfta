import MicroCFTA.SourceCurrentConjunctionDemandWorker
import MicroCFTA.SourceCurrentConjunctionRowsWorkerStability
import MicroCFTA.SourceCurrentConjunctionTuplePullStability

/-!
# Successful physical tuple execution at larger lower-stage bounds

Every successful actual demand sample retains its tuples and physical state.
The same sample then selects the same admission branch. Positive admission retains
its actual tuple rows and equality allocations. The algorithmic tuple budget
stays fixed. These laws require no readiness or future completion premise.
They do not identify tuple execution with the earlier admission-counted run.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandWorkerStability
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
    (actual : SourceCurrentConjunctionDemandAdmission.run p h budget nodes before = .done result after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    SourceCurrentConjunctionDemandAdmission.run largerP largerH budget nodes before = .done result after := by
  cases read : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before with
  | failed fault exposed =>
      simp only [SourceCurrentConjunctionDemandAdmission.run, read,
        SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual
      cases actual
  | done sampled exposed =>
      have stable := SourceCurrentConjunctionTuplePullStability.sample_done_stable read enoughH
      simp only [SourceCurrentConjunctionDemandAdmission.run, read, stable,
        SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual ⊢
      cases sampled with
      | overflow tuples cursor => exact actual
      | fit tuples =>
          cases tuples with
          | nil => exact actual
          | cons first rest =>
              cases processed : SourceCurrentConjunctionRowsWorker.tuples p h (first :: rest) exposed with
              | failed fault middle =>
                  simp only [processed] at actual
                  cases actual
              | done rows middle =>
                  have retained := SourceCurrentConjunctionRowsWorkerStability.tuples_done_stable
                    processed enoughP enoughH
                  simp only [processed] at actual
                  simpa only [retained, SourceCurrentConjunctionRowsWorker.Outcome.bind] using actual

/-- Different successful admission bounds identify the branch, rows, and physical state. -/
theorem admission_done_unique {p h otherP otherH budget : Nat} {nodes : List Node}
    {before after later : Physical Symbol Formula}
    {first second : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (one : SourceCurrentConjunctionDemandAdmission.run p h budget nodes before = .done first after)
    (two : SourceCurrentConjunctionDemandAdmission.run otherP otherH budget nodes before = .done second later) :
    first = second ∧ after = later := by
  have a := admission_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have b := admission_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  exact SourceCurrentConjunctionRowsWorker.Outcome.done.inj (a.symm.trans b)

/-- Larger lower-stage bounds retain every successful complete tuple worklist. -/
theorem explore_done_stable {p h largerP largerH budget : Nat}
    {table final : Table Symbol Formula} {pending : List (List Node)} {before after : Physical Symbol Formula}
    (actual : SourceCurrentConjunctionDemandWorker.explore p h budget table pending before = .done final after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    SourceCurrentConjunctionDemandWorker.explore largerP largerH budget table pending before = .done final after := by
  induction budget using Nat.strongRecOn generalizing table pending before final after with
  | ind budget smaller =>
      induction pending generalizing table before with
      | nil => simpa only [SourceCurrentConjunctionDemandWorker.explore_nil] using actual
      | cons nodes rest tail =>
          cases impossible : nodes.any isEmpty with
          | true =>
              rw [SourceCurrentConjunctionDemandWorker.explore_empty p h budget table nodes rest before impossible] at actual
              rw [SourceCurrentConjunctionDemandWorker.explore_empty largerP largerH budget table nodes rest before impossible]
              exact tail actual
          | false =>
              cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes with
              | true =>
                  rw [SourceCurrentConjunctionDemandWorker.explore_skip p h budget table nodes rest before impossible skipped] at actual
                  rw [SourceCurrentConjunctionDemandWorker.explore_skip largerP largerH budget table nodes rest before impossible skipped]
                  exact tail actual
              | false =>
                  cases sampled : SourceCurrentConjunctionDemandAdmission.run p h budget nodes before with
                  | failed fault middle =>
                      rw [SourceCurrentConjunctionDemandWorker.explore_admission_failed p h budget table nodes rest before middle
                        fault impossible skipped sampled] at actual
                      cases actual
                  | done result middle =>
                      have stable := admission_done_stable sampled enoughP enoughH
                      cases result with
                      | overflow =>
                          have positive := (SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes skipped).1
                          rw [SourceCurrentConjunctionDemandWorker.explore_overflow p h budget table nodes rest before middle
                            impossible skipped sampled] at actual
                          rw [SourceCurrentConjunctionDemandWorker.explore_overflow largerP largerH budget table nodes rest before middle
                            impossible skipped stable]
                          exact smaller 0 positive actual
                      | zero =>
                          rw [SourceCurrentConjunctionDemandWorker.explore_zero p h budget table nodes rest before middle
                            impossible skipped sampled] at actual
                          rw [SourceCurrentConjunctionDemandWorker.explore_zero largerP largerH budget table nodes rest before middle
                            impossible skipped stable]
                          exact tail actual
                      | positive predecessor requirements =>
                          have charge := SourceCurrentConjunctionDemandAdmission.positive_charge p h budget nodes before middle
                            predecessor requirements sampled
                          rw [SourceCurrentConjunctionDemandWorker.explore_positive p h budget table nodes rest before middle
                            predecessor requirements impossible skipped sampled] at actual
                          rw [SourceCurrentConjunctionDemandWorker.explore_positive largerP largerH budget table nodes rest before middle
                            predecessor requirements impossible skipped stable]
                          exact smaller (budget - (predecessor + 1)) (by omega) actual

/-- Different successful worklist bounds identify every returned entry and both physical fields. -/
theorem explore_done_unique {p h otherP otherH budget : Nat} {table first second : Table Symbol Formula}
    {pending : List (List Node)} {before after later : Physical Symbol Formula}
    (one : SourceCurrentConjunctionDemandWorker.explore p h budget table pending before = .done first after)
    (two : SourceCurrentConjunctionDemandWorker.explore otherP otherH budget table pending before = .done second later) :
    first = second ∧ after = later := by
  have a := explore_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have b := explore_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  exact Outcome.done.inj (a.symm.trans b)

/-- Larger lower-stage bounds retain the exact completed Boolean decision and physical state. -/
theorem decision_done_stable [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    {p h largerP largerH budget : Nat} {start : Node} {before after : Physical Symbol Formula} {answer : Bool}
    (actual : SourceCurrentConjunctionDemandWorker.decision p h budget start before = .done answer after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    SourceCurrentConjunctionDemandWorker.decision largerP largerH budget start before = .done answer after := by
  cases admitted : closed start with
  | false => simpa only [SourceCurrentConjunctionDemandWorker.decision, admitted, Bool.false_eq_true, ite_false] using actual
  | true =>
      cases explored : SourceCurrentConjunctionDemandWorker.explore p h budget [] [[start]] before with
      | failed =>
          simp only [SourceCurrentConjunctionDemandWorker.decision, admitted, ite_true, explored, Outcome.bind] at actual
          cases actual
      | done table current =>
          have stable := explore_done_stable explored enoughP enoughH
          simp only [SourceCurrentConjunctionDemandWorker.decision, admitted, ite_true, explored, Outcome.bind] at actual
          simpa only [SourceCurrentConjunctionDemandWorker.decision, admitted, ite_true, stable, Outcome.bind] using actual

/-- Different successful decision bounds identify the Boolean and complete physical state. -/
theorem decision_done_unique [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    {p h otherP otherH budget : Nat} {start : Node} {before after later : Physical Symbol Formula} {first second : Bool}
    (one : SourceCurrentConjunctionDemandWorker.decision p h budget start before = .done first after)
    (two : SourceCurrentConjunctionDemandWorker.decision otherP otherH budget start before = .done second later) :
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
    (actual : SourceCurrentConjunctionDemandWorker.call p h budget memo query before = .done (answer, saved) after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    SourceCurrentConjunctionDemandWorker.call largerP largerH budget memo query before = .done (answer, saved) after := by
  cases found : memo query.referenceOf with
  | some entry =>
      obtain ⟨original, result⟩ := entry
      simpa only [SourceCurrentConjunctionDemandWorker.call, found] using actual
  | none =>
      cases done : SourceCurrentConjunctionDemandWorker.decision p h budget query before with
      | failed =>
          simp only [SourceCurrentConjunctionDemandWorker.call, found, done, Outcome.bind] at actual
          cases actual
      | done result current =>
          have stable := decision_done_stable done enoughP enoughH
          simp only [SourceCurrentConjunctionDemandWorker.call, found, done, Outcome.bind] at actual
          simpa only [SourceCurrentConjunctionDemandWorker.call, found, stable, Outcome.bind] using actual

/-- Different successful call bounds identify the answer, physical state, and completed fourth memo. -/
theorem call_done_unique [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] {p h otherP otherH budget : Nat} {memo saved current : Memo} {query : ConcreteNode}
    {before after later : Physical ConcreteSymbol FullSyntax.Formula} {first second : Bool}
    (one : SourceCurrentConjunctionDemandWorker.call p h budget memo query before = .done (first, saved) after)
    (two : SourceCurrentConjunctionDemandWorker.call otherP otherH budget memo query before = .done (second, current) later) :
    first = second ∧ after = later ∧ saved = current := by
  have a := call_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have b := call_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  have same := Outcome.done.inj (a.symm.trans b)
  exact ⟨congrArg Prod.fst same.1, same.2, congrArg Prod.snd same.1⟩

end MicroCFTA.SourceCurrentConjunctionDemandWorkerStability
