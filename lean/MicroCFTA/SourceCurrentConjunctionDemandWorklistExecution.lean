import MicroCFTA.SourceCurrentConjunctionTupleWorkerCompletion
import MicroCFTA.SourceCurrentConjunctionDemandWorker
import MicroCFTA.SourceCurrentConjunctionDemandExecution

/-!
# Actual demand worklist execution graphs

The worklist uses the checked demand-admission graph. Its six branches
retain actual tables and physical states. A closed decision uses the final
table length for the fixed point. Fourth-memo hits skip the body. Successful
observations derive graphs, and every graph supplies stable source replay.
This active draft does not select a checked wrapper or alter eager APIs.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandWorklistExecution
open InternedConstructorTemplates
open SourceCurrentConjunctionWorker (Physical Table Outcome)
open SourceCurrentConjunctionWorklist (closed)
open SourceCurrentConjunctionDemandExecution (Admission admission_graph admission_complete)
open SourceCurrentConjunctionTupleWorkerCompletion (StableRun)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- The worklist records source skips and all three actual admission branches. -/
inductive Run : Nat → Table Symbol Formula → List (List Node) → Physical Symbol Formula →
    Table Symbol Formula → Physical Symbol Formula → Prop where
  | done : Run budget table [] state table state
  | empty (impossible : nodes.any isEmpty = true)
      (rest : Run budget table pending before final after) :
      Run budget table (nodes :: pending) before final after
  | skip (nonempty : nodes.any isEmpty = false)
      (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = true)
      (rest : Run budget table pending before final after) :
      Run budget table (nodes :: pending) before final after
  | overflow (nonempty : nodes.any isEmpty = false)
      (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
      (admission : Admission budget nodes before .overflow middle)
      (rest : Run 0 table pending middle final after) :
      Run budget table (nodes :: pending) before final after
  | zero (nonempty : nodes.any isEmpty = false)
      (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
      (admission : Admission budget nodes before .zero middle)
      (rest : Run budget (⟨nodes, []⟩ :: table) pending middle final after) :
      Run budget table (nodes :: pending) before final after
  | positive (nonempty : nodes.any isEmpty = false)
      (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
      (admission : Admission budget nodes before (.positive predecessor requirements) middle)
      (rest : Run (budget - (predecessor + 1)) (⟨nodes, requirements⟩ :: table)
        (requirements.flatten ++ pending) middle final after) :
      Run budget table (nodes :: pending) before final after

/-- A closed decision uses the completed table length for the actual fixed-point loop. -/
inductive Decision [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    (budget : Nat) (start : Node) : Physical Symbol Formula → Bool → Physical Symbol Formula → Prop where
  | open_input (isOpen : closed start = false) : Decision budget start before false before
  | closed (closedInput : closed start = true)
      (explored : Run budget [] [[start]] before table after)
      (grown : SourceCurrentConjunctionEmptinessTable.grow .empty key closed table (table.length + 1)
        (fun _ => false) = some known) :
      Decision budget start before (SourceCurrentConjunctionEmptinessTable.answer .empty key closed table known start) after

/-- Every successful literal worklist derives its actual six-branch graph. -/
theorem explore_graph {p h budget : Nat} {table final : Table Symbol Formula}
    {pending : List (List Node)} {before after : Physical Symbol Formula}
    (actual : SourceCurrentConjunctionDemandWorker.explore p h budget table pending before = .done final after) :
    Run budget table pending before final after := by
  induction budget using Nat.strongRecOn generalizing table pending before final after with
  | ind budget smaller =>
      induction pending generalizing table before with
      | nil =>
          rw [SourceCurrentConjunctionDemandWorker.explore_nil] at actual
          cases actual
          exact .done
      | cons nodes rest tail =>
          cases impossible : nodes.any isEmpty with
          | true =>
              rw [SourceCurrentConjunctionDemandWorker.explore_empty p h budget table nodes rest before impossible] at actual
              exact .empty impossible (tail actual)
          | false =>
              cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes with
              | true =>
                  rw [SourceCurrentConjunctionDemandWorker.explore_skip p h budget table nodes rest before impossible skipped] at actual
                  exact .skip impossible skipped (tail actual)
              | false =>
                  cases sampled : SourceCurrentConjunctionDemandAdmission.run p h budget nodes before with
                  | failed fault middle =>
                      rw [SourceCurrentConjunctionDemandWorker.explore_admission_failed p h budget table nodes rest before middle
                        fault impossible skipped sampled] at actual
                      cases actual
                  | done result middle =>
                      have admission := admission_graph sampled
                      cases result with
                      | overflow =>
                          have positive := (SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes skipped).1
                          rw [SourceCurrentConjunctionDemandWorker.explore_overflow p h budget table nodes rest before middle
                            impossible skipped sampled] at actual
                          exact .overflow impossible skipped admission (smaller 0 positive actual)
                      | zero =>
                          rw [SourceCurrentConjunctionDemandWorker.explore_zero p h budget table nodes rest before middle
                            impossible skipped sampled] at actual
                          exact .zero impossible skipped admission (tail actual)
                      | positive predecessor requirements =>
                          have charge := SourceCurrentConjunctionDemandAdmission.positive_charge p h budget nodes before middle
                            predecessor requirements sampled
                          rw [SourceCurrentConjunctionDemandWorker.explore_positive p h budget table nodes rest before middle
                            predecessor requirements impossible skipped sampled] at actual
                          exact .positive impossible skipped admission (smaller (budget - (predecessor + 1)) (by omega) actual)

/-- Every worklist graph supplies stable replay of all entries and both physical fields. -/
theorem explore_complete {budget : Nat} {table final : Table Symbol Formula} {pending : List (List Node)}
    {before after : Physical Symbol Formula} (actual : Run budget table pending before final after) :
    StableRun (fun p h => SourceCurrentConjunctionDemandWorker.explore p h budget table pending before) final after := by
  induction actual with
  | done => exact ⟨0, 0, by intros; exact SourceCurrentConjunctionDemandWorker.explore_nil _ _ _ _ _⟩
  | empty impossible _ ih =>
      obtain ⟨p, h, done⟩ := ih
      exact ⟨p, h, fun P H enoughP enoughH =>
        (SourceCurrentConjunctionDemandWorker.explore_empty P H _ _ _ _ _ impossible).trans
          (done P H enoughP enoughH)⟩
  | skip nonempty fresh _ ih =>
      obtain ⟨p, h, done⟩ := ih
      exact ⟨p, h, fun P H enoughP enoughH =>
        (SourceCurrentConjunctionDemandWorker.explore_skip P H _ _ _ _ _ nonempty fresh).trans
          (done P H enoughP enoughH)⟩
  | overflow nonempty fresh admission _ ih =>
      obtain ⟨p, h, first⟩ := admission_complete admission
      obtain ⟨laterP, laterH, done⟩ := ih
      exact ⟨max p laterP, max h laterH, fun P H enoughP enoughH =>
        (SourceCurrentConjunctionDemandWorker.explore_overflow P H _ _ _ _ _ _ nonempty fresh
          (first P H (by omega) (by omega))).trans (done P H (by omega) (by omega))⟩
  | zero nonempty fresh admission _ ih =>
      obtain ⟨p, h, first⟩ := admission_complete admission
      obtain ⟨laterP, laterH, done⟩ := ih
      exact ⟨max p laterP, max h laterH, fun P H enoughP enoughH =>
        (SourceCurrentConjunctionDemandWorker.explore_zero P H _ _ _ _ _ _ nonempty fresh
          (first P H (by omega) (by omega))).trans (done P H (by omega) (by omega))⟩
  | positive nonempty fresh admission _ ih =>
      obtain ⟨p, h, first⟩ := admission_complete admission
      obtain ⟨laterP, laterH, done⟩ := ih
      exact ⟨max p laterP, max h laterH, fun P H enoughP enoughH =>
        (SourceCurrentConjunctionDemandWorker.explore_positive P H _ _ _ _ _ _ _ _ nonempty fresh
          (first P H (by omega) (by omega))).trans (done P H (by omega) (by omega))⟩

/-- Every successful literal decision derives its open shortcut or actual table and fixed point. -/
theorem decision_graph [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    {p h budget : Nat} {start : Node} {before after : Physical Symbol Formula} {answer : Bool}
    (actual : SourceCurrentConjunctionDemandWorker.decision p h budget start before = .done answer after) :
    Decision budget start before answer after := by
  cases admitted : closed start with
  | false =>
      simp only [SourceCurrentConjunctionDemandWorker.decision, admitted, Bool.false_eq_true, ite_false] at actual
      cases actual
      exact .open_input admitted
  | true =>
      cases explored : SourceCurrentConjunctionDemandWorker.explore p h budget [] [[start]] before with
      | failed =>
          simp only [SourceCurrentConjunctionDemandWorker.decision, admitted, ite_true, explored, Outcome.bind] at actual
          cases actual
      | done table current =>
          simp only [SourceCurrentConjunctionDemandWorker.decision, admitted, ite_true, explored, Outcome.bind] at actual
          cases grown : SourceCurrentConjunctionEmptinessTable.grow .empty key closed table (table.length + 1)
              (fun _ => false) with
          | none => simp only [grown] at actual; cases actual
          | some known =>
              simp only [grown] at actual
              cases actual
              exact .closed admitted (explore_graph explored) grown

/-- Every decision graph supplies stable replay with its exact returned Boolean and state. -/
theorem decision_complete [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    {budget : Nat} {start : Node} {before after : Physical Symbol Formula} {answer : Bool}
    (actual : Decision budget start before answer after) :
    StableRun (fun p h => SourceCurrentConjunctionDemandWorker.decision p h budget start before) answer after := by
  cases actual with
  | open_input isOpen =>
      exact ⟨0, 0, by intros; exact SourceCurrentConjunctionDemandWorker.decision_open _ _ _ _ _ isOpen⟩
  | closed closedInput explored grown =>
      obtain ⟨p, h, done⟩ := explore_complete explored
      exact ⟨p, h, fun P H enoughP enoughH =>
        SourceCurrentConjunctionDemandWorker.decision_closed_done P H _ _ _ _ _ _ closedInput
          (done P H enoughP enoughH) grown⟩

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

/-- Fourth-memo hits retain the input state. Only completed misses install an answer. -/
inductive Call [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (budget : Nat) : Memo → ConcreteNode → Physical ConcreteSymbol FullSyntax.Formula →
      Bool → Physical ConcreteSymbol FullSyntax.Formula → Memo → Prop where
  | hit (found : memo query.referenceOf = some (original, answer)) :
      Call budget memo query before answer before memo
  | miss (absent : memo query.referenceOf = none)
      (actual : Decision budget query before answer after) :
      Call budget memo query before answer after (SourceCurrentEmptinessMemo.insert memo query answer)

/-- Every successful literal fourth-memo call derives its exact hit or tuple-decision graph. -/
theorem call_graph [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] {p h budget : Nat} {memo saved : Memo} {query : ConcreteNode}
    {before after : Physical ConcreteSymbol FullSyntax.Formula} {answer : Bool}
    (actual : SourceCurrentConjunctionDemandWorker.call p h budget memo query before = .done (answer, saved) after) :
    Call budget memo query before answer after saved := by
  cases found : memo query.referenceOf with
  | some entry =>
      obtain ⟨original, result⟩ := entry
      simp only [SourceCurrentConjunctionDemandWorker.call, found] at actual
      cases actual
      exact .hit found
  | none =>
      cases done : SourceCurrentConjunctionDemandWorker.decision p h budget query before with
      | failed =>
          simp only [SourceCurrentConjunctionDemandWorker.call, found, done, Outcome.bind] at actual
          cases actual
      | done result current =>
          simp only [SourceCurrentConjunctionDemandWorker.call, found, done, Outcome.bind] at actual
          cases actual
          exact .miss found (decision_graph done)

/-- Every call graph supplies stable replay of its full physical state and fourth memo. -/
theorem call_complete [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] {budget : Nat} {memo saved : Memo} {query : ConcreteNode}
    {before after : Physical ConcreteSymbol FullSyntax.Formula} {answer : Bool}
    (actual : Call budget memo query before answer after saved) :
    StableRun (fun p h => SourceCurrentConjunctionDemandWorker.call p h budget memo query before) (answer, saved) after := by
  cases actual with
  | hit found => exact ⟨0, 0, by intros; simp only [SourceCurrentConjunctionDemandWorker.call, found]⟩
  | miss absent actual =>
      obtain ⟨p, h, done⟩ := decision_complete actual
      exact ⟨p, h, fun P H enoughP enoughH => by
        simp only [SourceCurrentConjunctionDemandWorker.call, absent, done P H enoughP enoughH, Outcome.bind]⟩

end MicroCFTA.SourceCurrentConjunctionDemandWorklistExecution
