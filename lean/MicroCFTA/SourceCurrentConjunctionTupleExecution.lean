import MicroCFTA.SourceCurrentConjunctionTupleWorkerCompletion
import MicroCFTA.SourceCurrentConjunctionRowsWorkerActual

/-!
# Actual physical tuple-budget execution graphs

Admission records the actual ordered exposures. Overflow returns that state
before equality allocation. Zero admission records an empty full tuple list.
Positive admission records the full tuple count and allocated tuple rows.
Worklist, decision, and fourth-memo graphs retain exact physical states.
Successful execution derives these graphs. Each graph supplies stable replay.
The eager read schedule does not establish native lazy demand or runtime cost.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleExecution
open InternedConstructorTemplates
open SourceCurrentConjunctionWorker (Physical Table Outcome)
open SourceCurrentConjunctionWorklist (closed)
open SourceCurrentConjunctionRowsAllocation (Rows Tuples)
open SourceCurrentConjunctionCompletionReads (Exposures)
open SourceCurrentConjunctionTupleWorkerCompletion (StableRun)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Admission records actual reads, the full raw charge, and the exact returned state. -/
inductive Admission : Nat → List Node → Physical Symbol Formula →
    SourceCurrentConjunctionTupleAdmission.Result Symbol Formula → Physical Symbol Formula → Prop where
  | overflow {budget : Nat} {nodes : List Node} {before : Physical Symbol Formula}
      {edges : List (List Edge)} {heap : InternedConstructorTemplates.State Symbol Guard}
      (exposed : Exposures nodes before.heap edges heap)
      (tooMany : budget < (SourceCurrentConjunctionTupleBudget.sample budget
        (SourceCurrentConjunctionTuples.tuples edges)).length) :
      Admission budget nodes before .overflow ⟨heap, before.equality⟩
  | zero {budget : Nat} {nodes : List Node} {before : Physical Symbol Formula}
      {edges : List (List Edge)} {heap : InternedConstructorTemplates.State Symbol Guard}
      (exposed : Exposures nodes before.heap edges heap)
      (noTuples : SourceCurrentConjunctionTuples.tuples edges = []) :
      Admission budget nodes before .zero ⟨heap, before.equality⟩
  | positive {budget predecessor : Nat} {nodes : List Node} {before after : Physical Symbol Formula}
      {edges : List (List Edge)} {heap : InternedConstructorTemplates.State Symbol Guard}
      {requirements : List (List (List Node))}
      (exposed : Exposures nodes before.heap edges heap)
      (count : (SourceCurrentConjunctionTuples.tuples edges).length = predecessor + 1)
      (fits : predecessor + 1 ≤ budget)
      (allocated : Tuples (SourceCurrentConjunctionTuples.tuples edges)
        ⟨heap, before.equality⟩ requirements after) :
      Admission budget nodes before (.positive predecessor requirements) after

/-- Positive admission supplies its full row graph and its actual charge bound. -/
theorem Admission.positive_rows {budget predecessor : Nat} {nodes : List Node}
    {before after : Physical Symbol Formula} {requirements : List (List (List Node))}
    (actual : Admission budget nodes before (.positive predecessor requirements) after) :
    predecessor + 1 ≤ budget ∧ Rows nodes before requirements after := by
  cases actual with
  | positive exposed _ fits allocated => exact ⟨fits, .run exposed allocated⟩

/-- Zero admission supplies the complete empty row graph. -/
theorem Admission.zero_rows {budget : Nat} {nodes : List Node} {before after : Physical Symbol Formula}
    (actual : Admission budget nodes before .zero after) : Rows nodes before [] after := by
  cases actual with
  | zero exposed noTuples =>
      apply Rows.run exposed
      rw [noTuples]
      exact .nil

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

/-- An actual successful admission derives its exposure and complete tuple graph. -/
theorem admission_graph {p h budget : Nat} {nodes : List Node} {before after : Physical Symbol Formula}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before = .done result after) :
    Admission budget nodes before result after := by
  cases read : SourceCurrentConjunctionRowsWorker.exposures h nodes before with
  | failed fault middle =>
      simp only [SourceCurrentConjunctionTupleAdmission.run, read,
        SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual
      cases actual
  | done edges middle =>
      rcases middle with ⟨heap, operations⟩
      have exposed := SourceCurrentConjunctionRowsWorkerActual.exposures_graph read
      have unchanged : operations = before.equality := exposed.2
      subst operations
      simp only [SourceCurrentConjunctionTupleAdmission.run, read,
        SourceCurrentConjunctionRowsWorker.Outcome.bind] at actual
      split at actual
      · rename_i overflow
        cases actual
        exact .overflow exposed.1 overflow
      · rename_i fits
        have within := Nat.le_of_not_gt fits
        have entire := SourceCurrentConjunctionTupleBudget.sample_eq_of_fits budget
          (SourceCurrentConjunctionTuples.tuples edges) within
        cases sampled : SourceCurrentConjunctionTupleBudget.sample budget
            (SourceCurrentConjunctionTuples.tuples edges) with
        | nil =>
            simp only [sampled] at actual
            cases actual
            exact .zero exposed.1 (entire.symm.trans sampled)
        | cons first rest =>
            simp only [sampled] at actual
            cases processed : SourceCurrentConjunctionRowsWorker.tuples p h (first :: rest)
                ⟨heap, before.equality⟩ with
            | failed fault middle => simp only [processed] at actual; cases actual
            | done requirements final =>
                simp only [processed] at actual
                cases actual
                have full : SourceCurrentConjunctionTuples.tuples edges = first :: rest := entire.symm.trans sampled
                have complete : SourceCurrentConjunctionRowsWorker.tuples p h
                    (SourceCurrentConjunctionTuples.tuples edges) ⟨heap, before.equality⟩ = .done requirements after := by
                  simpa only [full] using processed
                refine .positive exposed.1 ?_ ?_
                  (SourceCurrentConjunctionRowsWorkerActual.tuples_graph
                    (fun tuple member => SourceCurrentConjunctionRowsAllocation.matching_arity tuple
                      (SourceCurrentConjunctionTuples.tuples_matching edges tuple member)) complete)
                · simp only [full, List.length_cons]
                · simpa only [sampled, List.length_cons] using within

/-- Every admission graph supplies stable replay at its exact returned physical state. -/
theorem admission_complete {budget : Nat} {nodes : List Node} {before after : Physical Symbol Formula}
    {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : Admission budget nodes before result after) :
    SourceCurrentConjunctionRowsWorkerCompletion.StableRun
      (fun p h => SourceCurrentConjunctionTupleAdmission.run p h budget nodes before) result after := by
  cases actual with
  | overflow exposed tooMany =>
      obtain ⟨p, h, done⟩ := SourceCurrentConjunctionRowsWorkerCompletion.exposures_complete exposed before.equality
      exact ⟨p, h, fun P H enoughP enoughH =>
        SourceCurrentConjunctionTupleAdmission.run_overflow P H _ _ _ _ _
          (done P H enoughP enoughH) tooMany⟩
  | zero exposed noTuples =>
      obtain ⟨p, h, done⟩ := SourceCurrentConjunctionRowsWorkerCompletion.exposures_complete exposed before.equality
      refine ⟨p, h, ?_⟩
      intro P H enoughP enoughH
      apply SourceCurrentConjunctionTupleAdmission.run_zero P H _ _ _ _ _ (done P H enoughP enoughH)
      simp only [noTuples, SourceCurrentConjunctionTupleBudget.sample, List.take_nil]
  | @positive predecessor nodes before after edges heap requirements exposed count fits allocated =>
      obtain ⟨p, h, readDone⟩ := SourceCurrentConjunctionRowsWorkerCompletion.exposures_complete exposed before.equality
      obtain ⟨laterP, laterH, tupleDone⟩ := SourceCurrentConjunctionRowsWorkerCompletion.tuples_complete allocated
      cases selected : SourceCurrentConjunctionTuples.tuples edges with
      | nil => simp only [selected, List.length_nil] at count; omega
      | cons first rest =>
          have predecessorEq : rest.length = predecessor := by
            simp only [selected, List.length_cons] at count
            omega
          have sampleEq : SourceCurrentConjunctionTupleBudget.sample budget
              (SourceCurrentConjunctionTuples.tuples edges) = first :: rest := by
            unfold SourceCurrentConjunctionTupleBudget.sample
            exact (List.take_of_length_le (by omega)).trans selected
          refine ⟨max p laterP, max h laterH, ?_⟩
          intro P H enoughP enoughH
          have completed := SourceCurrentConjunctionTupleAdmission.run_positive P H budget nodes before
            ⟨heap, before.equality⟩ after edges first rest requirements
            (readDone P H (by omega) (by omega)) sampleEq
            (by omega) (by simpa only [selected] using tupleDone P H (by omega) (by omega))
          simpa only [predecessorEq] using completed

/-- Every successful literal worklist derives its actual six-branch graph. -/
theorem explore_graph {p h budget : Nat} {table final : Table Symbol Formula}
    {pending : List (List Node)} {before after : Physical Symbol Formula}
    (actual : SourceCurrentConjunctionTupleWorker.explore p h budget table pending before = .done final after) :
    Run budget table pending before final after := by
  induction budget using Nat.strongRecOn generalizing table pending before final after with
  | ind budget smaller =>
      induction pending generalizing table before with
      | nil =>
          rw [SourceCurrentConjunctionTupleWorker.explore_nil] at actual
          cases actual
          exact .done
      | cons nodes rest tail =>
          cases impossible : nodes.any isEmpty with
          | true =>
              rw [SourceCurrentConjunctionTupleWorker.explore_empty p h budget table nodes rest before impossible] at actual
              exact .empty impossible (tail actual)
          | false =>
              cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes with
              | true =>
                  rw [SourceCurrentConjunctionTupleWorker.explore_skip p h budget table nodes rest before impossible skipped] at actual
                  exact .skip impossible skipped (tail actual)
              | false =>
                  cases sampled : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before with
                  | failed fault middle =>
                      rw [SourceCurrentConjunctionTupleWorker.explore_admission_failed p h budget table nodes rest before middle
                        fault impossible skipped sampled] at actual
                      cases actual
                  | done result middle =>
                      have admission := admission_graph sampled
                      cases result with
                      | overflow =>
                          have positive := (SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes skipped).1
                          rw [SourceCurrentConjunctionTupleWorker.explore_overflow p h budget table nodes rest before middle
                            impossible skipped sampled] at actual
                          exact .overflow impossible skipped admission (smaller 0 positive actual)
                      | zero =>
                          rw [SourceCurrentConjunctionTupleWorker.explore_zero p h budget table nodes rest before middle
                            impossible skipped sampled] at actual
                          exact .zero impossible skipped admission (tail actual)
                      | positive predecessor requirements =>
                          have charge := SourceCurrentConjunctionTupleAdmission.positive_charge p h budget nodes before middle
                            predecessor requirements sampled
                          rw [SourceCurrentConjunctionTupleWorker.explore_positive p h budget table nodes rest before middle
                            predecessor requirements impossible skipped sampled] at actual
                          exact .positive impossible skipped admission (smaller (budget - (predecessor + 1)) (by omega) actual)

/-- Every worklist graph supplies stable replay of all entries and both physical fields. -/
theorem explore_complete {budget : Nat} {table final : Table Symbol Formula} {pending : List (List Node)}
    {before after : Physical Symbol Formula} (actual : Run budget table pending before final after) :
    StableRun (fun p h => SourceCurrentConjunctionTupleWorker.explore p h budget table pending before) final after := by
  induction actual with
  | done => exact ⟨0, 0, by intros; exact SourceCurrentConjunctionTupleWorker.explore_nil _ _ _ _ _⟩
  | empty impossible _ ih =>
      obtain ⟨p, h, done⟩ := ih
      exact ⟨p, h, fun P H enoughP enoughH =>
        (SourceCurrentConjunctionTupleWorker.explore_empty P H _ _ _ _ _ impossible).trans
          (done P H enoughP enoughH)⟩
  | skip nonempty fresh _ ih =>
      obtain ⟨p, h, done⟩ := ih
      exact ⟨p, h, fun P H enoughP enoughH =>
        (SourceCurrentConjunctionTupleWorker.explore_skip P H _ _ _ _ _ nonempty fresh).trans
          (done P H enoughP enoughH)⟩
  | overflow nonempty fresh admission _ ih =>
      obtain ⟨p, h, first⟩ := admission_complete admission
      obtain ⟨laterP, laterH, done⟩ := ih
      exact ⟨max p laterP, max h laterH, fun P H enoughP enoughH =>
        (SourceCurrentConjunctionTupleWorker.explore_overflow P H _ _ _ _ _ _ nonempty fresh
          (first P H (by omega) (by omega))).trans (done P H (by omega) (by omega))⟩
  | zero nonempty fresh admission _ ih =>
      obtain ⟨p, h, first⟩ := admission_complete admission
      obtain ⟨laterP, laterH, done⟩ := ih
      exact ⟨max p laterP, max h laterH, fun P H enoughP enoughH =>
        (SourceCurrentConjunctionTupleWorker.explore_zero P H _ _ _ _ _ _ nonempty fresh
          (first P H (by omega) (by omega))).trans (done P H (by omega) (by omega))⟩
  | positive nonempty fresh admission _ ih =>
      obtain ⟨p, h, first⟩ := admission_complete admission
      obtain ⟨laterP, laterH, done⟩ := ih
      exact ⟨max p laterP, max h laterH, fun P H enoughP enoughH =>
        (SourceCurrentConjunctionTupleWorker.explore_positive P H _ _ _ _ _ _ _ _ nonempty fresh
          (first P H (by omega) (by omega))).trans (done P H (by omega) (by omega))⟩

/-- Every successful literal decision derives its open shortcut or actual table and fixed point. -/
theorem decision_graph [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    {p h budget : Nat} {start : Node} {before after : Physical Symbol Formula} {answer : Bool}
    (actual : SourceCurrentConjunctionTupleWorker.decision p h budget start before = .done answer after) :
    Decision budget start before answer after := by
  cases admitted : closed start with
  | false =>
      simp only [SourceCurrentConjunctionTupleWorker.decision, admitted, Bool.false_eq_true, ite_false] at actual
      cases actual
      exact .open_input admitted
  | true =>
      cases explored : SourceCurrentConjunctionTupleWorker.explore p h budget [] [[start]] before with
      | failed =>
          simp only [SourceCurrentConjunctionTupleWorker.decision, admitted, ite_true, explored, Outcome.bind] at actual
          cases actual
      | done table current =>
          simp only [SourceCurrentConjunctionTupleWorker.decision, admitted, ite_true, explored, Outcome.bind] at actual
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
    StableRun (fun p h => SourceCurrentConjunctionTupleWorker.decision p h budget start before) answer after := by
  cases actual with
  | open_input isOpen =>
      exact ⟨0, 0, by intros; exact SourceCurrentConjunctionTupleWorker.decision_open _ _ _ _ _ isOpen⟩
  | closed closedInput explored grown =>
      obtain ⟨p, h, done⟩ := explore_complete explored
      exact ⟨p, h, fun P H enoughP enoughH =>
        SourceCurrentConjunctionTupleWorker.decision_closed_done P H _ _ _ _ _ _ closedInput
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
    (actual : SourceCurrentConjunctionTupleWorker.call p h budget memo query before = .done (answer, saved) after) :
    Call budget memo query before answer after saved := by
  cases found : memo query.referenceOf with
  | some entry =>
      obtain ⟨original, result⟩ := entry
      simp only [SourceCurrentConjunctionTupleWorker.call, found] at actual
      cases actual
      exact .hit found
  | none =>
      cases done : SourceCurrentConjunctionTupleWorker.decision p h budget query before with
      | failed =>
          simp only [SourceCurrentConjunctionTupleWorker.call, found, done, Outcome.bind] at actual
          cases actual
      | done result current =>
          simp only [SourceCurrentConjunctionTupleWorker.call, found, done, Outcome.bind] at actual
          cases actual
          exact .miss found (decision_graph done)

/-- Every call graph supplies stable replay of its full physical state and fourth memo. -/
theorem call_complete [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] {budget : Nat} {memo saved : Memo} {query : ConcreteNode}
    {before after : Physical ConcreteSymbol FullSyntax.Formula} {answer : Bool}
    (actual : Call budget memo query before answer after saved) :
    StableRun (fun p h => SourceCurrentConjunctionTupleWorker.call p h budget memo query before) (answer, saved) after := by
  cases actual with
  | hit found => exact ⟨0, 0, by intros; simp only [SourceCurrentConjunctionTupleWorker.call, found]⟩
  | miss absent actual =>
      obtain ⟨p, h, done⟩ := decision_complete actual
      exact ⟨p, h, fun P H enoughP enoughH => by
        simp only [SourceCurrentConjunctionTupleWorker.call, absent, done P H enoughP enoughH, Outcome.bind]⟩

end MicroCFTA.SourceCurrentConjunctionTupleExecution
