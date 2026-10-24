import MicroCFTA.SourceCurrentConjunctionWorker
import MicroCFTA.SourceCurrentConjunctionRowsWorkerActual

/-!
# Graph correspondence and finite current conjunction workers

Literal successes derive the current worklist, decision, and memo graphs.
Finite graphs derive stable projection and read bounds. Initial physical
facts construct those graphs through the existing finite row proof. No
completed row supplier or future state invariant implements the worker.
-/
namespace MicroCFTA.SourceCurrentConjunctionWorkerCompletion
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentConjunctionWorker
open SourceCurrentConjunctionWorklist (Run closed)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Value Symbol Guard → Bool)

/-- Both larger bounds retain the exact completed output and physical state. -/
def StableRun (evaluation : Nat → Nat → Outcome Symbol Formula Output)
    (output : Output) (after : Physical Symbol Formula) : Prop :=
  ∃ p h, ∀ largerP largerH, p ≤ largerP → h ≤ largerH → evaluation largerP largerH = .done output after

/-- Every literal successful exploration records the same completed worklist. -/
theorem explore_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (p h budget : Nat) (table : Table Symbol Formula) (pending : List (List (Value Symbol Guard)))
    (before : Physical Symbol Formula) (final : Table Symbol Formula) (after : Physical Symbol Formula)
    (actual : explore p h budget table pending before = .done final after) :
    Run budget table pending before final after := by
  rw [explore.eq_def] at actual
  cases pending with
  | nil => cases actual; exact .done
  | cons nodes rest =>
      cases impossible : nodes.any isEmpty with
      | true =>
          simp only [impossible, ite_true] at actual
          exact .empty impossible (explore_sound p h budget table rest before final after actual)
      | false =>
          simp only [impossible, Bool.false_eq_true, ite_false] at actual
          cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes with
          | true =>
              simp only [skipped, ite_true] at actual
              exact .skip impossible skipped (explore_sound p h budget table rest before final after actual)
          | false =>
              simp only [skipped, Bool.false_eq_true, ite_false] at actual
              cases rows : SourceCurrentConjunctionRowsWorker.rows p h nodes before with
              | done requirements middle =>
                  simp only [rows] at actual
                  exact .admit impossible skipped (SourceCurrentConjunctionRowsWorkerActual.rows_graph rows)
                    (explore_sound p h (budget - 1) (⟨nodes, requirements⟩ :: table)
                      (requirements.flatten ++ rest) middle final after actual)
              | failed => simp only [rows] at actual; cases actual
termination_by (budget, pending.length)
decreasing_by
  all_goals first
    | apply Prod.Lex.right; simp_all
    | apply Prod.Lex.left
      have positive := (SourceCurrentConjunctionEmptinessTable.admitted SourceCurrentConjunctionRequirements.key
        SourceCurrentConjunctionWorklist.closed budget table nodes (by assumption)).1
      omega

/-- Finite actual worklist graphs supply stable lower-stage execution bounds. -/
theorem explore_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {budget : Nat} {table final : Table Symbol Formula} {pending : List (List (Value Symbol Guard))}
    {before after : Physical Symbol Formula} (actual : Run budget table pending before final after) :
    StableRun (fun p h => explore p h budget table pending before) final after := by
  induction actual with
  | done =>
      refine ⟨0, 0, ?_⟩
      intros
      dsimp only
      rw [explore.eq_def]
  | empty impossible rest ih =>
      obtain ⟨p, h, later⟩ := ih
      refine ⟨p, h, ?_⟩
      intro P H enoughP enoughH
      dsimp only
      rw [explore.eq_def]
      simpa only [impossible, ite_true] using later P H enoughP enoughH
  | skip nonempty skipped rest ih =>
      obtain ⟨p, h, later⟩ := ih
      refine ⟨p, h, ?_⟩
      intro P H enoughP enoughH
      dsimp only
      rw [explore.eq_def]
      simpa only [nonempty, Bool.false_eq_true, ite_false, skipped, ite_true] using later P H enoughP enoughH
  | admit nonempty fresh rows rest ih =>
      obtain ⟨p, h, own⟩ := SourceCurrentConjunctionRowsWorkerCompletion.rows_complete rows
      obtain ⟨laterP, laterH, later⟩ := ih
      refine ⟨max p laterP, max h laterH, ?_⟩
      intro P H enoughP enoughH
      dsimp only
      rw [explore.eq_def]
      simp only [nonempty, Bool.false_eq_true, ite_false, fresh,
        own P H (Nat.le_trans (Nat.le_max_left _ _) enoughP) (Nat.le_trans (Nat.le_max_left _ _) enoughH)]
      exact later P H (Nat.le_trans (Nat.le_max_right _ _) enoughP) (Nat.le_trans (Nat.le_max_right _ _) enoughH)

/-- A literal decision success has the current open shortcut or actual worklist and fixed point. -/
theorem decision_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (p h budget : Nat) (start : Value Symbol Guard) (before : Physical Symbol Formula)
    (answer : Bool) (after : Physical Symbol Formula)
    (actual : decision p h budget start before = .done answer after) :
    SourceCurrentConjunctionDecision.Decision budget start before answer after := by
  cases admitted : closed start with
  | false => simp only [decision, admitted, Bool.false_eq_true, ite_false] at actual; cases actual; exact .open_input admitted
  | true =>
      simp only [decision, admitted, ite_true] at actual
      cases explored : explore p h budget [] [[start]] before with
      | failed => simp only [explored, Outcome.bind] at actual; cases actual
      | done table current =>
          simp only [explored, Outcome.bind] at actual
          cases grown : SourceCurrentConjunctionEmptinessTable.grow .empty key closed table (budget + 1) (fun _ => false) with
          | none => simp only [grown] at actual; cases actual
          | some known =>
              simp only [grown] at actual
              cases actual
              exact .closed admitted (explore_sound p h budget [] [[start]] before _ _ explored) grown

/-- An actual decision graph supplies stable bounds for its exact physical return. -/
theorem decision_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    {budget : Nat} {start : Value Symbol Guard} {before after : Physical Symbol Formula} {answer : Bool}
    (actual : SourceCurrentConjunctionDecision.Decision budget start before answer after) :
    StableRun (fun p h => decision p h budget start before) answer after := by
  cases actual with
  | open_input openInput => exact ⟨0, 0, by intros; simp only [decision, openInput, Bool.false_eq_true, ite_false]⟩
  | closed admitted explored grown =>
      obtain ⟨p, h, later⟩ := explore_complete explored
      refine ⟨p, h, ?_⟩
      intro P H enoughP enoughH
      simp only [decision, admitted, ite_true, later P H enoughP enoughH, Outcome.bind, grown]

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

/-- A supplied memo success derives its literal current hit or completed miss. -/
theorem call_sound [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq (Value ConcreteSymbol ConcreteGuard)]
    (p h budget : Nat) (memo : Memo) (query : Value ConcreteSymbol ConcreteGuard)
    (before : Physical ConcreteSymbol FullSyntax.Formula) (answer : Bool)
    (after : Physical ConcreteSymbol FullSyntax.Formula) (saved : Memo)
    (actual : call p h budget memo query before = .done (answer, saved) after) :
    SourceCurrentConjunctionMemo.Call budget memo query before answer after saved := by
  cases found : memo query.referenceOf with
  | some entry =>
      obtain ⟨original, result⟩ := entry
      simp only [call, found] at actual
      cases actual
      exact .hit found
  | none =>
      cases done : decision p h budget query before with
      | failed => simp only [call, found, done, Outcome.bind] at actual; cases actual
      | done result current =>
          simp only [call, found, done, Outcome.bind] at actual
          cases actual
          exact .miss found (decision_sound p h budget query before _ _ done)

/-- Completed current memo graphs supply stable bounds without a body-completion premise. -/
theorem call_complete [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq (Value ConcreteSymbol ConcreteGuard)]
    {budget : Nat} {memo saved : Memo} {query : Value ConcreteSymbol ConcreteGuard}
    {before after : Physical ConcreteSymbol FullSyntax.Formula} {answer : Bool}
    (actual : SourceCurrentConjunctionMemo.Call budget memo query before answer after saved) :
    StableRun (fun p h => call p h budget memo query before) (answer, saved) after := by
  cases actual with
  | hit found => exact ⟨0, 0, by intros; simp only [call, found]⟩
  | miss absent body =>
      obtain ⟨p, h, later⟩ := decision_complete body
      exact ⟨p, h, by intro P H enoughP enoughH; simp only [call, absent, later P H enoughP enoughH, Outcome.bind]⟩

/-- Initial physical row facts construct finite literal exploration and its actual effects. -/
theorem explore_finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (budget : Nat) (table : Table Symbol Formula) (pending : List (List (Value Symbol Guard)))
    (before : Physical Symbol Formula) (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (stored : SourceCurrentConjunctionWorklist.TableReady before table)
    (available : SourceCurrentConjunctionWorklist.PendingReady before pending) :
    ∃ final after, StableRun (fun p h => explore p h budget table pending before) final after ∧
      Run budget table pending before final after ∧ SourceCurrentConjunctionRowsAllocation.Effects before after := by
  obtain ⟨final, after, actual, effects, _, _⟩ := SourceCurrentConjunctionWorklist.complete budget table pending before ready stored available
  exact ⟨final, after, explore_complete actual, actual, effects⟩

/-- Initial physical query facts construct finite literal current memo execution. -/
theorem call_finite [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq (Value ConcreteSymbol ConcreteGuard)]
    (budget : Nat) (memo : Memo) (query : Value ConcreteSymbol ConcreteGuard)
    (before : Physical ConcreteSymbol FullSyntax.Formula) (ready : SourceCurrentConjunctionRowsAllocation.Ready before)
    (available : Available before.heap query) :
    ∃ answer after saved, StableRun (fun p h => call p h budget memo query before) (answer, saved) after ∧
      SourceCurrentConjunctionMemo.Call budget memo query before answer after saved ∧
      SourceCurrentConjunctionRowsAllocation.Effects before after := by
  obtain ⟨answer, after, saved, actual, effects⟩ := SourceCurrentConjunctionMemo.complete budget memo query before ready available
  exact ⟨answer, after, saved, call_complete actual, actual, effects⟩

end MicroCFTA.SourceCurrentConjunctionWorkerCompletion
