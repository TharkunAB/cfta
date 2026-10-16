import MicroCFTA.SourceCurrentConjunctionRowsWorker
import MicroCFTA.SourceCurrentConjunctionMemo

/-!
# Literal current conjunction exploration and memo requests

The worklist checks Empty before budget, closedness, and prior membership.
Only admission decreases the algorithmic budget. Actual returned row states
precede insertion and the generated requirements precede the old pending
suffix. Two independent bounds instrument projection and stored reads.
The fixed-point counter is an explicit observation bound. These serial
workers do not establish host forcing or lazy memo publication.
-/
namespace MicroCFTA.SourceCurrentConjunctionWorker
open InternedConstructorTemplates
open SourceCurrentConjunctionWorklist (closed)

abbrev Physical (Symbol Formula : Type) := SourceCurrentConjunctionRowsAllocation.State Symbol Formula
abbrev Table (Symbol Formula : Type) :=
  List (SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol (SourceSymbolicIndex.Constraint Formula)))

/-- Row failures retain their reached local worklist. Grow exhaustion retains the completed table. -/
inductive Fault (Symbol Formula : Type) where
  | rows (fault : SourceCurrentConjunctionRowsWorker.Fault) (table : Table Symbol Formula)
      (pending : List (List (Value Symbol (SourceSymbolicIndex.Constraint Formula))))
  | grow (table : Table Symbol Formula)

/-- Every completed or failed observation retains both returned physical state components. -/
inductive Outcome (Symbol Formula Output : Type) : Type 1 where
  | done (output : Output) (state : Physical Symbol Formula)
  | failed (fault : Fault Symbol Formula) (state : Physical Symbol Formula)

def Outcome.state : Outcome Symbol Formula Output → Physical Symbol Formula
  | .done _ state | .failed _ state => state

/-- Only a completed prefix enters its continuation at the literal returned state. -/
def Outcome.bind (first : Outcome Symbol Formula Input)
    (next : Input → Physical Symbol Formula → Outcome Symbol Formula Output) : Outcome Symbol Formula Output :=
  match first with
  | .done value state => next value state
  | .failed fault state => .failed fault state

variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Value Symbol Guard → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Value Symbol Guard → Bool)

/-- The finite budget worklist executes literal rows only after all source admission tests pass. -/
noncomputable def explore [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (p h budget : Nat) (table : Table Symbol Formula)
    (pending : List (List (Value Symbol Guard))) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (Table Symbol Formula) :=
  match pending with
  | [] => .done table before
  | nodes :: rest =>
      if nodes.any isEmpty then explore p h budget table rest before
      else if SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes then
        explore p h budget table rest before
      else
        match SourceCurrentConjunctionRowsWorker.rows p h nodes before with
        | .done requirements middle =>
            explore p h (budget - 1) (⟨nodes, requirements⟩ :: table) (requirements.flatten ++ rest) middle
        | .failed fault after => .failed (.rows fault table (nodes :: rest)) after
termination_by (budget, pending.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have positive := (SourceCurrentConjunctionEmptinessTable.admitted SourceCurrentConjunctionRequirements.key
      SourceCurrentConjunctionWorklist.closed budget table nodes
      (Bool.eq_false_iff.mpr (by assumption))).1
    omega

/-- Open inputs skip exploration. Closed inputs execute it before the literal finite fixed point. -/
noncomputable def decision [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)] (p h budget : Nat) (start : Value Symbol Guard)
    (before : Physical Symbol Formula) : Outcome Symbol Formula Bool :=
  if closed start then
    (explore p h budget [] [[start]] before).bind fun table after =>
      match SourceCurrentConjunctionEmptinessTable.grow .empty key closed table (budget + 1) (fun _ => false) with
      | some known => .done (SourceCurrentConjunctionEmptinessTable.answer .empty key closed table known start) after
      | none => .failed (.grow table) after
  else .done false before

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

/-- Lookup precedes the body guard. Only a completed miss inserts its original query and answer. -/
noncomputable def call [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq (Value ConcreteSymbol ConcreteGuard)] (p h budget : Nat) (memo : Memo)
    (query : Value ConcreteSymbol ConcreteGuard) (before : Physical ConcreteSymbol FullSyntax.Formula) :
    Outcome ConcreteSymbol FullSyntax.Formula (Bool × Memo) :=
  match memo query.referenceOf with
  | some (_, answer) => .done (answer, memo) before
  | none => (decision p h budget query before).bind fun answer after =>
      .done (answer, SourceCurrentEmptinessMemo.insert memo query answer) after

/-- A failed memo miss retains its literal physical failure and inserts no completed answer. -/
theorem call_failed [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq (Value ConcreteSymbol ConcreteGuard)]
    (p h budget : Nat) (memo : Memo) (query : Value ConcreteSymbol ConcreteGuard)
    (before after : Physical ConcreteSymbol FullSyntax.Formula) (fault : Fault ConcreteSymbol FullSyntax.Formula)
    (absent : memo query.referenceOf = none) (failed : decision p h budget query before = .failed fault after) :
    call p h budget memo query before = .failed fault after := by
  simp only [call, absent, failed, Outcome.bind]

end MicroCFTA.SourceCurrentConjunctionWorker
