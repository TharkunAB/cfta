import MicroCFTA.SourceCurrentConjunctionTupleAdmission
import MicroCFTA.SourceCurrentConjunctionWorker

/-!
# Physical conjunction exploration with a raw tuple budget

The worklist uses the actual physical admission worker. Overflow sets the
remaining budget to zero and does not insert the pending conjunction.
Zero-tuple admission inserts an empty row list without spending budget.
Positive admission charges every raw tuple, including rejected tuples.
The fixed-point counter uses the returned table length plus one.

These functions are the replacement executor for the planned migration.
The selected allocated caller still uses the earlier executor. The eager
operand exposure schedule remains explicit. This module does not establish
Haskell lazy read demand or a native bound on tuple-product construction.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleWorker
open InternedConstructorTemplates
open SourceCurrentConjunctionWorker (Physical Table Fault Outcome)
open SourceCurrentConjunctionWorklist (closed)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Execute raw-tuple admission and thread every actual returned physical state. -/
noncomputable def explore (p h budget : Nat) (table : Table Symbol Formula)
    (pending : List (List Node)) (before : Physical Symbol Formula) :
    Outcome Symbol Formula (Table Symbol Formula) :=
  match pending with
  | [] => .done table before
  | nodes :: rest =>
      if nodes.any isEmpty then explore p h budget table rest before
      else if SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes then
        explore p h budget table rest before
      else
        match _actual : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before with
        | .failed fault after => .failed (.rows fault table (nodes :: rest)) after
        | .done .overflow exposed => explore p h 0 table rest exposed
        | .done .zero exposed => explore p h budget (⟨nodes, []⟩ :: table) rest exposed
        | .done (.positive predecessor requirements) after =>
            explore p h (budget - (predecessor + 1)) (⟨nodes, requirements⟩ :: table)
              (requirements.flatten ++ rest) after
termination_by (budget, pending.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have positive := (SourceCurrentConjunctionEmptinessTable.admitted
      SourceCurrentConjunctionRequirements.key SourceCurrentConjunctionWorklist.closed budget table nodes
      (Bool.eq_false_iff.mpr (by assumption))).1
    omega
  · exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have charge := SourceCurrentConjunctionTupleAdmission.positive_charge p h budget nodes before after
      predecessor requirements (by assumption)
    omega

/-- An empty queue returns the complete current table and physical state. -/
theorem explore_nil (p h budget : Nat) (table : Table Symbol Formula) (before : Physical Symbol Formula) :
    explore p h budget table [] before = .done table before := by
  rw [explore.eq_def]

/-- An Empty operand removes the head before admission or exposure. -/
theorem explore_empty (p h budget : Nat) (table : Table Symbol Formula) (nodes : List Node)
    (pending : List (List Node)) (before : Physical Symbol Formula)
    (impossible : nodes.any isEmpty = true) :
    explore p h budget table (nodes :: pending) before = explore p h budget table pending before := by
  rw [explore.eq_def]
  simp only [impossible, ite_true]

/-- Budget, closedness, and repeated-key skips retain both physical states. -/
theorem explore_skip (p h budget : Nat) (table : Table Symbol Formula) (nodes : List Node)
    (pending : List (List Node)) (before : Physical Symbol Formula)
    (nonempty : nodes.any isEmpty = false)
    (skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = true) :
    explore p h budget table (nodes :: pending) before = explore p h budget table pending before := by
  rw [explore.eq_def]
  simp only [nonempty, Bool.false_eq_true, ite_false, skipped, ite_true]

/-- A failed admission retains its exact diagnostic, worklist, and returned state. -/
theorem explore_admission_failed (p h budget : Nat) (table : Table Symbol Formula) (nodes : List Node)
    (pending : List (List Node)) (before after : Physical Symbol Formula)
    (fault : SourceCurrentConjunctionRowsWorker.Fault)
    (nonempty : nodes.any isEmpty = false)
    (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
    (failed : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before = .failed fault after) :
    explore p h budget table (nodes :: pending) before = .failed (.rows fault table (nodes :: pending)) after := by
  rw [explore.eq_def]
  simp only [nonempty, fresh, Bool.false_eq_true, ite_false]
  rw [failed]

/-- Overflow inserts nothing and drains the old suffix at zero remaining budget. -/
theorem explore_overflow (p h budget : Nat) (table : Table Symbol Formula) (nodes : List Node)
    (pending : List (List Node)) (before exposed : Physical Symbol Formula)
    (nonempty : nodes.any isEmpty = false)
    (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
    (sampled : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before = .done .overflow exposed) :
    explore p h budget table (nodes :: pending) before = explore p h 0 table pending exposed := by
  rw [explore.eq_def]
  simp only [nonempty, fresh, Bool.false_eq_true, ite_false]
  rw [sampled]

/-- A zero-tuple admission stores no rows and keeps the remaining budget. -/
theorem explore_zero (p h budget : Nat) (table : Table Symbol Formula) (nodes : List Node)
    (pending : List (List Node)) (before exposed : Physical Symbol Formula)
    (nonempty : nodes.any isEmpty = false)
    (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
    (sampled : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before = .done .zero exposed) :
    explore p h budget table (nodes :: pending) before =
      explore p h budget (⟨nodes, []⟩ :: table) pending exposed := by
  rw [explore.eq_def]
  simp only [nonempty, fresh, Bool.false_eq_true, ite_false]
  rw [sampled]

/-- Positive admission charges the raw count and prepends only its actual requirements. -/
theorem explore_positive (p h budget : Nat) (table : Table Symbol Formula) (nodes : List Node)
    (pending : List (List Node)) (before after : Physical Symbol Formula)
    (predecessor : Nat) (requirements : List (List (List Node)))
    (nonempty : nodes.any isEmpty = false)
    (fresh : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes = false)
    (sampled : SourceCurrentConjunctionTupleAdmission.run p h budget nodes before =
      .done (.positive predecessor requirements) after) :
    explore p h budget table (nodes :: pending) before =
      explore p h (budget - (predecessor + 1)) (⟨nodes, requirements⟩ :: table)
        (requirements.flatten ++ pending) after := by
  rw [explore.eq_def]
  simp only [nonempty, fresh, Bool.false_eq_true, ite_false]
  rw [sampled]

/-- Open inputs skip all reads; closed inputs use the actual finite returned table. -/
noncomputable def decision [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    (p h budget : Nat) (start : Node)
    (before : Physical Symbol Formula) : Outcome Symbol Formula Bool :=
  if closed start then
    (explore p h budget [] [[start]] before).bind fun table after =>
      match SourceCurrentConjunctionEmptinessTable.grow .empty key closed table (table.length + 1) (fun _ => false) with
      | some known => .done (SourceCurrentConjunctionEmptinessTable.answer .empty key closed table known start) after
      | none => .failed (.grow table) after
  else .done false before

/-- An open query preserves the original physical state without entering exploration. -/
theorem decision_open [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    (p h budget : Nat) (start : Node) (before : Physical Symbol Formula)
    (openInput : closed start = false) : decision p h budget start before = .done false before := by
  simp only [decision, openInput, Bool.false_eq_true, ite_false]

/-- A completed closed decision retains its exact table, fixed point, and returned state. -/
theorem decision_closed_done [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]
    (p h budget : Nat) (start : Node)
    (before after : Physical Symbol Formula) (table : Table Symbol Formula)
    (known : SourceCurrentConjunctionEmptinessTable.State key table → Bool)
    (closedInput : closed start = true)
    (explored : explore p h budget [] [[start]] before = .done table after)
    (grown : SourceCurrentConjunctionEmptinessTable.grow .empty key closed table (table.length + 1)
      (fun _ => false) = some known) :
    decision p h budget start before =
      .done (SourceCurrentConjunctionEmptinessTable.answer .empty key closed table known start) after := by
  simp only [decision, closedInput, ite_true, explored, Outcome.bind, grown]

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo

/-- Only a completed miss stores its actual query and answer in the fourth memo. -/
noncomputable def call [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (p h budget : Nat) (memo : Memo) (query : ConcreteNode)
    (before : Physical ConcreteSymbol FullSyntax.Formula) :
    Outcome ConcreteSymbol FullSyntax.Formula (Bool × Memo) :=
  match memo query.referenceOf with
  | some (_, answer) => .done (answer, memo) before
  | none => (decision p h budget query before).bind fun answer after =>
      .done (answer, SourceCurrentEmptinessMemo.insert memo query answer) after

/-- A completed fourth-memo hit skips exploration and retains the entire physical state. -/
theorem call_hit [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (p h budget : Nat) (memo : Memo) (query original : ConcreteNode)
    (before : Physical ConcreteSymbol FullSyntax.Formula) (answer : Bool)
    (found : memo query.referenceOf = some (original, answer)) :
    call p h budget memo query before = .done (answer, memo) before := by
  simp only [call, found]

/-- A failed miss retains its exact state and installs no completed answer. -/
theorem call_failed [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (p h budget : Nat) (memo : Memo) (query : ConcreteNode)
    (before after : Physical ConcreteSymbol FullSyntax.Formula) (fault : Fault ConcreteSymbol FullSyntax.Formula)
    (absent : memo query.referenceOf = none)
    (failed : decision p h budget query before = .failed fault after) :
    call p h budget memo query before = .failed fault after := by
  simp only [call, absent, failed, Outcome.bind]

end MicroCFTA.SourceCurrentConjunctionTupleWorker
