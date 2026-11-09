import MicroCFTA.SourceCurrentConjunctionSharedWorklistTerminalMaterialization

/-!
# Shared decision and completed-memo boundary

Closed decisions run the actual shared worklist, read its cached table, and
apply the existing fixed-point answer. Every fault retains the full private
and physical snapshot. Open inputs and memo hits perform no native read.
Only a successful miss inserts an answer. The selected caller does not use
this boundary yet. Boolean soundness and native resource bounds are separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorker
open InternedConstructorTemplates (Value EdgeKey)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "Table" => SourceCurrentConjunctionWorker.Table Symbol Formula
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "closed" => SourceCurrentConjunctionWorklist.closed
local notation "explore" => SourceCurrentConjunctionSharedWorklistRun.explore
local notation "initial" => SourceCurrentConjunctionSharedWorklistStep.initial
local notation "readTable" => SourceCurrentConjunctionSharedWorklistMaterialization.readTable

/-- Exploration, pure table reading, and fixed-point faults retain distinct diagnostics. -/
inductive Fault (Symbol Formula : Type) where
  | explore (actual : SourceCurrentConjunctionSharedWorklistStep.Fault Symbol Formula)
  | materialization
  | grow (table : SourceCurrentConjunctionWorker.Table Symbol Formula)

/-- Every outcome retains the exact shared private heaps and native physical state. -/
inductive Outcome (Symbol Formula Output : Type) where
  | done (output : Output) (state : SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula)
  | failed (fault : Fault Symbol Formula) (state : SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula)

/-- Successful and failed observations expose their identical reached snapshot. -/
def Outcome.state : Outcome Symbol Formula Output → WorkState
  | .done _ state | .failed _ state => state

/-- Only a successful observation enters the continuation at its actual snapshot. -/
def Outcome.bind (first : Outcome Symbol Formula Input)
    (next : Input → WorkState → Outcome Symbol Formula Output) : Outcome Symbol Formula Output :=
  match first with
  | .done value state => next value state
  | .failed fault state => .failed fault state

section Generic
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Derive the endpoint credits from the actual original-query execution. -/
noncomputable def endpointCredits (p h budget : Nat) (start : Node) (before : Physical) : List Nat :=
  (Classical.choose (SourceCurrentConjunctionSharedWorklistRunFrame.explore_frame
    p h budget start before)).credits

/-- The internally chosen credits certify the exact actual exploration endpoint. -/
theorem endpointCredits_valid (p h budget : Nat) (start : Node) (before : Physical) :
    SourceCurrentConjunctionRequirementRowsOrigins.Credits (endpointCredits p h budget start before)
      (explore p h budget start before).state.storage := by
  have same := Classical.choose_spec (SourceCurrentConjunctionSharedWorklistRunFrame.explore_frame
    p h budget start before)
  have valid := (Classical.choose (SourceCurrentConjunctionSharedWorklistRunFrame.explore_frame
    p h budget start before)).valid
  rw [same] at valid
  exact valid

/-- A drained original execution makes the actual chosen-credit table read succeed. -/
theorem endpoint_materializable (p h budget : Nat) (start : Node) (before : Physical)
    (after : WorkState) (actual : explore p h budget start before = .done .drained after) :
    ∃ table, readTable (endpointCredits p h budget start before) after = some table := by
  have valid := (SourceCurrentConjunctionSharedWorklistTerminalMaterialization.explore_invariants
    p h budget start before).1
  have creditValid := endpointCredits_valid p h budget start before
  rw [actual] at valid creditValid
  obtain ⟨cells, spines, _⟩ :=
    SourceCurrentConjunctionSharedWorklistTerminalMaterialization.explore_materializable
      p h budget start before after actual
  exact SourceCurrentConjunctionSharedWorklistTableRead.readTable_complete
    (endpointCredits p h budget start before) after creditValid cells spines valid

variable [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Open inputs skip reads. Closed inputs retain every actual exploration or table fault. -/
noncomputable def decision (p h budget : Nat) (start : Node) (before : Physical) :
    Outcome Symbol Formula Bool :=
  if closed start then
    match explore p h budget start before with
    | .failed fault after => .failed (.explore fault) after
    | .done _ after =>
        match readTable (endpointCredits p h budget start before) after with
        | none => .failed .materialization after
        | some table =>
            match SourceCurrentConjunctionEmptinessTable.grow .empty key closed table
                (table.length + 1) (fun _ => false) with
            | none => .failed (.grow table) after
            | some known => .done
                (SourceCurrentConjunctionEmptinessTable.answer .empty key closed table known start) after
  else .done false (initial budget start before)

/-- An open decision retains its original physical state and empty private heaps. -/
theorem decision_open (p h budget : Nat) (start : Node) (before : Physical)
    (openInput : closed start = false) :
    decision p h budget start before = .done false (initial budget start before) := by
  simp only [decision, openInput, Bool.false_eq_true, ite_false]

/-- An exploration fault retains its exact diagnostic and full returned snapshot. -/
theorem decision_failed (p h budget : Nat) (start : Node) (before : Physical)
    (fault : SourceCurrentConjunctionSharedWorklistStep.Fault Symbol Formula) (after : WorkState)
    (closedInput : closed start = true)
    (actual : explore p h budget start before = .failed fault after) :
    decision p h budget start before = .failed (.explore fault) after := by
  simp only [decision, closedInput, ite_true, actual]

/-- The concrete missing-table branch retains its actual exploration snapshot. -/
theorem decision_materialization_failed (p h budget : Nat) (start : Node) (before : Physical)
    (after : WorkState) (closedInput : closed start = true)
    (actual : explore p h budget start before = .done .drained after)
    (missing : readTable (endpointCredits p h budget start before) after = none) :
    decision p h budget start before = .failed .materialization after := by
  simp only [decision, closedInput, ite_true, actual, missing]

/-- A fixed-point failure retains both its literal table and the actual shared snapshot. -/
theorem decision_grow_failed (p h budget : Nat) (start : Node) (before : Physical)
    (after : WorkState) (table : Table) (closedInput : closed start = true)
    (actual : explore p h budget start before = .done .drained after)
    (read : readTable (endpointCredits p h budget start before) after = some table)
    (failed : SourceCurrentConjunctionEmptinessTable.grow .empty key closed table
      (table.length + 1) (fun _ => false) = none) :
    decision p h budget start before = .failed (.grow table) after := by
  simp only [decision, closedInput, ite_true, actual, read, failed]

/-- A completed decision answers from the literal cached table and fixed point. -/
theorem decision_closed_done (p h budget : Nat) (start : Node) (before : Physical)
    (after : WorkState) (table : Table) (known : SourceCurrentConjunctionEmptinessTable.State key table → Bool)
    (closedInput : closed start = true)
    (actual : explore p h budget start before = .done .drained after)
    (read : readTable (endpointCredits p h budget start before) after = some table)
    (grown : SourceCurrentConjunctionEmptinessTable.grow .empty key closed table
      (table.length + 1) (fun _ => false) = some known) :
    decision p h budget start before =
      .done (SourceCurrentConjunctionEmptinessTable.answer .empty key closed table known start) after := by
  simp only [decision, closedInput, ite_true, actual, read, grown]

/-- Original decisions return an exact exploration fault or an answer; internal table faults are unreachable. -/
theorem decision_total (p h budget : Nat) (start : Node) (before : Physical) :
    (∃ fault after, decision p h budget start before = .failed (.explore fault) after) ∨
      ∃ answer after, decision p h budget start before = .done answer after := by
  cases classified : closed start with
  | false => exact Or.inr ⟨false, initial budget start before, decision_open p h budget start before classified⟩
  | true =>
      rcases SourceCurrentConjunctionSharedWorklistTerminalMaterialization.explore_total
        p h budget start before with failed | completed
      · obtain ⟨fault, after, actual⟩ := failed
        exact Or.inl ⟨fault, after, decision_failed p h budget start before fault after classified actual⟩
      · obtain ⟨after, _, _, actual, _⟩ := completed
        obtain ⟨table, read⟩ := endpoint_materializable p h budget start before after actual
        have grown := SourceCurrentConjunctionEmptinessTable.grow_rounds_complete .empty key closed
          table table.length 0 (by omega)
        exact Or.inr ⟨_, after, decision_closed_done p h budget start before after table _
          classified actual read grown⟩
end Generic

local notation "ConcreteSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "ConcreteGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ConcreteNode" => Value ConcreteSymbol ConcreteGuard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "ConcretePhysical" => SourceCurrentConjunctionRowsWorker.Physical ConcreteSymbol FullSyntax.Formula
local notation "ConcreteState" => SourceCurrentConjunctionSharedWorklistStep.State ConcreteSymbol FullSyntax.Formula

/-- Hits perform no reads. Only successful misses insert the actual query and answer. -/
noncomputable def call [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (p h budget : Nat) (memo : Memo) (query : ConcreteNode)
    (before : ConcretePhysical) : Outcome ConcreteSymbol FullSyntax.Formula (Bool × Memo) :=
  match memo query.referenceOf with
  | some (_, answer) => .done (answer, memo) (initial budget query before)
  | none => (decision p h budget query before).bind fun answer after =>
      .done (answer, SourceCurrentEmptinessMemo.insert memo query answer) after

/-- A memo hit retains the same answer, complete memo, and original physical state. -/
theorem call_hit [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (p h budget : Nat) (memo : Memo) (query original : ConcreteNode)
    (before : ConcretePhysical) (answer : Bool)
    (found : memo query.referenceOf = some (original, answer)) :
    call p h budget memo query before = .done (answer, memo) (initial budget query before) := by
  simp only [call, found]

/-- A failed miss retains its exact fault and snapshot and publishes no completed memo entry. -/
theorem call_failed [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (p h budget : Nat) (memo : Memo) (query : ConcreteNode)
    (before : ConcretePhysical) (after : ConcreteState) (fault : Fault ConcreteSymbol FullSyntax.Formula)
    (absent : memo query.referenceOf = none)
    (failed : decision p h budget query before = .failed fault after) :
    call p h budget memo query before = .failed fault after := by
  simp only [call, absent, failed, Outcome.bind]

/-- A successful miss publishes only its actual returned answer at the same full snapshot. -/
theorem call_done [DecidableEq ConcreteSymbol] [DecidableEq (EdgeKey ConcreteSymbol ConcreteGuard)]
    [DecidableEq ConcreteNode] (p h budget : Nat) (memo : Memo) (query : ConcreteNode)
    (before : ConcretePhysical) (after : ConcreteState) (answer : Bool)
    (absent : memo query.referenceOf = none)
    (done : decision p h budget query before = .done answer after) :
    call p h budget memo query before =
      .done (answer, SourceCurrentEmptinessMemo.insert memo query answer) after := by
  simp only [call, absent, done, Outcome.bind]

end MicroCFTA.SourceCurrentConjunctionSharedWorker
