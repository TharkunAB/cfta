import MicroCFTA.SourceCurrentAllocatedRecordScanWorker
import MicroCFTA.SourceCurrentAllocatedClassWorker
import MicroCFTA.SourceCurrentAllocatedLocalReduction

/-!
# Literal local equality reduction

The actual precheck runs once. Live classes retain their original records
through Scan. Required children start from the Scan return. Class editing
starts from the required return. Every failure retains its phase observation,
full checked state, fourth memo, and warm merge memo. Structural bounds for
required children and class edits remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedLocalWorker
open Language EqualityNormalize InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap

/-- A phase failure retains its complete underlying observation. -/
inductive Fault (width : Nat) : Type 1 where
  | precheck (message : String)
  | scan (observation : SourceCurrentAllocatedScanWorker.Fault width)
  | required (observation : SourceEqualityRequiredWorker.Result Symbol Guard (List (Value Symbol Guard)))
  | classes (observation : SourceCurrentAllocatedClassWorker.Outcome width)

/-- Each return retains every shared state component at the reached phase. -/
inductive Outcome (Output : Type) (width : Nat) : Type 1 where
  | done (value : Output) (checked : Checked width) (fourth : Fourth) (memo : Memo)
  | failed (fault : Fault width) (checked : Checked width) (fourth : Fourth) (memo : Memo)

def Outcome.state : Outcome Output width → Checked width
  | .done _ checked _ _ | .failed _ checked _ _ => checked

def Outcome.fourth : Outcome Output width → Fourth
  | .done _ _ fourth _ | .failed _ _ fourth _ => fourth

def Outcome.memo : Outcome Output width → Memo
  | .done _ _ _ memo | .failed _ _ _ memo => memo

/-- Only success enters the continuation at the complete returned state. -/
def Outcome.bind (first : Outcome A width)
    (next : A → Checked width → Fourth → Memo → Outcome B width) : Outcome B width :=
  match first with
  | .done value checked fourth memo => next value checked fourth memo
  | .failed fault checked fourth memo => .failed fault checked fourth memo

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Record selection executes the same reached class queries with the warm merge memo. -/
noncomputable def scan (g s p h n budget : Nat) (records : List Record)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) :
    Outcome SourceCurrentAllocatedRecordScanWorker.Result width :=
  match SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records before fourth with
  | .done result after saved => .done result after saved memo
  | .failed fault after saved => .failed (.scan fault) after saved memo

/-- Required-path failures retain the exact returned constructor heap and observation. -/
noncomputable def required (r h : Nat) (paths : List SourceEqualityNeeded.Path) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo) : Outcome (List (Value Symbol Guard)) width :=
  match SourceEqualityRequiredExecution.requireAll r h paths values before.native.machine.heap with
  | .done results heap => .done results (advanceHeap before heap) fourth memo
  | .pending key heap => .failed (.required (.pending key heap)) (advanceHeap before heap) fourth memo
  | .unresolved name heap => .failed (.required (.unresolved name heap)) (advanceHeap before heap) fourth memo
  | .exhausted limit heap => .failed (.required (.exhausted limit heap)) (advanceHeap before heap) fourth memo

/-- Failed class edits retain their full shared state, including reached local target slots. -/
noncomputable def pass (e p h m c n : Nat) (records : List Record) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo) : Outcome (List (Value Symbol Guard)) width :=
  match SourceCurrentAllocatedClassWorker.pass e p h m c n records values before memo with
  | .done results after saved => .done results after fourth saved
  | raw@(.failed _ shared) => .failed (.classes raw) shared.checked fourth shared.memo

/-- A stopped class skips required children and class editing at its actual Scan return. -/
noncomputable def classes (g s r e p h m c n budget : Nat) (records : List Record)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) :
    Outcome (List (Value Symbol Guard)) width :=
  (scan g s p h n budget records values before fourth memo).bind fun result middle saved current =>
    match result.1 with
    | some _ => .done (EqualityLeafProjectionRuntimeEmpty.erase values) middle saved current
    | none =>
        (required r h (SourceEqualitySelectedRequired.paths (result.2.map SourceEqualityClassOrder.Record.paths))
          values middle saved current).bind fun requiredValues checked next warm =>
            pass e p h m c n result.2 requiredValues checked next warm

/-- The allocated own accessor and precheck select the literal local continuation. -/
noncomputable def reduce (g s r e p h m c n budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) :
    Outcome (List (Value Symbol Guard)) width :=
  let observed := runPrefix loaded.stored loaded.guard inherited before.operations
  let middle := SourceCurrentAllocatedQueryMemo.advancePhysical before ⟨before.native.machine.heap, observed.2⟩
  match observed.1 with
  | .error message => .failed (.precheck message) middle fourth memo
  | .ok .unchanged => .done values middle fourth memo
  | .ok .emptyChildren => .done (EqualityLeafProjectionRuntimeEmpty.erase values) middle fourth memo
  | .ok (.classes records) => classes g s r e p h m c n budget records values middle fourth memo

/-- An accessor or precheck error retains its actual returned operation tables. -/
theorem reduce_error (g s r e p h m c n budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (message : String)
    (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .error message) :
    reduce g s r e p h m c n budget loaded inherited values before fourth memo =
      .failed (.precheck message) (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth memo := by
  simp only [reduce, actual, SourceCurrentAllocatedPrecheck.state]

/-- An unchanged prefix skips every bounded continuation at its exact returned state. -/
theorem reduce_unchanged (g s r e p h m c n budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .unchanged) :
    reduce g s r e p h m c n budget loaded inherited values before fourth memo =
      .done values (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth memo := by
  simp only [reduce, actual, SourceCurrentAllocatedPrecheck.state]

/-- A contradictory prefix erases original slots before any Scan, requirement, or class work. -/
theorem reduce_emptyChildren (g s r e p h m c n budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (actual : (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok .emptyChildren) :
    reduce g s r e p h m c n budget loaded inherited values before fourth memo =
      .done (EqualityLeafProjectionRuntimeEmpty.erase values)
        (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth memo := by
  simp only [reduce, actual, SourceCurrentAllocatedPrecheck.state]

end MicroCFTA.SourceCurrentAllocatedLocalWorker
