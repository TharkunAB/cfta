import MicroCFTA.SourceCurrentAllocatedGateWorker
import MicroCFTA.SourceCurrentAllocatedSeededWorker
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorker

/-!
# Literal class scanning with shared conjunction calls

Primary refusal runs the secondary gate. A false secondary answer executes
the first-seeded query and the current conjunction memo. True stops before
the suffix. Selected classes retain source order. Failed prefixes retain
their complete checked state, fourth memo, and underlying observation.
The five stage bounds remain separate from the conjunction budget.
Caller selection remains separate from this versioned worker.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedScanWorker
open Language EqualityNormalize InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
abbrev Checked := SourceEqualityNativeDemand.State
abbrev Memo := SourceCurrentEmptinessMemo.Memo
abbrev Result := Option Class × Constraints
abbrev Snapshot := SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula

/-- Each failure retains its class and exact reached phase observation. -/
inductive Fault (width : Nat) : Type 1 where
  | gate (paths : Class) (observation : SourceCurrentAllocatedGateWorker.Fault)
  | query (paths : Class) (observation : SourceCurrentAllocatedSeededWorker.Fault width)
  | decision (paths : Class) (observation : SourceCurrentConjunctionSharedWorker.Fault Symbol FullSyntax.Formula)
      (snapshot : Snapshot)
  | selected (paths : Class) (rest : Fault width)

/-- Every returned phase retains its complete checked state and actual fourth memo. -/
inductive Outcome (Output : Type) (width : Nat) : Type 1 where
  | done (result : Output) (state : Checked width) (memo : Memo)
  | failed (fault : Fault width) (state : Checked width) (memo : Memo)

def Outcome.state : Outcome Output width → Checked width
  | .done _ state _ | .failed _ state _ => state

def Outcome.memo : Outcome Output width → Memo
  | .done _ _ memo | .failed _ _ memo => memo

/-- Only success enters the next phase at the exact checked and memo return. -/
def Outcome.bind (first : Outcome A width)
    (next : A → Checked width → Memo → Outcome B width) : Outcome B width :=
  match first with
  | .done value state memo => next value state memo
  | .failed fault state memo => .failed fault state memo

/-- A selected head remains before the returned list or failed selected suffix. -/
def Outcome.select (paths : Class) : Outcome Result width → Outcome Result width
  | .done (stopped, selected) state memo => .done (stopped, paths :: selected) state memo
  | .failed fault state memo => .failed (.selected paths fault) state memo

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)]

/-- A literal gate advances only its reached heap and retains the fourth memo. -/
noncomputable def gate (belowEnd : Bool) (fuel : Nat) (values : List (Value Symbol Guard))
    (paths : Class) (before : Checked width) (memo : Memo) : Outcome Bool width :=
  match (if belowEnd then SourceCurrentAllocatedGateWorker.primary fuel values paths before
      else SourceCurrentAllocatedGateWorker.secondary fuel values paths before) with
  | .done answer after => .done answer after memo
  | .failed fault after => .failed (.gate paths fault) after memo

/-- A refused class projects without mergeAlternatives and retains the fourth memo. -/
noncomputable def query (p h n : Nat) (values : List (Value Symbol Guard)) (paths : Class)
    (before : Checked width) (memo : Memo) : Outcome (Value Symbol Guard) width :=
  match SourceCurrentAllocatedSeededWorker.seeded p h n values (paths.map (List.map Int.ofNat)) before with
  | .done value after => .done value after memo
  | .failed fault after => .failed (.query paths fault) after memo

/-- The current fourth memo installs only a completed literal conjunction answer. -/
noncomputable def decision (p h budget : Nat) (paths : Class) (value : Value Symbol Guard)
    (before : Checked width) (memo : Memo) : Outcome Bool width :=
  match SourceCurrentAllocatedSharedConjunctionWorker.call p h budget value before memo with
  | .done answer after saved _ => .done answer after saved
  | .failed fault after saved snapshot => .failed (.decision paths fault snapshot) after saved

/-- A successful decision retains the same checked return and fourth memo. -/
theorem decision_lift {p h budget : Nat} {paths : Class} {value : Value Symbol Guard}
    {before after : Checked width} {memo saved : Memo} {answer : Bool} {snapshot : Snapshot}
    (actual : SourceCurrentAllocatedSharedConjunctionWorker.call p h budget value before memo =
      .done answer after saved snapshot) :
    decision p h budget paths value before memo = .done answer after saved := by
  simp only [decision, actual]

/-- A failed decision retains the exact shared fault and complete private snapshot. -/
theorem decision_failed_lift {p h budget : Nat} {paths : Class} {value : Value Symbol Guard}
    {before after : Checked width} {memo saved : Memo}
    {fault : SourceCurrentConjunctionSharedWorker.Fault Symbol FullSyntax.Formula} {snapshot : Snapshot}
    (actual : SourceCurrentAllocatedSharedConjunctionWorker.call p h budget value before memo =
      .failed fault after saved snapshot) :
    decision p h budget paths value before memo = .failed (.decision paths fault snapshot) after saved := by
  simp only [decision, actual]

/-- Every successful decision exposes the same callee and its actual private snapshot. -/
theorem decision_done {p h budget : Nat} {paths : Class} {value : Value Symbol Guard}
    {before after : Checked width} {memo saved : Memo} {answer : Bool}
    (actual : decision p h budget paths value before memo = .done answer after saved) :
    ∃ snapshot, SourceCurrentAllocatedSharedConjunctionWorker.call p h budget value before memo =
      .done answer after saved snapshot := by
  cases observed : SourceCurrentAllocatedSharedConjunctionWorker.call p h budget value before memo with
  | done result reached current snapshot =>
      simp only [decision, observed] at actual
      obtain ⟨rfl, rfl, rfl⟩ := Outcome.done.inj actual
      exact ⟨snapshot, rfl⟩
  | failed fault reached current snapshot =>
      simp only [decision, observed] at actual
      cases actual

/-- Every failed decision exposes the literal snapshot and unchanged incoming fourth memo. -/
theorem decision_failed {p h budget : Nat} {paths : Class} {value : Value Symbol Guard}
    {before after : Checked width} {memo saved : Memo} {observation : Fault width}
    (actual : decision p h budget paths value before memo = .failed observation after saved) :
    ∃ fault snapshot,
      observation = .decision paths fault snapshot ∧ saved = memo ∧
      SourceCurrentAllocatedSharedConjunctionWorker.call p h budget value before memo =
        .failed fault after saved snapshot := by
  cases observed : SourceCurrentAllocatedSharedConjunctionWorker.call p h budget value before memo with
  | done result reached current snapshot =>
      simp only [decision, observed] at actual
      cases actual
  | failed fault reached current snapshot =>
      have retained := SourceCurrentAllocatedSharedConjunctionWorker.call_failed observed
      simp only [decision, observed] at actual
      obtain ⟨rfl, rfl, rfl⟩ := Outcome.failed.inj actual
      exact ⟨fault, snapshot, rfl, retained.1, rfl⟩

/-- Only reached branches execute; a true conjunction answer skips the remaining classes. -/
noncomputable def scan (g s p h n budget : Nat) (values : List (Value Symbol Guard)) :
    Constraints → Checked width → Memo → Outcome Result width
  | [], before, memo => .done (none, []) before memo
  | paths :: classes, before, memo =>
      (gate true g values paths before memo).bind fun primary middle current =>
        if primary then
          (gate false s values paths middle current).bind fun secondary later saved =>
            if secondary then scan g s p h n budget values classes later saved
            else (query p h n values paths later saved).bind fun value checked fourth =>
              (decision p h budget paths value checked fourth).bind fun answer after final =>
                if answer then .done (some paths, []) after final
                else scan g s p h n budget values classes after final
        else (scan g s p h n budget values classes middle current).select paths

/-- Empty input retains the complete checked state and fourth memo at every bound. -/
theorem scan_nil (g s p h n budget : Nat) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) :
    scan g s p h n budget values [] before memo = .done (none, []) before memo := rfl

end MicroCFTA.SourceCurrentAllocatedSharedScanWorker
