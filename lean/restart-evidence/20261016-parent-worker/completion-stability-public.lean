import MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedParentWorkerStability
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion.StableRun
#check MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion.StableRun
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion.edge_complete
#check MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion.edge_complete
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion.edgeBody_complete
#check MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion.edgeBody_complete
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerStability.local_done_stable
#check MicroCFTA.SourceCurrentAllocatedParentWorkerStability.local_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerStability.edge_done_stable
#check MicroCFTA.SourceCurrentAllocatedParentWorkerStability.edge_done_stable
#print axioms MicroCFTA.SourceCurrentAllocatedParentWorkerStability.edge_done_unique
#check MicroCFTA.SourceCurrentAllocatedParentWorkerStability.edge_done_unique

namespace MicroCFTA.ParentWorkerIndependentProbes
open Language InternedConstructorTemplates
open SourceCurrentAllocatedParentWorker
open SourceCurrentAllocatedParentWorkerCompletion
open SourceCurrentAllocatedParentWorkerStability
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

-- Raw rejection needs no field receipt and works with every stage bound zero.
example (budget : Nat) (symbol : Symbol) (original : Guard) (inherited : EqValue)
    (children : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (test : SourceEqualityMkEdgeAllocation.contradictory original = true) :
    edge 0 0 0 0 0 0 0 0 0 budget symbol original inherited children before fourth memo =
      .done (SourceCurrentAllocatedMkEdge.reject symbol before).1
        (SourceCurrentAllocatedMkEdge.reject symbol before).2 fourth memo :=
  edge_rejected _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ test

-- Rejected graph completion discharges its unused live-field premise internally.
example (budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (children : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (test : SourceEqualityMkEdgeAllocation.contradictory original = true) :
    StableRun (fun g s r e p h m c n => edge g s r e p h m c n budget symbol original inherited children before fourth memo)
      (SourceCurrentAllocatedMkEdge.reject symbol before).1 (SourceCurrentAllocatedMkEdge.reject symbol before).2 fourth memo := by
  apply edge_complete (SourceCurrentAllocatedParentEdge.Edge.rejected (loaded := loaded) test)
  intro live
  rw [test] at live
  cases live

-- Live graph completion retains the exact local forest and checked constructor return.
example {budget : Nat} {symbol : Symbol} {original : Guard} {loaded : Allocated} {inherited : EqValue}
    {children results : List (Value Symbol Guard)} {before middle after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo} {result : EdgeValue Symbol Guard}
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false)
    (field : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (localGraph : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited children before fourth memo
      results middle savedFourth saved)
    (constructed : SourceCurrentAllocatedMkEdge.build symbol loaded results middle = (.ok result, after)) :
    StableRun (fun g s r e p h m c n => edge g s r e p h m c n budget symbol original inherited children before fourth memo)
      result after savedFourth saved :=
  edge_complete (.live live localGraph constructed) (fun _ => field)

-- Outer body completion uses its own field, checked return, and both untouched result tables.
example {budget : Nat} {request : SourceCurrentAllocatedPartialState.EdgeRequest}
    {before after : Caller width} {result : EdgeValue Symbol Guard}
    (actual : SourceCurrentAllocatedPartialGraph.EdgeBody budget request before result after) :
    StableRun (fun g s r e p h m c n => edge g s r e p h m c n budget request.value.entry.key.symbol
      request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge)
      result after.checked after.fourth after.merge ∧
      after.nodeResults = before.nodeResults ∧ after.edgeResults = before.edgeResults := by
  refine ⟨edgeBody_complete actual, ?_⟩
  cases actual
  exact ⟨rfl, rfl⟩

-- Missing live representation remains distinct and retains the original checked state.
example (g s r e p h m c n budget : Nat) (symbol : Symbol) (original : Guard) (inherited : EqValue)
    (children : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false)
    (absent : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok none) :
    edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .failed .missingField before fourth memo := edge_missing_field _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ live absent

-- Malformed field errors remain literal and skip every local stage.
example (g s r e p h m c n budget : Nat) (symbol : Symbol) (original : Guard) (inherited : EqValue)
    (children : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (message : String) (live : SourceEqualityMkEdgeAllocation.contradictory original = false)
    (failed : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .error message) :
    edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .failed (.field message) before fourth memo := edge_field_error _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ message live failed

-- Constructor failure keeps its actual reached operation state, not the pre-constructor cache.
example (symbol : Symbol) (loaded : Allocated) (children : List (Value Symbol Guard))
    (before after : Checked width) (fourth : Fourth) (memo : Memo) (message : String)
    (failed : SourceCurrentAllocatedMkEdge.build symbol loaded children before = (.error message, after)) :
    (build symbol loaded children before fourth memo).state.operations = after.operations := by
  rw [build_error symbol loaded children before after fourth memo message failed]
  rfl

-- Local failure retains the complete diagnostic, including any nested class-local target slots.
example (g s r e p h m c n budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (children : List (Value Symbol Guard)) (before after : Checked width) (fourth savedFourth : Fourth) (memo saved : Memo)
    (fault : SourceCurrentAllocatedLocalWorker.Fault width)
    (failed : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited children before fourth memo =
      .failed fault after savedFourth saved) :
    reduceChildren g s r e p h m c n budget loaded inherited children before fourth memo =
      .failed (.localReduction fault) after savedFourth saved := by simp only [reduceChildren, failed]

-- Different successful bounds identify raw edge fields and every complete returned state component.
example {g s r e p h m c n G S R E P H M C N budget : Nat} {symbol : Symbol} {original : Guard} {inherited : EqValue}
    {children : List (Value Symbol Guard)} {first second : EdgeValue Symbol Guard} {before after later : Checked width}
    {fourth savedFourth currentFourth : Fourth} {memo saved current : Memo}
    (one : edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .done first after savedFourth saved)
    (two : edge G S R E P H M C N budget symbol original inherited children before fourth memo =
      .done second later currentFourth current) :
    first.entry.key.constraint = second.entry.key.constraint ∧ first.children = second.children ∧
      after = later ∧ savedFourth = currentFourth ∧ saved = current := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := edge_done_unique one two
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
end MicroCFTA.ParentWorkerIndependentProbes
