import MicroCFTA.SourceCurrentUnionNormalScan
import MicroCFTA.SourceCurrentUnionNormalEdits
import MicroCFTA.SourceCurrentAllocatedParentWorker

/-!
# Union normality through actual Local and Parent workers

The literal precheck precedes Scan, Required, and the class pass. Parent
performs the actual field lookup and checked edge construction. Every
stopping result retains the invariant from the exact initial heap.
No whole outer completion or source-progress result is asserted here.
-/
namespace MicroCFTA.SourceCurrentUnionNormalLocalParent
open InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record

private theorem bind (first : SourceCurrentAllocatedLocalWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedLocalWorker.Outcome B width)
    (normal : UnionNormal first.state.native.machine.heap)
    (later : ∀ value after fourth memo, UnionNormal after.native.machine.heap → UnionNormal (next value after fourth memo).state.native.machine.heap) :
    UnionNormal (first.bind next).state.native.machine.heap := by
  cases first with
  | failed => exact normal
  | done value state fourth memo => exact later value state fourth memo normal

private theorem scan [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (g s p h n budget : Nat) (records : List Record) (values : List (Value Symbol Guard))
    (state : Checked width) (fourth : Fourth) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedLocalWorker.scan g s p h n budget records values state fourth memo).state.native.machine.heap := by
  have retained := SourceCurrentUnionNormalScan.records g s p h n budget values records state fourth normal
  cases actual : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records state fourth <;>
    simpa only [SourceCurrentAllocatedLocalWorker.scan,actual,SourceCurrentAllocatedLocalWorker.Outcome.state,
      SourceCurrentAllocatedScanWorker.Outcome.state] using retained

private theorem required [DecidableEq (EdgeKey Symbol Guard)] (r h : Nat)
    (paths : List SourceEqualityNeeded.Path) (values : List (Value Symbol Guard))
    (state : Checked width) (fourth : Fourth) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedLocalWorker.required r h paths values state fourth memo).state.native.machine.heap := by
  have retained := SourceCurrentRequiredUnionNormalRead.requireAll r h paths values state.native.machine.heap normal
  cases actual : SourceEqualityRequiredExecution.requireAll r h paths values state.native.machine.heap <;>
    simpa only [SourceCurrentAllocatedLocalWorker.required,actual,SourceCurrentAllocatedLocalWorker.Outcome.state,
      SourceCurrentRequiredUnionNormalRead.StoppedNormal,SourceCurrentConjunctionClassScan.advanceHeap,
      SourceCurrentAllocatedQueryMemo.advancePhysical,SourceRecursiveIntersectionThunks.advance] using retained

private theorem pass [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (e p h m s n : Nat)
    (records : List Record) (values : List (Value Symbol Guard))
    (state : Checked width) (fourth : Fourth) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedLocalWorker.pass e p h m s n records values state fourth memo).state.native.machine.heap := by
  have retained := SourceCurrentUnionNormalEdits.pass e p h m s n records values state memo normal
  cases actual : SourceCurrentAllocatedClassWorker.pass e p h m s n records values state memo <;>
    simpa only [SourceCurrentAllocatedLocalWorker.pass,actual,SourceCurrentAllocatedLocalWorker.Outcome.state,
      SourceCurrentAllocatedClassWorker.Outcome.state] using retained

private theorem classes [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (g s r e p h m c n budget : Nat) (records : List Record) (values : List (Value Symbol Guard))
    (state : Checked width) (fourth : Fourth) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n budget records values state fourth memo).state.native.machine.heap := by
  apply bind _ _ (scan g s p h n budget records values state fourth memo normal)
  intro result middle saved current middleNormal
  split
  · exact middleNormal
  · exact bind _ _ (required r h _ values middle saved current middleNormal)
      (fun requiredValues after next warm afterNormal => pass e p h m c n _ requiredValues after next warm afterNormal)

/-- Actual Local reduction retains union normality through every reached phase and fault. -/
theorem local [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (g s r e p h m c n budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (state : Checked width) (fourth : Fourth) (memo : Memo)
    (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values state fourth memo).state.native.machine.heap := by
  unfold SourceCurrentAllocatedLocalWorker.reduce
  dsimp only
  split
  · exact normal
  · exact normal
  · exact normal
  · exact classes g s r e p h m c n budget _ values _ fourth memo normal

private theorem raw_build [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (loaded : Allocated)
    (values : List (Value Symbol Guard)) (state : Checked width) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedMkEdge.build symbol loaded values state).2.native.machine.heap := by
  unfold SourceCurrentAllocatedMkEdge.build SourceEqualityMkEdgeAllocation.build
  dsimp only
  split
  · exact normal
  · rename_i keep actual
    cases keep
    · exact SourceCurrentRequiredUnionNormal.edge symbol _ [.empty] _ normal
    · exact SourceCurrentRequiredUnionNormal.edge symbol _ values _ normal

private theorem parent_build [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (loaded : Allocated)
    (values : List (Value Symbol Guard)) (state : Checked width) (fourth : Fourth) (memo : Memo)
    (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedParentWorker.build symbol loaded values state fourth memo).state.native.machine.heap := by
  have retained := raw_build symbol loaded values state normal
  unfold SourceCurrentAllocatedParentWorker.build
  dsimp only
  split <;> exact retained

private theorem children [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (g s r e p h m c n budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (state : Checked width) (fourth : Fourth) (memo : Memo)
    (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedParentWorker.reduceChildren g s r e p h m c n budget loaded inherited values state fourth memo).state.native.machine.heap := by
  have retained := local g s r e p h m c n budget loaded inherited values state fourth memo normal
  cases actual : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited values state fourth memo <;>
    simpa only [SourceCurrentAllocatedParentWorker.reduceChildren,actual,SourceCurrentAllocatedParentWorker.Outcome.state,
      SourceCurrentAllocatedLocalWorker.Outcome.state] using retained

/-- Actual Parent edge reduction retains normality on raw rejection and all live outcomes. -/
theorem parent [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
    (g s r e p h m c n budget : Nat) (symbol : Symbol) (original : Guard) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (state : Checked width) (fourth : Fourth) (memo : Memo)
    (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget symbol original inherited values state fourth memo).state.native.machine.heap := by
  unfold SourceCurrentAllocatedParentWorker.edge
  split
  · exact SourceCurrentRequiredUnionNormal.edge symbol _ [.empty] _ normal
  · split
    · exact normal
    · exact normal
    · have retained := children g s r e p h m c n budget _ inherited values state fourth memo normal
      cases actual : SourceCurrentAllocatedParentWorker.reduceChildren g s r e p h m c n budget _ inherited values state fourth memo with
      | failed => simpa only [actual,SourceCurrentAllocatedParentWorker.Outcome.bind,SourceCurrentAllocatedParentWorker.Outcome.state] using retained
      | done values after saved warm =>
          exact parent_build symbol _ values after saved warm (by simpa only [actual,SourceCurrentAllocatedParentWorker.Outcome.state] using retained)
end MicroCFTA.SourceCurrentUnionNormalLocalParent
