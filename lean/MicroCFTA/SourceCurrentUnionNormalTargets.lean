import MicroCFTA.SourceCurrentUnionNormalNativePrograms
import MicroCFTA.SourceCurrentUnionNormalProjectionGate
import MicroCFTA.SourceCurrentUnionNormalMerge
import MicroCFTA.SourceCurrentAllocatedSeededWorker
import MicroCFTA.SourceCurrentAllocatedSharedTargetWorker

/-!
# Union normality through actual first-seeded and shared targets

The workers retain the exact captured forest, seed order, and returned
checked state. Misses, ready slots, native faults, and pending reads all
retain the invariant. No callback or completed-result law is an input.
-/
namespace MicroCFTA.SourceCurrentUnionNormalTargets
open InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State

private theorem seeded_bind (first : SourceCurrentAllocatedSeededWorker.Outcome width)
    (next : Value Symbol Guard → Checked width → SourceCurrentAllocatedSeededWorker.Outcome width)
    (normal : UnionNormal first.state.native.machine.heap)
    (later : ∀ value after, UnionNormal after.native.machine.heap → UnionNormal (next value after).state.native.machine.heap) :
    UnionNormal (first.bind next).state.native.machine.heap := by
  cases first with
  | failed => exact normal
  | done value state => exact later value state normal

private theorem seeded_operand [DecidableEq (EdgeKey Symbol Guard)] (p h : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (state : Checked width) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSeededWorker.operand p h path values state).state.native.machine.heap := by
  have retained := SourceCurrentUnionNormalProjectionGate.forest p h path values state.native.machine.heap normal
  cases actual : SourceEqualityProjectionWorker.forest p h path values state.native.machine.heap <;>
    simpa only [SourceCurrentAllocatedSeededWorker.operand,actual,SourceCurrentAllocatedSeededWorker.Outcome.state,
      SourceCurrentAllocatedQueryMemo.advancePhysical,SourceRecursiveIntersectionThunks.advance,
      SourceCurrentRequiredUnionNormalRead.StoppedNormal] using retained

private theorem seeded_leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (n : Nat)
    (left right : Value Symbol Guard) (state : Checked width) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSeededWorker.leaf n left right state).state.native.machine.heap := by
  have retained := SourceCurrentUnionNormalNativePrograms.request n IntersectionEmptyDomain.emptyDomain left right state normal
  cases actual : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) state <;>
    simpa only [SourceCurrentAllocatedSeededWorker.leaf,actual,SourceCurrentAllocatedSeededWorker.Outcome.state,
      SourceEqualityNativeDemand.Outcome.state] using retained

private theorem seeded_fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (p h n : Nat)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (state : Checked width) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSeededWorker.fold p h n values seed paths state).state.native.machine.heap := by
  induction paths generalizing state with
  | nil => exact seeded_operand p h seed values state normal
  | cons path rest ih =>
      exact seeded_bind _ _ (seeded_operand p h path values state normal)
        (fun head middle middleNormal => seeded_bind _ _ (ih middle middleNormal)
          (fun tail after afterNormal => seeded_leaf n head tail after afterNormal))

/-- The actual first-seed rotation retains normality on every bounded outcome. -/
theorem seeded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (p h n : Nat)
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (state : Checked width) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSeededWorker.seeded p h n values paths state).state.native.machine.heap := by
  cases paths with
  | nil => exact normal
  | cons seed rest => exact seeded_fold p h n values seed rest state normal

private theorem target_bind (first : SourceCurrentAllocatedTargetWorker.Outcome width)
    (next : Value Symbol Guard → Checked width → Memo → SourceCurrentAllocatedTargetWorker.Outcome width)
    (normal : UnionNormal first.state.native.machine.heap)
    (later : ∀ value after memo, UnionNormal after.native.machine.heap → UnionNormal (next value after memo).state.native.machine.heap) :
    UnionNormal (first.bind next).state.native.machine.heap := by
  cases first with
  | failed => exact normal
  | done value state memo => exact later value state memo normal

private theorem projection [DecidableEq (EdgeKey Symbol Guard)] (p h : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedTargetWorker.projection p h path values state memo).state.native.machine.heap := by
  have retained := SourceCurrentUnionNormalProjectionGate.forest p h path values state.native.machine.heap normal
  cases actual : SourceEqualityProjectionWorker.forest p h path values state.native.machine.heap <;>
    simpa only [SourceCurrentAllocatedTargetWorker.projection,actual,SourceCurrentAllocatedTargetWorker.Outcome.state,
      SourceCurrentAllocatedQueryMemo.advancePhysical,SourceRecursiveIntersectionThunks.advance,
      SourceCurrentRequiredUnionNormalRead.StoppedNormal] using retained

private theorem merge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (m s : Nat)
    (value : Value Symbol Guard) (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedTargetWorker.merge m s value state memo).state.native.machine.heap := by
  have retained := SourceCurrentUnionNormalMerge.merge SourceCurrentAllocatedMerge.literalClear m s value
    (SourceCurrentAllocatedNativeEffects.physical state) memo normal
  cases actual : SourceCurrentAllocatedMergeWorker.call SourceCurrentAllocatedMerge.literalClear m s value
      (SourceCurrentAllocatedNativeEffects.physical state) memo <;>
    simpa only [SourceCurrentAllocatedTargetWorker.merge,actual,SourceCurrentAllocatedTargetWorker.Outcome.state,
      SourceCurrentAllocatedMergeWorker.Outcome.state,SourceCurrentAllocatedQueryMemo.advancePhysical,
      SourceRecursiveIntersectionThunks.advance] using retained

private theorem operand [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (p h m s : Nat) (path : List Int)
    (values : List (Value Symbol Guard)) (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedTargetWorker.operand p h m s path values state memo).state.native.machine.heap :=
  target_bind _ _ (projection p h path values state memo normal) (fun value after saved afterNormal => merge m s value after saved afterNormal)

private theorem leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (n : Nat)
    (left right : Value Symbol Guard) (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedTargetWorker.leaf n left right state memo).state.native.machine.heap := by
  have retained := SourceCurrentUnionNormalNativePrograms.request n IntersectionEmptyDomain.emptyDomain left right state normal
  cases actual : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) state <;>
    simpa only [SourceCurrentAllocatedTargetWorker.leaf,actual,SourceCurrentAllocatedTargetWorker.Outcome.state,
      SourceEqualityNativeDemand.Outcome.state] using retained

private theorem fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (p h m s n : Nat)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedTargetWorker.fold p h m s n values seed paths state memo).state.native.machine.heap := by
  induction paths generalizing state memo with
  | nil => exact operand p h m s seed values state memo normal
  | cons path rest ih =>
      exact target_bind _ _ (operand p h m s path values state memo normal)
        (fun head middle current middleNormal => target_bind _ _ (ih middle current middleNormal)
          (fun tail after saved afterNormal => leaf n head tail after saved afterNormal))

/-- Actual Target retains normality through projection, Merge, and native requests. -/
theorem target [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (p h m s n : Nat)
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (state : Checked width) (memo : Memo) (normal : UnionNormal state.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedTargetWorker.target p h m s n values paths state memo).state.native.machine.heap := by
  cases paths with
  | nil => exact normal
  | cons seed rest => exact fold p h m s n values seed rest state memo normal

/-- Both ready slots and completed or failed target misses retain the invariant. -/
theorem force [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (p h m s n : Nat)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path)
    (state : Shared width) (normal : UnionNormal state.checked.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSharedTargetWorker.force p h m s n record values path state).state.checked.native.machine.heap := by
  unfold SourceCurrentAllocatedSharedTargetWorker.force
  split
  · exact normal
  · have retained := target p h m s n values (SourceEqualityClassTarget.operandPaths record.paths path) state.checked state.memo normal
    cases actual : SourceCurrentAllocatedTargetWorker.target p h m s n values
        (SourceEqualityClassTarget.operandPaths record.paths path) state.checked state.memo <;>
      simpa only [actual,SourceCurrentAllocatedTargetWorker.Outcome.state,SourceCurrentAllocatedSharedTargetWorker.Outcome.state,
        SourceCurrentAllocatedSharedTargetState.store] using retained

private theorem step [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (n : Nat)
    (left right : Value Symbol Guard) (state : Shared width) (normal : UnionNormal state.checked.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSharedTargetWorker.step n left right state).state.checked.native.machine.heap := by
  have retained := SourceCurrentUnionNormalNativePrograms.request n IntersectionEmptyDomain.emptyDomain left right state.checked normal
  cases actual : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) state.checked <;>
    simpa only [SourceCurrentAllocatedSharedTargetWorker.step,actual,SourceCurrentAllocatedSharedTargetWorker.Outcome.state,
      SourceEqualityNativeDemand.Outcome.state,SourceCurrentAllocatedSharedTargetState.advance] using retained

/-- Actual Force then leaf intersection retain the exact returned shared heap. -/
theorem shared_leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (p h m s n : Nat)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path)
    (input : Value Symbol Guard) (state : Shared width) (normal : UnionNormal state.checked.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record values path input state).state.checked.native.machine.heap := by
  have first := force p h m s n record values path state normal
  unfold SourceCurrentAllocatedSharedTargetWorker.leaf
  cases actual : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record values path state with
  | failed => simpa only [actual,SourceCurrentAllocatedSharedTargetWorker.Outcome.bind,SourceCurrentAllocatedSharedTargetWorker.Outcome.state] using first
  | done value after => exact step n value input after (by simpa only [actual,SourceCurrentAllocatedSharedTargetWorker.Outcome.state] using first)
end MicroCFTA.SourceCurrentUnionNormalTargets
