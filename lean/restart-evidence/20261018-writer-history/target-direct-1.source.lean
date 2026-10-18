import MicroCFTA.SourceCurrentMergePositiveRowOrigins
import MicroCFTA.SourceCurrentLowerOperationInvariants

/-!
# Actual target merge writer histories

Successful target stages preserve the actual earlier merge writers.
Projection supplies the physical facts for each completed merge call.
Native calls retain the merge table. No semantic read graph is an input.
-/
namespace MicroCFTA.SourceCurrentTargetMergeHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentLowerOperationInvariants (SharedGood)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMergePositiveRowOrigins (Raw)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "literalClear" => SourceCurrentAllocatedMerge.literalClear
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A completed operand derives causal writers from its actual projection and merge. -/
theorem operand {p h m s path values before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.operand p h m s path values before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (raw : Raw literalClear top memo) :
    Raw literalClear top saved := by
  obtain ⟨projected,middle,current,projectionDone,mergeDone⟩ :=
    (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
  obtain ⟨heap,graph,shape,sameMemo⟩ := SourceCurrentAllocatedTargetWorkerSound.projection_sound
    p h path values before memo projected middle current projectionDone
  subst current
  have facts := SourceEqualityProjectionCosts.forest_effects graph good.semantic good.costs available
  have merged := SourceCurrentAllocatedTargetWorkerSound.merge_sound
    m s projected middle memo result after saved mergeDone
  have middleHeap : middle.native.machine.heap = heap := by rw [shape]; rfl
  rw [middleHeap] at merged
  cases merged with
  | done called =>
    exact (SourceCurrentMergePositiveRowOrigins.call called.graph facts.2.1 facts.2.2.1
      (stored.grows facts.1) raw facts.2.2.2).1

private theorem target_leaf_memo {n left right before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.leaf n left right before memo = .done result after saved) :
    saved = memo := by
  cases observed : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before with
  | done value checked =>
    simp only [SourceCurrentAllocatedTargetWorker.leaf,observed] at actual
    cases actual
    rfl
  | yielded | failed | constraintError | blocked =>
    simp only [SourceCurrentAllocatedTargetWorker.leaf,observed] at actual
    cases actual

/-- Each actual fold stage retains writers through the exact head and tail states. -/
theorem fold {p h m s n values seed paths before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.fold p h m s n values seed paths before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (raw : Raw literalClear top memo) :
    Raw literalClear top saved := by
  induction paths generalizing before memo result after saved with
  | nil => exact operand actual good stored available raw
  | cons path paths ih =>
    obtain ⟨head,middle,current,first,later⟩ :=
      (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
    have headRaw := operand first good stored available raw
    obtain ⟨headEffect,headStored,_headAvailable⟩ :=
      SourceCurrentLowerOperationInvariants.operand first good stored available
    obtain ⟨tail,final,completed,rest,last⟩ :=
      (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp later
    have tailRaw := ih rest headEffect.good headStored
      (fun value member => headEffect.keeps.available value (available value member)) headRaw
    exact (target_leaf_memo last) ▸ tailRaw

/-- A literal target return preserves the causal merge table from its initial forest. -/
theorem target {p h m s n values paths before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.target p h m s n values paths before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (raw : Raw literalClear top memo) :
    Raw literalClear top saved := by
  cases paths with
  | nil => cases actual; exact raw
  | cons seed paths => exact fold actual good stored available raw

/-- A slot hit retains its table. A miss derives writers from the actual target call. -/
theorem force {p h m s n record originals path before result after}
    (actual : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before = .done result after)
    (good : SharedGood (width := width) before)
    (available : Values before.checked.native.machine.heap originals)
    (raw : Raw literalClear top before.memo) : Raw literalClear top after.memo := by
  cases found : before.targets path with
  | some value =>
    simp only [SourceCurrentAllocatedSharedTargetWorker.force,found] at actual
    cases actual
    exact raw
  | none =>
    cases returned : SourceCurrentAllocatedTargetWorker.target p h m s n originals
        (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo with
    | failed =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.force,found,returned] at actual
      cases actual
    | done value checked saved =>
      simp only [SourceCurrentAllocatedSharedTargetWorker.force,found,returned] at actual
      cases actual
      exact target returned good.checked good.stored available raw

/-- The native step after target forcing retains the completed merge writers. -/
theorem leaf {p h m s n record originals path input before result after}
    (actual : SourceCurrentAllocatedSharedTargetWorker.leaf p h m s n record originals path input before = .done result after)
    (good : SharedGood (width := width) before)
    (available : Values before.checked.native.machine.heap originals)
    (raw : Raw literalClear top before.memo) : Raw literalClear top after.memo := by
  cases first : SourceCurrentAllocatedSharedTargetWorker.force p h m s n record originals path before with
  | failed =>
    simp only [SourceCurrentAllocatedSharedTargetWorker.leaf,first,
      SourceCurrentAllocatedSharedTargetWorker.Outcome.bind] at actual
    cases actual
  | done value middle =>
    simp only [SourceCurrentAllocatedSharedTargetWorker.leaf,first,
      SourceCurrentAllocatedSharedTargetWorker.Outcome.bind] at actual
    have retained := force first good available raw
    have same := (SourceCurrentAllocatedSharedTargetWorker.step_state n value input middle).2.2
    rw [actual] at same
    exact same ▸ retained

end MicroCFTA.SourceCurrentTargetMergeHistory
