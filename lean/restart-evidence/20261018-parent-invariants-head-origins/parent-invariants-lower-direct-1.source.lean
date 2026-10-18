import MicroCFTA.SourceCurrentNativeOperationHeap
import MicroCFTA.SourceCurrentOpenProjectionFields
import MicroCFTA.SourceCurrentAllocatedParentWorker
import MicroCFTA.SourceCurrentAllocatedTargetWorkerSound
import MicroCFTA.SourceCurrentAllocatedMergePhysical
import MicroCFTA.SourceCurrentConjunctionCallUnique
import MicroCFTA.SourceCurrentConjunctionWorkerCompletion

/-!
# Physical invariants through actual completed lower workers

The proofs inspect literal successful worker equations. Initial physical
memo entries must contain available results. No reached range, input plan,
semantic native result law, or supplied completed graph is an input.
-/
namespace MicroCFTA.SourceCurrentLowerOperationInvariants
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentNativeOperationHeap (Good)
open SourceCurrentMemoMergeEffects (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Fields" => SourceCurrentConjunctionEquality.Fields
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}

/-- Initial probe heaps and weak native cells provide the physical lower-worker state. -/
theorem Good.physical {before : Checked width} (good : Good before) :
    SourceCurrentConjunctionRowsAllocation.Ready (physical before) :=
  ⟨good.semantic,good.costs,good.operations,good.fields⟩

/-- Literal physical advancement retains all weak native cells and full equality memo validity. -/
theorem Good.advance {before : Checked width} (good : Good before) (after : Physical)
    (effects : Effects (physical before) after) : Good (advancePhysical before after) := by
  have extension := SourceCurrentAllocatedQueryMemo.advance_extension before after effects
  have valid : SourceRecursiveIntersectionKernel.Valid (advancePhysical before after).native.machine :=
    ⟨effects.ready.semantic.ready.semantic.1.normal.facts,good.native.machine.2⟩
  exact ⟨⟨valid,
    FlatMemoThunk.Valid.map _ _ _ _ good.native.nodes (fun _ ready => ready.grows extension),
    FlatMemoThunk.Valid.map _ _ _ _ good.native.edges (fun _ ready => ready.grows extension)⟩,
    effects.keeps.ready,effects.ready.valid,effects.ready.fields,effects.ready.semantic,effects.ready.costs⟩

/-- A successful stage retains the exact current heap and all earlier physical records. -/
structure Effect (before after : Checked width) : Prop where
  /-- Every final physical invariant follows from the initial state. -/
  good : Good after
  /-- Constructor records and issued identities remain present. -/
  keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap after.native.machine.heap
  /-- Equality allocation and completed operation entries grow. -/
  operations : SourceEqualityConstraintMemoAllocation.Grows before.operations after.operations

/-- An unchanged checked state retains all initial invariants. -/
theorem Effect.refl (before : Checked width) (good : Good before) : Effect before before :=
  ⟨good,SourceEqualityRequiredCache.pure_keeps _ good.heap,SourceEqualityConstraintMemoAllocation.grows_refl _⟩

/-- Consecutive actual returns retain both physical histories. -/
theorem Effect.trans {before middle after : Checked width} (first : Effect before middle)
    (last : Effect middle after) : Effect before after :=
  ⟨last.good,first.keeps.trans last.keeps,SourceCurrentConjunctionEquality.grows_trans first.operations last.operations⟩

private theorem advanced {before : Checked width} (good : Good before) {after : Physical}
    (effects : Effects (physical before) after) : Effect before (advancePhysical before after) :=
  ⟨good.advance after effects,effects.keeps,effects.grows⟩

private theorem same_operations {before : Checked width} (good : Good before)
    (heap : State Symbol Guard) (keeps : SourceEqualityRequiredCache.Keeps before.native.machine.heap heap)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap heap) (fields : Fields before.operations heap) :
    Effect before (advancePhysical before ⟨heap,before.operations⟩) :=
  advanced good ⟨keeps,⟨semantic,costs,good.operations,fields⟩,SourceEqualityConstraintMemoAllocation.grows_refl _⟩

private theorem forest {path values before result heap}
    [DecidableEq (EdgeKey Symbol Guard)]
    (actual : SourceEqualityProjectionGraph.Forest path values before.native.machine.heap result heap)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before (advancePhysical before ⟨heap,before.operations⟩) ∧ Available heap result := by
  have checked := SourceEqualityProjectionCosts.forest_effects actual good.semantic good.costs available
  have fields := SourceCurrentOpenProjectionFields.forest (FieldAvailable before.operations)
    actual good.semantic good.costs available good.fields
  exact ⟨same_operations good heap checked.1 checked.2.1 checked.2.2.1 fields,checked.2.2.2⟩

private theorem projection {p h path values before memo result after saved}
    [DecidableEq (EdgeKey Symbol Guard)]
    (actual : SourceCurrentAllocatedTargetWorker.projection p h path values before memo = .done result after saved)
    (good : Good (width := width) before) (available : Values before.native.machine.heap values) :
    Effect before after ∧ Available after.native.machine.heap result ∧ saved = memo := by
  obtain ⟨heap,graph,rfl,rfl⟩ := SourceCurrentAllocatedTargetWorkerSound.projection_sound p h path values before memo result after saved actual
  exact ⟨(forest graph good available).1,(forest graph good available).2,rfl⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem merge {m s input before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.merge m s input before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Available before.native.machine.heap input) :
    Effect before after ∧ Stored after.native.machine.heap saved ∧ Available after.native.machine.heap result := by
  have graph := SourceCurrentAllocatedTargetWorkerSound.merge_sound m s input before memo result after saved actual
  cases graph with
  | done call =>
    obtain ⟨effects,stored,available,_⟩ := call.verified good.physical stored available
    exact ⟨advanced good effects,stored,available⟩

/-- Completed operands derive every actual projection and allocated merge invariant. -/
theorem operand {p h m s path values before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.operand p h m s path values before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap saved ∧ Available after.native.machine.heap result := by
  obtain ⟨value,middle,current,first,last⟩ := (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
  obtain ⟨effect,known,rfl⟩ := projection first good available
  obtain ⟨remaining,retained,returned⟩ := merge last effect.good (stored.grows effect.keeps) known
  exact ⟨effect.trans remaining,retained,returned⟩

private theorem query {n left right before result after}
    (actual : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done result after)
    (good : Good (width := width) before) (first : Available before.native.machine.heap left)
    (second : Available before.native.machine.heap right) : Effect before after ∧ Available after.native.machine.heap result := by
  have ready : SourceRecursiveIntersectionThunks.NodeReady before.native.machine
      ⟨IntersectionEmptyDomain.emptyDomain,left,right⟩ := ⟨True.intro,first,second⟩
  obtain ⟨final,_,keeps,growth,available⟩ := SourceCurrentNativeOperationHeap.node n _ before after result good ready actual
  exact ⟨⟨final,keeps,growth⟩,available⟩

private theorem target_leaf {n left right before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.leaf n left right before memo = .done result after saved)
    (good : Good (width := width) before) (first : Available before.native.machine.heap left)
    (second : Available before.native.machine.heap right) :
    Effect before after ∧ Available after.native.machine.heap result ∧ saved = memo := by
  cases observed : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) before with
  | done value checked =>
    simp only [SourceCurrentAllocatedTargetWorker.leaf,observed] at actual
    cases actual
    exact ⟨(query observed good first second).1,(query observed good first second).2,rfl⟩
  | yielded | failed | constraintError | blocked => simp only [SourceCurrentAllocatedTargetWorker.leaf,observed] at actual; cases actual

private theorem target_fold {p h m s n values seed paths before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.fold p h m s n values seed paths before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap saved ∧ Available after.native.machine.heap result := by
  induction paths generalizing before memo result after saved with
  | nil => exact operand actual good stored available
  | cons path paths ih =>
    obtain ⟨head,middle,current,first,later⟩ := (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp actual
    obtain ⟨headEffect,headStored,headAvailable⟩ := operand first good stored available
    obtain ⟨tail,final,completed,rest,last⟩ := (SourceCurrentAllocatedTargetWorkerSound.bind_done _ _ result after saved).mp later
    obtain ⟨tailEffect,tailStored,tailAvailable⟩ := ih rest headEffect.good headStored
      (fun value member => headEffect.keeps.available value (available value member))
    obtain ⟨lastEffect,lastAvailable,rfl⟩ := target_leaf last tailEffect.good
      (tailEffect.keeps.available _ headAvailable) tailAvailable
    exact ⟨(headEffect.trans tailEffect).trans lastEffect,tailStored.grows lastEffect.keeps,lastAvailable⟩

/-- Every completed target derives full physical validity from its initial forest and merge entries. -/
theorem target {p h m s n values paths before memo result after saved}
    (actual : SourceCurrentAllocatedTargetWorker.target p h m s n values paths before memo = .done result after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) :
    Effect before after ∧ Stored after.native.machine.heap saved ∧ Available after.native.machine.heap result := by
  cases paths with
  | nil => cases actual; exact ⟨.refl _ good,stored,empty_available _⟩
  | cons seed paths => exact target_fold actual good stored available

end MicroCFTA.SourceCurrentLowerOperationInvariants
