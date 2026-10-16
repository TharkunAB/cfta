import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardProjection
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeGuardFinite
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardExecution
import MicroCFTA.SourceCurrentAllocatedTargetComplete

/-!
# Hereditary guard bounds through actual target folds

An operand projects the original forest and merges its actual return.
Each native query runs after the exact recursive tail return.
The bound charges one conjunction step per actual fold query.
Both universal certificate tables pass through those same states.
These results verify supplied reads. They do not assert target completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardTarget
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedTargetGraph SourceCurrentAllocatedTargetComplete
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "Le" => SourceCurrentAllocatedFiniteOrdinaryGuardLimits.Le
local notation "step" => SourceCurrentAllocatedFiniteOrdinaryGuardLimits.step
local notation "Node" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "Children" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children

/-- The fold charges one native guard step after each actual tail return. -/
def foldLimit (limits : Limits) : Nat → Limits
  | 0 => limits
  | count + 1 => step (foldLimit limits count)

/-- Every later fold envelope retains the original forest envelope. -/
theorem foldLimit_ge (limits : Limits) (count : Nat) : Le limits (foldLimit limits count) := by
  induction count with
  | zero => exact SourceCurrentAllocatedFiniteOrdinaryGuardLimits.le_refl _
  | succ count ih => exact SourceCurrentAllocatedFiniteOrdinaryGuardLimits.le_trans ih
      (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.step_ge _)

/-- A target with n operands has at most n minus one native fold queries. -/
def targetLimit (limits : Limits) (paths : List (List Int)) : Limits := foldLimit limits (paths.length - 1)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The same operand receipt produces hereditary bounds and retains both universal tables. -/
theorem operand_receipt
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {path : List Int}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo result after saved memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (merged : MergeStored memo)
    (native : NativeStored before.native) (limits : Limits) (profile : Children limits values) :
    MergeStored saved ∧ NativeStored after.native ∧ Node limits result := by
  have nativeAfter : NativeStored after.native :=
    ⟨by simpa only [receipt.nodes] using native.nodes, by simpa only [receipt.edges] using native.edges⟩
  obtain ⟨projected, middle, current, projection, mergedReceipt⟩ := receipt.actual
  have projectedBound := SourceCurrentAllocatedFiniteOrdinaryGuardProjection.forest projection.graph
    ready.semantic available profile
  cases mergedReceipt.actual with
  | done call =>
      obtain ⟨_effects, _physical, finalMerged, _available, certificate⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryMergeGuardProducer.call_guard call.graph
          projection.ready.semantic projection.ready.costs (physicalStored.grows projection.effects.keeps)
          merged projection.available
      exact ⟨finalMerged, nativeAfter, certificate limits projectedBound⟩

/-- The exact fold order derives each native query's input bound before that query. -/
theorem fold
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Fold values seed paths before memo result after saved} (reads : FoldReads formulas solver actual memos final) :
    Ready before → Values before.native.machine.heap values → PhysicalStored before.native.machine.heap memo →
      MergeStored memo → NativeStored before.native → ∀ limits, Children limits values →
      Ready after ∧ Effects (physical before) (physical after) ∧ PhysicalStored after.native.machine.heap saved ∧
      MergeStored saved ∧ NativeStored after.native ∧ Available after.native.machine.heap result ∧
      Node (foldLimit limits paths.length) result := by
  induction reads with
  | nil receipt =>
      intro ready available physicalStored merged native limits profile
      have own := operand_receipt receipt ready available physicalStored merged native limits profile
      exact ⟨receipt.ready, receipt.effects, receipt.stored, own.1, own.2.1, receipt.available, own.2.2⟩
  | cons receipt remaining query ih =>
      intro ready available physicalStored merged native limits profile
      have head := operand_receipt receipt ready available physicalStored merged native limits profile
      have tail := ih receipt.ready receipt.originals receipt.stored head.1 head.2.1 limits profile
      have left := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node.mono _ head.2.2
        (foldLimit_ge limits _)
      cases query.actual with
      | run trace =>
          have checked := SourceCurrentAllocatedFiniteOrdinaryGuardExecution.node_trace
            ⟨IntersectionEmptyDomain.emptyDomain, _, _⟩ _ _ _ _ trace tail.1.good tail.1.semantic
            tail.2.2.2.2.1 rfl _ left tail.2.2.2.2.2.2
          exact ⟨query.ready, receipt.effects.trans (tail.2.1.trans query.effects),
            tail.2.2.1.grows query.effects.keeps, tail.2.2.2.1, checked.1, query.available, checked.2⟩

/-- Supplied target reads derive their own hereditary output bound and retain both tables. -/
theorem target_reads
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Target values paths before memo result after saved} (reads : TargetReads formulas solver actual memos final)
    (ready : Ready before) (available : Values before.native.machine.heap values)
    (physicalStored : PhysicalStored before.native.machine.heap memo) (merged : MergeStored memo)
    (native : NativeStored before.native) (limits : Limits) (profile : Children limits values) :
    MergeStored saved ∧ NativeStored after.native ∧ Node (targetLimit limits paths) result := by
  cases reads with
  | nil => exact ⟨merged, native, True.intro⟩
  | cons reads =>
      have checked := fold reads ready available physicalStored merged native limits profile
      exact ⟨checked.2.2.2.1, checked.2.2.2.2.1, checked.2.2.2.2.2.2⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardTarget
