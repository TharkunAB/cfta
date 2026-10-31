import MicroCFTA.SourceCurrentAllocatedNativeStoredTrace
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources
import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.SourcePruningEnumerationNodes

/-!
# Ordinary results of actual target queries

Empty-seen ordinary operands bound the new result by each operand.
The actual query trace maintains the returned native certificates.
The cold producer derives its entry certificates from the literal initializer.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetResult
open InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "NodeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
variable {width : Nat} [DecidableEq (EdgeKey Symbol Guard)]

/-- An actual target receipt derives the new node, both bounds and its physical handle. -/
theorem receipt_result
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {left right value : Value Symbol Guard} {before after : Checked width} {memos : Memos}
    (ready : SourceCurrentConjunctionClassScan.Ready before) (stored : Stored before.native)
    (leftDomain : NodeDomain left) (rightDomain : NodeDomain right)
    (receipt : SourceCurrentAllocatedTargetQuery.Receipt formulas solver inventory left right before value after memos) :
    Stored after.native ∧ NodeDomain value ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height left ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height right ∧
      ∃ handle, SourcePruningEnumerationNodes.encodeNode value = some handle ∧
        SourcePruningEnumerationNodes.lookupNode after.native.machine.heap handle = some value := by
  have result : Stored after.native ∧ NodeDomain value ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height left ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height right := by
    cases receipt.actual with
    | run trace =>
        exact SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace
          ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ _ _ _ _ trace
          ready.good ready.semantic stored ⟨rfl, leftDomain, rightDomain⟩
  obtain ⟨handle, encoded, decoded⟩ := SourcePruningEnumerationNodes.available_readback
    after.native.machine.heap value receipt.ready.good.native.machine.1.coherent receipt.available receipt.closed
  exact ⟨result.1, result.2.1, result.2.2.1, result.2.2.2, handle, encoded, decoded⟩

/-- A query step derives its actual new result and retains the entry structural certificates. -/
theorem finite_result (bits : Nat) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (left right : Value Symbol Guard) (before : Checked (bits + 2))
    (ready : SourceCurrentConjunctionClassScan.Ready before) (admitted : At formulas solver inventory before)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile before) (room : Room bits profile)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (stored : Stored before.native) (leftDomain : NodeDomain left) (rightDomain : NodeDomain right) :
    ∃ next : Inventory, ∃ value after,
      next.source = before.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right before value after memos ∧
      Stored after.native ∧ NodeDomain value ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height left ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height right ∧
      ∃ handle, SourcePruningEnumerationNodes.encodeNode value = some handle ∧
        SourcePruningEnumerationNodes.lookupNode after.native.machine.heap handle = some value := by
  have actualRoom := fits.room room
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left before.native.machine.heap
    ready.good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right before.native.machine.heap
    ready.good.native.machine.1.coherent rightAvailable rightClosed
  have ranges := (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before
    ready.good ready.semantic left right leftOriginal rightOriginal leftAvailable rightAvailable
    actualRoom.1 actualRoom.2.1 actualRoom.2.2).1
  obtain ⟨next, value, after, source, roots, receipt⟩ := SourceCurrentAllocatedTargetQuery.finite
    formulas solver inventory left right before ready admitted leftAvailable rightAvailable
    leftClosed rightClosed ranges memos valid
  exact ⟨next, value, after, source, roots, receipt, receipt_result ready stored leftDomain rightDomain receipt⟩

/-- Literal empty native initialization supplies the first query without a Stored input. -/
theorem initial_finite_result (bits : Nat) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (heap : State Symbol Guard)
    (left right : Value Symbol Guard)
    (ready : SourceCurrentConjunctionClassScan.Ready (SourceCurrentAllocatedPartialInitialization.checked (bits + 2) cache heap))
    (admitted : At formulas solver inventory (SourceCurrentAllocatedPartialInitialization.checked (bits + 2) cache heap))
    (leftAvailable : Available heap left) (rightAvailable : Available heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile
      (SourceCurrentAllocatedPartialInitialization.checked (bits + 2) cache heap)) (room : Room bits profile)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid heap memos)
    (leftDomain : NodeDomain left) (rightDomain : NodeDomain right) :
    ∃ next : Inventory, ∃ value after,
      next.source = heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right
        (SourceCurrentAllocatedPartialInitialization.checked (bits + 2) cache heap) value after memos ∧
      Stored after.native ∧ NodeDomain value ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height left ∧
      MergedOrdinaryHeight.height value ≤ MergedOrdinaryHeight.height right ∧
      ∃ handle, SourcePruningEnumerationNodes.encodeNode value = some handle ∧
        SourcePruningEnumerationNodes.lookupNode after.native.machine.heap handle = some value := by
  have stored : Stored (SourceCurrentAllocatedPartialInitialization.checked (bits + 2) cache heap).native :=
    SourceCurrentAllocatedFiniteOrdinaryStored.initial_stored (bits + 2) ⟨heap, Cache.emptyState⟩
  exact finite_result bits profile formulas solver inventory left right
    (SourceCurrentAllocatedPartialInitialization.checked (bits + 2) cache heap)
    ready admitted leftAvailable rightAvailable leftClosed rightClosed fits room memos valid stored leftDomain rightDomain

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryTargetResult
