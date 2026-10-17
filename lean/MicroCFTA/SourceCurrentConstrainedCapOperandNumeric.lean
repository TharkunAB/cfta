import MicroCFTA.SourceCurrentProjectionNumeric
import MicroCFTA.SourceCurrentMemoMergeUniformNumeric
import MicroCFTA.SourceCurrentConstrainedCapOperandFrame

/-!
# Complete selected Operand resources from the initial checked state

Projection runs before Merge at its exact returned checked state. Initial
forest and path data determine both schedules. The same actual Operand
retains its full receipt, native cells, global memos, and query Frame.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapOperandNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame)
open SourceCurrentMemoMergeResourceControl (Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable {width : Nat}

/-- The initial forest count and signed path bound the actual projected heap. -/
def projectionBound (path : List Int) (count resource : Nat) : Nat :=
  SourceCurrentProjectionInitialResources.forestBound path count resource

/-- The same initial forecast bounds Merge without inspecting its future projected argument. -/
def workFuel (path : List Int) (count resource : Nat) : Nat :=
  SourceCurrentMemoMergeUniformNumeric.workFuel (projectionBound path count resource)

/-- The initial Merge ceiling supplies all nested selections. -/
def selectionFuel (path : List Int) (count resource : Nat) : Nat :=
  SourceCurrentMemoMergeUniformNumeric.selectionFuel (projectionBound path count resource)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial selected support constructs the complete Operand, both numeric schedules, and its full Frame. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (path : List Int) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (resource : Nat) (frame : Frame formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domain : Domain path values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (fits : Fits resource before.native.machine.heap) :
    ∃ result after saved final,
      SourceCurrentAllocatedTargetGraph.Operand path values before memo result after saved ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values before memo result after saved memos final ∧
      Frame formulas solver inventory after ∧
      Fits (workFuel path values.length resource) after.native.machine.heap ∧
      InternedValueMass.value result ≤ workFuel path values.length resource ∧
      ∃ projected middle current,
        SourceCurrentConjunctionTargetProjection.Receipt formulas solver inventory path values before projected middle memos current ∧
        SourceCurrentAllocatedMerge.Receipt formulas solver inventory SourceCurrentAllocatedMerge.literalClear
          projected middle memo result after saved current final ∧
        Fits (projectionBound path values.length resource) middle.native.machine.heap ∧
        SourceEqualityProjectionWorker.forest (SourceCurrentProjectionNumeric.workFuel path)
          (SourceCurrentProjectionNumeric.readFuel path values.length resource)
          path values before.native.machine.heap = .done projected middle.native.machine.heap ∧
        SourceCurrentMemoMergeWorker.call SourceCurrentAllocatedMerge.literalClear top
          (workFuel path values.length resource) (selectionFuel path values.length resource)
          projected middle.native.machine.heap memo = .done result after.native.machine.heap saved ∧
        (∀ workExtra readExtra,
          SourceEqualityProjectionWorker.forest (SourceCurrentProjectionNumeric.workFuel path + workExtra)
            (SourceCurrentProjectionNumeric.readFuel path values.length resource + readExtra)
            path values before.native.machine.heap = .done projected middle.native.machine.heap) ∧
        ∀ workExtra selectionExtra,
          SourceCurrentMemoMergeWorker.call SourceCurrentAllocatedMerge.literalClear top
            (workFuel path values.length resource + workExtra) (selectionFuel path values.length resource + selectionExtra)
            projected middle.native.machine.heap memo = .done result after.native.machine.heap saved := by
  obtain ⟨result, after, saved, final, actual, receipt, returned⟩ :=
    SourceCurrentConstrainedCapOperandFrame.complete formulas solver inventory path values before memo
      frame available domain physicalStored covered memos valid
  obtain ⟨projected, middle, current, projection, merged⟩ := receipt.actual
  have first := SourceCurrentProjectionNumeric.of_forest projection.graph resource frame.ready.semantic
    frame.ready.costs available domain fits
  have last :
      SourceCurrentMemoMergeWorker.call SourceCurrentAllocatedMerge.literalClear top
        (workFuel path values.length resource) (selectionFuel path values.length resource)
        projected middle.native.machine.heap memo = .done result after.native.machine.heap saved ∧
      Fits (workFuel path values.length resource) after.native.machine.heap ∧
      InternedValueMass.value result ≤ workFuel path values.length resource ∧
      ∀ workExtra selectionExtra,
        SourceCurrentMemoMergeWorker.call SourceCurrentAllocatedMerge.literalClear top
          (workFuel path values.length resource + workExtra) (selectionFuel path values.length resource + selectionExtra)
          projected middle.native.machine.heap memo = .done result after.native.machine.heap saved := by
    cases merged.actual with
    | done call =>
        exact SourceCurrentMemoMergeUniformNumeric.of_call call.graph (projectionBound path values.length resource)
          projection.ready.semantic projection.ready.costs (physicalStored.grows projection.effects.keeps)
          projection.available first.2.1
  exact ⟨result, after, saved, final, actual, receipt, returned, last.2.1, last.2.2.1,
    projected, middle, current, projection, merged, first.2.1, first.1, last.1, first.2.2, last.2.2.2⟩

end MicroCFTA.SourceCurrentConstrainedCapOperandNumeric
