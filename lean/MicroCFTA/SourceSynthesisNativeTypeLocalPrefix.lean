import MicroCFTA.SourceSynthesisNativeTypeScan
import MicroCFTA.SourceSynthesisNativeTypeSharedState
import MicroCFTA.SourceCurrentAllocatedPrecheck

/-!
# Shared Type facts through the literal local prefix

Precheck retains the native state and changes equality operations. Scan
retains its actual returned native state. Heap extension transports both
warm Merge facts and every earlier target. No cold state replaces a
returned prefix. Input routes and causal guard profiles remain entry facts.
These laws do not construct the actual Scan graph or prove its completion.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeLocalPrefix
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceRecursiveIntersectionKernel (Extension)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The actual precheck receipt retains shared Type facts at its returned operations. -/
theorem precheck (lib : Library)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {original : Guard} {loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula}
    {inherited own : SourceEqualityConstraintAllocation.Value} {branch : SourceEqualityPrecheck.Branch}
    {before : Shared width}
    (actual : SourceCurrentAllocatedPrecheck.Receipt formulas solver inventory original loaded inherited
      before.checked own branch) (ready : Ready lib before) :
    Ready lib (SourceCurrentAllocatedSharedTargetState.advance before
      (SourceCurrentAllocatedPrecheck.state before.checked loaded inherited)) ∧
      Extension before.checked.native.machine
        (SourceCurrentAllocatedPrecheck.state before.checked loaded inherited).native.machine := by
  have next : SourceSynthesisNativeTypeClosedRequests.Ready lib
      (SourceCurrentAllocatedPrecheck.state before.checked loaded inherited) :=
    ⟨actual.ready.good, actual.ready.semantic, ready.checked.scopes, ready.checked.idle,
      ⟨ready.checked.stored.constructors, ready.checked.stored.native⟩⟩
  exact ⟨SourceSynthesisNativeTypeSharedState.advance lib before _ ready next ready.costs actual.extension,
    actual.extension⟩

variable [DecidableEq (Value Symbol Guard)]

/-- The same Scan return transports both warm Merge stores and all historical targets. -/
theorem scan (lib : Library) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {budget : Nat} {unconstrained reaches : Value Symbol Guard → Bool}
    {values : List (Value Symbol Guard)} {classes selected : EqualityNormalize.Constraints}
    {before : Shared width} {after : Checked width} {memo saved : SourceCurrentEmptinessMemo.Memo}
    {outcome : Option EqualityNormalize.Class}
    (actual : SourceCurrentConjunctionClassScan.Scan budget unconstrained reaches values classes
      before.checked memo outcome selected after saved)
    (ready : Ready lib before) (available : Values before.checked.native.machine.heap values)
    (closed : ClosedValues values)
    (routes : ∀ paths ∈ classes, ∀ path ∈ paths, ForestPath (Origin lib) (path.map Int.ofNat) values)
    (guards : GuardHeap (Origin lib) before.checked.native.machine.heap) :
    Ready lib (SourceCurrentAllocatedSharedTargetState.advance before after) ∧
      Extension before.checked.native.machine after.native.machine ∧
      GuardHeap (Origin lib) after.native.machine.heap ∧ Values after.native.machine.heap values := by
  obtain ⟨next, costs, extension, retained, known⟩ := SourceSynthesisNativeTypeScan.scan lib formulas solver actual
    ready.checked ready.costs available closed routes guards
  exact ⟨SourceSynthesisNativeTypeSharedState.advance lib before after ready next costs extension,
    extension, retained, known⟩

end MicroCFTA.SourceSynthesisNativeTypeLocalPrefix
