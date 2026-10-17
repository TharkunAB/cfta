import MicroCFTA.SourceCurrentConstrainedCapMaskCharacterization
import MicroCFTA.SourceCurrentHereditaryNativeUniversalStore
import MicroCFTA.SourceCurrentHereditaryMerge
import MicroCFTA.SourceCurrentConjunctionClassScan
import MicroCFTA.SourceCurrentConjunctionRequired

/-!
# Causal stores and original masks through the actual Required prefix

Required reads change the constructor heap before the class fold.
The native cells and Merge table remain at their exact original values.
Actual constructor reads retain the causal Mu store at the returned heap.
These results verify supplied reads. They do not construct a finite call.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRichRequiredSupport
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapPaths (ForestSupported)
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "NativeStored" => SourceCurrentHereditaryNativeUniversalStore.Stored
local notation "MergeStored" => SourceCurrentHereditaryMerge.Stored

/-- Actual Required reads retain every original mask and both causal tables at the class entry. -/
theorem requireAll [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (depth : Nat) {width : Nat}
    {paths : List (List Int)} {values results : List (Value Symbol Guard)}
    {before : Checked width} {heap : State Symbol Guard} {memo : Memo} {memos final : Memos}
    (reads : SourceCurrentRequiredQueryMemos.RequireAllReads paths values results before.native.machine.heap heap memos final)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (native : NativeStored annotation before) (merged : MergeStored annotation memo)
    (bounded : ∀ value ∈ values, Cap annotation depth value) :
    NativeStored annotation (SourceCurrentConjunctionClassScan.advanceHeap before heap) ∧
      MergeStored annotation memo ∧ Language.All₂ (Preserves annotation) values results ∧
      (∀ value ∈ results, Cap annotation depth value) ∧
      ∀ path, ForestSupported annotation path values → ForestSupported annotation path results := by
  have actual := SourceCurrentConstrainedCapRequiredSupport.requireAll annotation depth reads
    ready.semantic ready.costs available closed native.constructors bounded
  have advanced : NativeStored annotation (SourceCurrentConjunctionClassScan.advanceHeap before heap) :=
    SourceCurrentHereditaryNativeUniversalStore.advance annotation before
      {before.native.machine with heap := heap} native actual.1
  exact ⟨advanced, merged, actual.2, SourceCurrentConstrainedCapMaskCharacterization.children_cap actual.2 bounded,
    fun path supported => SourceCurrentConstrainedCapRequiredSupport.forest_supported annotation actual.2 path supported⟩

/-- The same selected Required receipt retains its full old conclusion and the rich class-entry laws. -/
theorem receipt [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (depth : Nat) {width : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory} {selected : EqualityNormalize.Constraints}
    {values results : List (Value Symbol Guard)} {before : Checked width} {heap : State Symbol Guard}
    {memo : Memo} {memos final : Memos}
    (actual : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before
      (SourceCurrentConjunctionClassScan.advanceHeap before heap))
    (reads : SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
      values results before.native.machine.heap heap memos final)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (native : NativeStored annotation before) (merged : MergeStored annotation memo)
    (bounded : ∀ value ∈ values, Cap annotation depth value) :
    SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before
        (SourceCurrentConjunctionClassScan.advanceHeap before heap) ∧
      NativeStored annotation (SourceCurrentConjunctionClassScan.advanceHeap before heap) ∧
      MergeStored annotation memo ∧ Language.All₂ (Preserves annotation) values results ∧
      (∀ value ∈ results, Cap annotation depth value) ∧
      ∀ path, ForestSupported annotation path values → ForestSupported annotation path results :=
  ⟨actual, requireAll annotation depth reads ready available closed native merged bounded⟩

end MicroCFTA.SourceCurrentConstrainedCapRichRequiredSupport
