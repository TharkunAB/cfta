import MicroCFTA.SourceCurrentConstrainedCapSelectedRequiredComplete
import MicroCFTA.SourceCurrentRequiredWorkerNumeric

/-!
# Initial selected Required at a trie-only worker bound

The original primary certificates construct the full Required return.
The same return executes at the worker bound from its initial Needed trie.
Reader fuel remains existential. Initial numeric heap Fits remains open.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapSelectedRequiredWorker
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap
local notation "advance" => SourceCurrentAllocatedPartialState.advance
variable {width : Nat} [DecidableEq (EdgeKey Symbol Guard)]

/-- Original certificates construct the same full Required receipt at every sufficient trie-only worker bound. -/
theorem complete (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Checked width)
    (frame : Frame formulas solver inventory before) (available : Values before.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap false before.native.machine.heap)
    (caps : ∀ value ∈ values, Cap depth value) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results heap final readFuel,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before
        (advanceHeap before heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before heap) ∧
      SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap heap memos final ∧
      (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
      (∀ worker reader,
        SourceCurrentRequiredWorkerNumeric.workFuel (SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected)) ≤ worker →
        readFuel ≤ reader → SourceEqualityRequiredExecution.requireAll worker reader (SourceEqualitySelectedRequired.paths selected)
          values before.native.machine.heap = .done results heap) := by
  obtain ⟨results, heap, final, fuel, oldRead, required, reads, returned, globals, bounded, length, done⟩ :=
    SourceCurrentConstrainedCapSelectedRequiredComplete.complete depth formulas solver inventory unconstrained reaches
      selected values before frame available proper primary caps memos valid
  obtain ⟨readFuel, stable⟩ := SourceCurrentRequiredWorkerNumeric.requireAll fuel oldRead
    (SourceEqualitySelectedRequired.paths selected) values results before.native.machine.heap heap done
    frame.ready.semantic frame.ready.costs available
  exact ⟨results, heap, final, readFuel, required, reads, returned, globals, bounded, length, stable⟩

/-- The initial caller retains all tables and laws at the same trie-only worker bound. -/
theorem caller (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Caller width)
    (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.checked.native.machine.heap false before.checked.native.machine.heap)
    (caps : ∀ value ∈ values, Cap depth value) :
    ∃ results heap final readFuel,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before.checked
        (advanceHeap before.checked heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.checked.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before.checked heap) ∧
      Post formulas solver inventory before (advance before (advanceHeap before.checked heap) before.fourth before.merge) final ∧
      (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).nodeResults = before.nodeResults ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).edgeResults = before.edgeResults ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).fourth = before.fourth ∧
      (advance before (advanceHeap before.checked heap) before.fourth before.merge).merge = before.merge ∧
      (∀ worker reader,
        SourceCurrentRequiredWorkerNumeric.workFuel (SourceEqualityNeeded.build (SourceEqualitySelectedRequired.paths selected)) ≤ worker →
        readFuel ≤ reader → SourceEqualityRequiredExecution.requireAll worker reader (SourceEqualitySelectedRequired.paths selected)
          values before.checked.native.machine.heap = .done results heap) := by
  obtain ⟨results, heap, final, fuel, oldRead, required, reads, returned, post, bounded, length,
      nodes, edges, fourth, merged, done⟩ :=
    SourceCurrentConstrainedCapSelectedRequiredComplete.caller depth formulas solver inventory unconstrained reaches
      selected values before memos initial frame available proper primary caps
  obtain ⟨readFuel, stable⟩ := SourceCurrentRequiredWorkerNumeric.requireAll fuel oldRead
    (SourceEqualitySelectedRequired.paths selected) values results before.checked.native.machine.heap heap done
    frame.ready.semantic frame.ready.costs available
  exact ⟨results, heap, final, readFuel, required, reads, returned, post, bounded, length,
    nodes, edges, fourth, merged, stable⟩

end MicroCFTA.SourceCurrentConstrainedCapSelectedRequiredWorker
