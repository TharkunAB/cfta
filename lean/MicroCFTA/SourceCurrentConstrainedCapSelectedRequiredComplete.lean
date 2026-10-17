import MicroCFTA.SourceCurrentConstrainedCapSelectedRequired
import MicroCFTA.SourceCurrentConstrainedCapOperandFrame
import MicroCFTA.SourceCurrentConjunctionRequiredGlobalMemos
import MicroCFTA.SourceCurrentAllocatedProbeRequired
import MicroCFTA.SourceCurrentAllocatedPartialInvariant

/-!
# Initial selected Required execution with full Frames and local caps

Original false primary certificates construct the actual Required return.
The same execution supplies global reads, the full returned query Frame,
and local caps. Open unselected siblings remain permitted. This theorem
does not yet give an initial numeric forecast for the Required prefix.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapSelectedRequiredComplete
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

/-- Initial primary certificates construct Required, its full Frame, global effect, and finite output caps. -/
theorem complete (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained reaches : Value Symbol Guard → Bool)
    (selected : EqualityNormalize.Constraints) (values : List (Value Symbol Guard)) (before : Checked width)
    (frame : Frame formulas solver inventory before) (available : Values before.native.machine.heap values)
    (proper : ∀ path ∈ selected.flatten, path ≠ [])
    (primary : ∀ paths ∈ selected, EndpointStatefulGateTrace.ClassTrace unconstrained reaches values paths
      before.native.machine.heap false before.native.machine.heap)
    (caps : ∀ value ∈ values, Cap depth value) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results heap final fuel readFuel,
      SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected values results before
        (advanceHeap before heap) ∧
      SourceCurrentRequiredQueryMemos.RequireAllReads (SourceEqualitySelectedRequired.paths selected)
        values results before.native.machine.heap heap memos final ∧
      Frame formulas solver inventory (advanceHeap before heap) ∧
      SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap heap memos final ∧
      (∀ value ∈ results, Cap depth value) ∧ results.length = values.length ∧
      SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
        values before.native.machine.heap = .done results heap := by
  obtain ⟨results, heap, required⟩ := SourceCurrentConjunctionRequired.required_complete
    formulas solver inventory unconstrained reaches selected values before frame.ready frame.admitted available proper primary
  obtain ⟨fuel, readFuel, stable⟩ := required.stable
  have done := stable fuel readFuel (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨final, reads, finalValid, retained, query⟩ := SourceCurrentRequiredQueryMemos.requireAll_memos
    fuel readFuel (SourceEqualitySelectedRequired.paths selected) values results before.native.machine.heap heap done
      frame.ready.semantic frame.ready.costs available memos valid
  have produced := SourceCurrentConstrainedCapSelectedRequired.requireAll Plain depth reads frame.ready.semantic
    frame.ready.costs available frame.context.guards caps
  have returned := SourceCurrentConstrainedCapOperandFrame.advance frame required.ready required.extension
    required.nodes required.edges produced.1
  exact ⟨results, heap, final, fuel, readFuel, required, reads, returned,
    ⟨required.effects.keeps, required.ready.semantic, required.ready.costs, finalValid, retained, query⟩,
    produced.2.1, produced.2.2, done⟩

/-- The constructed Required prefix retains the complete caller and both unchanged outer tables. -/
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
    ∃ results heap final fuel readFuel,
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
      SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
        values before.checked.native.machine.heap = .done results heap := by
  obtain ⟨results, heap, final, fuel, readFuel, required, reads, returned, globals, bounded, length, done⟩ :=
    complete depth formulas solver inventory unconstrained reaches selected values before.checked frame available
      proper primary caps memos initial.globals
  have probes := SourceCurrentAllocatedProbeRequired.requireAll fuel readFuel
    (SourceEqualitySelectedRequired.paths selected) values results before.checked.native.machine.heap heap done
    initial.ready.semantic initial.ready.costs initial.probes available
  have post : Post formulas solver inventory before
      (advance before (advanceHeap before.checked heap) before.fourth before.merge) final :=
    ⟨⟨required.ready, required.admitted,
      initial.sound.advance formulas solver _ before.fourth before.merge required.effects,
      initial.stored.grows required.effects.keeps, initial.covered,
      SourceCurrentEmptinessMemo.grows formulas solver required.effects.keeps before.fourth initial.correct,
      globals.valid, probes.2.2.2.1⟩, required.effects, extends_refl _, fun _ _ found => found⟩
  exact ⟨results, heap, final, fuel, readFuel, required, reads, returned, post,
    bounded, length, rfl, rfl, rfl, rfl, done⟩

end MicroCFTA.SourceCurrentConstrainedCapSelectedRequiredComplete
