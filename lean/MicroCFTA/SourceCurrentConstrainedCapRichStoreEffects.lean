import MicroCFTA.SourceCurrentConstrainedCapSharedSupport
import MicroCFTA.SourceCurrentConstrainedCapEditSupport

/-!
# Rich shared stores through actual constructor and head work

Each result uses the literal returned constructor heap or head heap.
Native returned-cell laws, Merge laws, and captured slot laws stay separate.
Head exposure derives its Mu store from the initial finite cap. No theorem
requires a desired result annotation or a future leaf law.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapRichStoreEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedSharedEditGraph (SharedState advanceHeap)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentConstrainedCapSharedSupport.Stored
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : Inventory} {record : SourceEqualityClassOrder.Record}
variable {originals : List (Value Symbol Guard)} {base : Heap} {before : SharedState width}

/-- Actual node work retains rich stores, readiness, and availability at its exact output heap. -/
theorem node (ready : Ready formulas solver inventory record originals base before)
    (edges : List (EdgeValue Symbol Guard)) (resident : Edges before.checked.native.machine.heap edges)
    (stored : Stored record originals before) :
    let actual := run (makeNode edges) before.checked.native.machine.heap
    Stored record originals (advanceHeap before actual.2) ∧
      Ready formulas solver inventory record originals base (advanceHeap before actual.2) ∧
      Effects (physical before.checked) (physical (advanceHeap before actual.2).checked) ∧
      Available actual.2 actual.1 := by
  have physical := SourceCurrentAllocatedSharedEditEffects.node_physical ready edges resident
  have retained := SourceCurrentConstrainedCapSharedSupport.advance_heap_stored before
    (run (makeNode edges) before.checked.native.machine.heap).2 stored (stored.native.constructors.makeNode edges)
  exact ⟨retained, physical⟩

/-- Actual raw edge work retains its complete guard, ordered children, and every rich store. -/
theorem edge (ready : Ready formulas solver inventory record originals base before)
    (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard))
    (field : SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations guard)
    (available : Values before.checked.native.machine.heap children) (stored : Stored record originals before) :
    let actual := run (makeEdge symbol guard children) before.checked.native.machine.heap
    Stored record originals (advanceHeap before actual.2) ∧
      Ready formulas solver inventory record originals base (advanceHeap before actual.2) ∧
      Effects (physical before.checked) (physical (advanceHeap before actual.2).checked) ∧
      InternedEdgeResidency.EdgeResident actual.2 actual.1 ∧ actual.1.children = children := by
  have physical := SourceCurrentAllocatedSharedEditEffects.edge_physical ready symbol guard children field available
  have retained := SourceCurrentConstrainedCapSharedSupport.advance_heap_stored before
    (run (makeEdge symbol guard children) before.checked.native.machine.heap).2 stored
    (stored.native.constructors.makeEdge symbol guard children)
  exact ⟨retained, physical⟩

/-- Actual head exposure retains all path masks and derives the returned rich store from its finite-cap input. -/
theorem head (capDepth : Nat) (ready : Ready formulas solver inventory record originals base before)
    {input exposed : Value Symbol Guard} {heap : Heap}
    (actual : SourceEqualityRequiredHead.Head input before.checked.native.machine.heap exposed heap)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (bounded : SourceCurrentConstrainedCap.Cap Plain capDepth input) (stored : Stored record originals before) :
    Stored record originals (advanceHeap before heap) ∧
      Ready formulas solver inventory record originals base (advanceHeap before heap) ∧
      Effects (physical before.checked) (physical (advanceHeap before heap).checked) ∧ Available heap exposed ∧
      SourceCurrentConstrainedCap.Cap Plain capDepth exposed ∧
      SourceCurrentConstrainedCapRequiredSupport.Preserves Plain input exposed := by
  have physical := SourceCurrentAllocatedSharedEditEffects.head_physical ready actual available
  have produced := SourceCurrentConstrainedCapExposure.head Plain capDepth actual
    ready.checked.semantic.ready available closed bounded stored.native.constructors
  have masks := SourceCurrentConstrainedCapEditSupport.head Plain capDepth actual
    ready.checked.semantic.ready available closed bounded stored.native.constructors
  have retained := SourceCurrentConstrainedCapSharedSupport.advance_heap_stored before heap stored produced.1
  exact ⟨retained, physical.1, physical.2.1, physical.2.2, produced.2, masks.2⟩

end MicroCFTA.SourceCurrentConstrainedCapRichStoreEffects
