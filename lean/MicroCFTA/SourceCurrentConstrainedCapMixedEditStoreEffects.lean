import MicroCFTA.SourceCurrentConstrainedCapMixedShared
import MicroCFTA.SourceCurrentConstrainedCapProjectionGuard
import MicroCFTA.SourceCurrentConstrainedCapExposure
import MicroCFTA.SourceCurrentAllocatedSharedEditEffects

/-!
# Mixed shared stores through actual constructor and head work

Actual constructor effects retain the slot and Merge certificates. Recursive
head exposure produces its guard heap from the same read. The initial cap
and causal guard heap derive the returned cap at the same finite depth.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapMixedEditStoreEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedSharedEditGraph (SharedState advanceHeap)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentConstrainedCapMixedShared.Stored
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : Inventory} {record : SourceEqualityClassOrder.Record}
variable {originals : List (Value Symbol Guard)} {base : Heap} {before : SharedState width}

private theorem advance_stored (heap : Heap) (stored : Stored record originals before)
    (ready : Ready formulas solver inventory record originals base (advanceHeap before heap))
    (effects : Effects (physical before.checked) (physical (advanceHeap before heap).checked))
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain heap) :
    Stored record originals (advanceHeap before heap) := by
  have current := SourceCurrentConstrainedCapCurrentNative.advance Plain before.checked
    (advanceHeap before heap).checked stored.current ready.checked.good
    ready.checked.semantic.ready.semantic guards
    (SourceCurrentAllocatedQueryMemo.advance_extension before.checked ⟨heap, before.checked.operations⟩ effects) rfl rfl
  exact SourceCurrentConstrainedCapMixedShared.advance_stored record originals before _ stored current

/-- Actual node work retains all mixed stores and the same physical output receipt. -/
theorem node (ready : Ready formulas solver inventory record originals base before)
    (edges : List (EdgeValue Symbol Guard)) (resident : Edges before.checked.native.machine.heap edges)
    (stored : Stored record originals before) :
    let actual := run (makeNode edges) before.checked.native.machine.heap
    Stored record originals (advanceHeap before actual.2) ∧
      Ready formulas solver inventory record originals base (advanceHeap before actual.2) ∧
      Effects (physical before.checked) (physical (advanceHeap before actual.2).checked) ∧
      Available actual.2 actual.1 := by
  have physical := SourceCurrentAllocatedSharedEditEffects.node_physical ready edges resident
  have guards := SourceCurrentConstrainedCapGuardHeap.preserve Plain before.checked.native.machine.heap _
    stored.current.1.guards (InternedShallowHeap.makeNode_noNewMu edges before.checked.native.machine.heap)
  exact ⟨advance_stored _ stored physical.1 physical.2.1 guards, physical⟩

/-- Actual raw edge work retains its exact children, field, and every mixed store. -/
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
  have guards : SourceCurrentConstrainedCapGuardHeap.Heap Plain
      (run (makeEdge symbol guard children) before.checked.native.machine.heap).2 := stored.current.1.guards
  exact ⟨advance_stored _ stored physical.1 physical.2.1 guards, physical⟩

/-- The SAME actual head produces its guard heap and same-depth cap before the editor resumes. -/
theorem head (capDepth : Nat) (ready : Ready formulas solver inventory record originals base before)
    {input exposed : Value Symbol Guard} {heap : Heap}
    (actual : SourceEqualityRequiredHead.Head input before.checked.native.machine.heap exposed heap)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (bounded : SourceCurrentConstrainedCap.Cap Plain capDepth input) (stored : Stored record originals before) :
    Stored record originals (advanceHeap before heap) ∧
      Ready formulas solver inventory record originals base (advanceHeap before heap) ∧
      Effects (physical before.checked) (physical (advanceHeap before heap).checked) ∧ Available heap exposed ∧
      SourceCurrentConstrainedCap.Cap Plain capDepth exposed := by
  have physical := SourceCurrentAllocatedSharedEditEffects.head_physical ready actual available
  have guards := SourceCurrentConstrainedCapProjectionGuard.head Plain actual ready.checked.semantic ready.checked.costs
    available stored.current.1.guards
  have produced := SourceCurrentConstrainedCapExposure.head Plain capDepth actual ready.checked.semantic.ready
    available closed bounded
    (SourceCurrentConstrainedCapGuardNative.stored Plain before.checked.native.machine.heap stored.current.1.guards)
  exact ⟨advance_stored heap stored physical.1 physical.2.1 guards,
    physical.1, physical.2.1, physical.2.2, produced.2⟩

end MicroCFTA.SourceCurrentConstrainedCapMixedEditStoreEffects
