import MicroCFTA.SourceSynthesisNativeTypeSharedState
import MicroCFTA.SourceCurrentAllocatedSharedEditGraph
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceCurrentHereditaryExposure

/-!
# Constructor and head work at shared Type states

Actual heap work retains native tables, operations, target slots and Merge
memo entries. Constructor work preserves the causal Mu store independently
of Program guards. Recursive exposure uses its input Type annotation and
the actual conditional store. No language inventory is an input.
-/
namespace MicroCFTA.SourceSynthesisNativeTypeSharedHeap
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceSynthesisTypeSyntax (Library)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceSynthesisNativeTypeTrace (Origin)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentAllocatedSharedEditGraph (advanceHeap)
open SourceCurrentAllocatedNativeEffects (physical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {width : Nat}

private theorem advance (lib : Library) (before : Shared width) (heap : Heap)
    (ready : Ready lib before)
    (effects : Effects (SourceCurrentAllocatedNativeEffects.physical before.checked) ⟨heap, before.checked.operations⟩)
    (stored : SourceCurrentHereditaryConstruction.MuStored (Origin lib) heap) :
    Ready lib (advanceHeap before heap) ∧
      Extension before.checked.native.machine (advanceHeap before heap).checked.native.machine := by
  have nativeStore := SourceCurrentHereditaryNativeUniversalStore.advance (Origin lib) before.checked
    {before.checked.native.machine with heap := heap} ready.checked.stored stored
  have nextReady : SourceSynthesisNativeTypeClosedRequests.Ready lib
      (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩) :=
    ⟨SourceCurrentAllocatedConjunctionMemo.advance_good before.checked _ ready.checked.good effects,
      effects.ready.semantic,
      SourceCurrentAllocatedConjunctionMemo.advance_scoped before.checked _ ready.checked.scopes,
      SourceCurrentAllocatedConjunctionMemo.advance_idle before.checked _ ready.checked.idle, nativeStore⟩
  have extension := SourceCurrentAllocatedQueryMemo.advance_extension before.checked _ effects
  exact ⟨SourceSynthesisNativeTypeSharedState.advance lib before _ ready nextReady effects.ready.costs extension,
    extension⟩

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual node construction retains the shared facts and returns a closed available node. -/
theorem node (lib : Library) {before : Shared width} {edges : List (EdgeValue Symbol Guard)}
    {result : Value Symbol Guard} {heap : Heap}
    (actual : run (makeNode edges) before.checked.native.machine.heap = (result, heap))
    (ready : Ready lib before) (resident : Edges before.checked.native.machine.heap edges)
    (closed : ClosedEdges edges) :
    Ready lib (advanceHeap before heap) ∧
      Extension before.checked.native.machine (advanceHeap before heap).checked.native.machine ∧
      Available heap result ∧ result.free = [] := by
  have physical := SourceCurrentRequiredHeapEffects.node_constructor
    (SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations) edges before.checked.native.machine.heap
    ready.checked.semantic ready.costs ready.checked.good.fields resident
  have effects : Effects (SourceCurrentAllocatedNativeEffects.physical before.checked)
      ⟨(run (makeNode edges) before.checked.native.machine.heap).2, before.checked.operations⟩ :=
    ⟨physical.1, ⟨physical.2.1, physical.2.2.1, ready.checked.good.operations, physical.2.2.2.1⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  have next := advance lib before _ ready effects (ready.checked.stored.constructors.makeNode edges)
  have resultClosed := MergedColdReaderClosedInputs.makeNode_closed edges before.checked.native.machine.heap
    ready.checked.semantic.ready.semantic.1.normal.facts resident closed
  simpa only [actual] using And.intro next.1 (And.intro next.2 (And.intro physical.2.2.2.2 resultClosed))

/-- Actual row reconstruction retains its complete original guard and ordered children. -/
theorem edge (lib : Library) (original : EdgeValue Symbol Guard) (values : List (Value Symbol Guard))
    {before : Shared width} {result : EdgeValue Symbol Guard} {heap : Heap}
    (actual : run (makeEdge original.entry.key.symbol original.entry.key.constraint values)
      before.checked.native.machine.heap = (result, heap))
    (ready : Ready lib before) (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap original)
    (available : Values before.checked.native.machine.heap values) :
    Ready lib (advanceHeap before heap) ∧
      Extension before.checked.native.machine (advanceHeap before heap).checked.native.machine ∧
      InternedEdgeResidency.EdgeResident heap result ∧ result.children = values ∧
      result.entry.key.constraint = original.entry.key.constraint := by
  have physical := SourceEqualityRequiredCache.edge original.entry.key.symbol original.entry.key.constraint values
    before.checked.native.machine.heap ready.checked.semantic.ready available
  have semantic := SourceEqualityRequiredSemanticCache.edge original.entry.key.symbol original.entry.key.constraint values
    before.checked.native.machine.heap ready.checked.semantic available
  have field := ready.checked.good.fields original.entry.key original resident
  have fields := SourceEqualityAnnotationHeap.run (SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations) _
    (SourceEqualityAnnotationHeap.makeEdge _ original.entry.key.symbol original.entry.key.constraint values field)
    before.checked.native.machine.heap ready.checked.good.fields
  have effects : Effects (SourceCurrentAllocatedNativeEffects.physical before.checked)
      ⟨(run (makeEdge original.entry.key.symbol original.entry.key.constraint values) before.checked.native.machine.heap).2,
        before.checked.operations⟩ :=
    ⟨physical.1, ⟨semantic, ready.costs, ready.checked.good.operations, fields⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  have next := advance lib before _ ready effects
    (ready.checked.stored.constructors.makeEdge original.entry.key.symbol original.entry.key.constraint values)
  have readback := MergedPhysicalGroupEdges.makeEdge_fields before.checked.native.machine.heap
    ready.checked.semantic.ready.semantic.1.normal.facts original.entry.key.symbol original.entry.key.constraint values available
  simpa only [actual] using And.intro next.1
    (And.intro next.2 (And.intro physical.2.1 (And.intro readback.2.2 readback.2.1)))

/-- Actual head exposure derives its closed annotated result from the causal input store. -/
theorem head (lib : Library) {before : Shared width} {input result : Value Symbol Guard} {heap : Heap}
    (actual : SourceEqualityRequiredHead.Head input before.checked.native.machine.heap result heap)
    (ready : Ready lib before) (available : Available before.checked.native.machine.heap input)
    (closed : input.free = []) (annotated : Annotated (Origin lib) input) :
    Ready lib (advanceHeap before heap) ∧
      Extension before.checked.native.machine (advanceHeap before heap).checked.native.machine ∧
      Available heap result ∧ result.free = [] ∧ Annotated (Origin lib) result := by
  have physical := SourceCurrentRequiredHeapEffects.head
    (SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations) actual
    ready.checked.semantic ready.costs ready.checked.good.fields available
  have typed := SourceCurrentHereditaryExposure.head (Origin lib) actual ready.checked.semantic.ready
    available closed annotated ready.checked.stored.constructors
  have checked := actual.verified ready.checked.semantic.ready available closed
  have effects : Effects (SourceCurrentAllocatedNativeEffects.physical before.checked) ⟨heap, before.checked.operations⟩ :=
    ⟨physical.1, ⟨physical.2.1, physical.2.2.1, ready.checked.good.operations, physical.2.2.2.1⟩,
      SourceEqualityConstraintMemoAllocation.grows_refl _⟩
  have next := advance lib before heap ready effects typed.1
  exact ⟨next.1, next.2, physical.2.2.2.2, checked.2.2.1, typed.2⟩

end MicroCFTA.SourceSynthesisNativeTypeSharedHeap
