import MicroCFTA.SourcePruningEnumerationSelectedValueProjectionHeap
import MicroCFTA.SourcePruningEnumerationSelectedPreparationIdentification

/-!
# Projectability at the actual selected preparation endpoint

The original packet realizes the stored source handle.
The actual preparation result fixes the returned physical heap.
Every row of a completed prepared node has a supported projection.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedPreparation
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap projectable
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The original packet and actual preparation row retain projection at every observed endpoint. -/
theorem run_projectable_heap
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller width} {memos : Memos} {metadata : SourcePruningRecordTypes.Metadata Typing}
    {before : Cached} {entryFuel nativeFuel uv handle : Nat} {scs : List Suspended}
    {decoded : Node} {entered : Core} {outcome : MergedSourceComparison.Result Symbol Constraint Node}
    (packet : Packet formulas solver inventory caller memos metadata before)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decodedLookup : lookupNode caller.checked.native.machine.heap handle = some decoded)
    (actual : run entryFuel nativeFuel uv caller before =
      ([.ok ((uv, handle, scs, decoded), entered)], some outcome))
    (heap : ProjectionHeap caller.checked.native.machine.heap) : ProjectionHeap outcome.state := by
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  obtain ⟨value, valueLookup, available, closed⟩ := realized uv handle scs stored
  have same : value = decoded := Option.some.inj (valueLookup.symm.trans decodedLookup)
  subst value
  have entryRun : ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
      entryFuel uv before.core) = [.ok ((uv, handle, scs, decoded), entered)] := by
    simpa only [run] using congrArg Prod.fst actual
  have nativeRun : SourcePruningEnumerationSelectedValue.run nativeFuel decoded
      caller.checked.native.machine.heap = outcome := by
    have next := congrArg Prod.snd actual
    simpa only [run, entryRun, Option.some.injEq] using next
  have retained := SourcePruningEnumerationSelectedValue.run_projectable_heap nativeFuel decoded
    caller.checked.native.machine.heap packet.context.ready.semantic.ready available closed heap
  simpa only [nativeRun] using retained

/-- Stable completed preparation retains projection at its own physical heap. -/
theorem complete_projectable_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (bound : Nat) (decoded result : Node)
    (after : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (running : ∀ extra, run (bound + extra) (bound + extra) uv caller before =
      ([.ok ((uv, handle, scs, decoded), entered)], some (.done result after)))
    (heap : ProjectionHeap caller.checked.native.machine.heap) : ProjectionHeap after := by
  have identified := identify_complete formulas solver inventory caller memos metadata before uv handle scs
    packet ready stored bound decoded result after entered running
  exact run_projectable_heap packet stored identified.2.1 (running 0) heap

/-- The actual completed prepared node derives projection support for every stored row. -/
theorem complete_rows_projectable
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (bound : Nat) (decoded : Node) (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (after : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (running : ∀ extra, run (bound + extra) (bound + extra) uv caller before =
      ([.ok ((uv, handle, scs, decoded), entered)], some (.done (.node parentEntry rows depth free) after)))
    (heap : ProjectionHeap caller.checked.native.machine.heap) :
    ∀ edge ∈ rows, SourcePruningEnumerationConstraint.project edge.entry.key.constraint ≠ none := by
  obtain ⟨_running, _lookup, post, _packet, _stable, _ready, _stored, _counter, _values,
    _flags, _waiting, available, _closed, _language, _model⟩ :=
    identify_complete formulas solver inventory caller memos metadata before uv handle scs
      packet ready stored bound decoded (.node parentEntry rows depth free) after entered running
  have returned := complete_projectable_heap formulas solver inventory caller memos metadata before uv handle scs
    packet ready stored bound decoded (.node parentEntry rows depth free) after entered running heap
  have annotated := SourceEqualityAnnotationHeap.available projectable after returned
    post.context.ready.semantic.ready.semantic.1.normal.facts.linked
    (.node parentEntry rows depth free) available
  cases annotated with
  | node _ _ _ _ guards _ => exact guards

end MicroCFTA.SourcePruningEnumerationSelectedPreparation
