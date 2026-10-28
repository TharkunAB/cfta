import MicroCFTA.SourcePruningEnumerationSelectedValueArity
import MicroCFTA.SourcePruningEnumerationSelectedPreparationIdentification

/-!
# Original arity at the actual selected preparation endpoint

The original packet realizes the stored source handle.
The actual entry singleton retains that decoded source value.
The actual native outcome determines the returned physical heap.
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
local notation "ArityHeap" => SourcePruningEnumerationArityOrigins.Heap
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The original packet and actual preparation row derive arity at its exact done or failed endpoint. -/
theorem run_heap
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
    (heap : ArityHeap caller.checked.native.machine.heap) : ArityHeap outcome.state := by
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  obtain ⟨value, valueLookup, available, _closed⟩ := realized uv handle scs stored
  have same : value = decoded := Option.some.inj (valueLookup.symm.trans decodedLookup)
  subst value
  have entryRun : ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
      entryFuel uv before.core) = [.ok ((uv, handle, scs, decoded), entered)] := by
    simpa only [run] using congrArg Prod.fst actual
  have nativeRun : SourcePruningEnumerationSelectedValue.run nativeFuel decoded
      caller.checked.native.machine.heap = outcome := by
    have next := congrArg Prod.snd actual
    simpa only [run, entryRun, Option.some.injEq] using next
  have retained := SourcePruningEnumerationSelectedValue.run_heap nativeFuel decoded
    caller.checked.native.machine.heap packet.context.ready.semantic.ready.semantic.1.normal.facts heap available
  simpa only [nativeRun] using retained

/-- The same stable preparation family retains the initial arity at its own completed physical heap. -/
theorem complete_heap
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
    (heap : ArityHeap caller.checked.native.machine.heap) : ArityHeap after := by
  have identified := identify_complete formulas solver inventory caller memos metadata before uv handle scs
    packet ready stored bound decoded result after entered running
  exact run_heap packet stored identified.2.1 (running 0) heap

end MicroCFTA.SourcePruningEnumerationSelectedPreparation
