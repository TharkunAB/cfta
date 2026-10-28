import MicroCFTA.SourcePruningEnumerationPreparedPreparationResources

/-!
# Original resources at an actual selected preparation point

The actual entry row identifies the original decoded value.
The same native completion supplies the prepared heap.
Original resource and guard bounds reach that exact endpoint.
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
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- An actual preparation point derives its resource and guard bounds from the original packet. -/
theorem run_resources_known
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller width} {memos : Memos} {metadata : SourcePruningRecordTypes.Metadata Typing}
    {before : Cached} {entryFuel nativeFuel uv handle : Nat} {scs : List Suspended}
    {decoded prepared : Node} {entered : Core} {heap : InternedConstructorTemplates.State Symbol Constraint}
    (packet : Packet formulas solver inventory caller memos metadata before)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decodedLookup : lookupNode caller.checked.native.machine.heap handle = some decoded)
    (actual : run entryFuel nativeFuel uv caller before =
      ([.ok ((uv, handle, scs, decoded), entered)], some (.done prepared heap)))
    (profile : SourceCurrentAllocatedNativeResourceForecast.Profile)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (property : Constraint → Prop)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap) :
    SourceCurrentConstrainedCapGeneratedQueryResources.Fits
        (SourcePruningEnumerationSelectedValueCaller.normalizationProfile profile)
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap).checked ∧
      InternedValueMass.value prepared ≤
        (SourcePruningEnumerationSelectedValueCaller.normalizationProfile profile).mass ∧
      SourceEqualityAnnotationHeap.Heap property heap := by
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  obtain ⟨value, lookup, available, closed⟩ := realized uv handle scs stored
  have same : value = decoded := Option.some.inj (lookup.symm.trans decodedLookup)
  subst value
  have entryRun : ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
      entryFuel uv before.core) = [.ok ((uv, handle, scs, decoded), entered)] := by
    simpa only [run] using congrArg Prod.fst actual
  have nativeRun : SourcePruningEnumerationSelectedValue.run nativeFuel decoded
      caller.checked.native.machine.heap = .done prepared heap := by
    have next := congrArg Prod.snd actual
    simpa only [run, entryRun, Option.some.injEq] using next
  have numeric := SourcePruningEnumerationSelectedValueCaller.fits_after profile caller nativeFuel
    decoded prepared heap packet.context.ready.semantic packet.context.ready.costs
    available closed bounded nativeRun
  have invariants := SourcePruningEnumerationSelectedValue.run_invariants property nativeFuel
    decoded caller.checked.native.machine.heap prepared heap packet.context.ready.semantic available
    packet.context.ready.costs packet.context.probes known nativeRun
  exact ⟨numeric.1, numeric.2, invariants.2.2⟩

end MicroCFTA.SourcePruningEnumerationSelectedPreparation
