import MicroCFTA.SourcePruningEnumerationSelectedPreparationResources
import MicroCFTA.SourcePruningEnumerationPreparedReservation

/-!
# Guard alphabets and row bounds after actual selected preparation

The original preparation producer fixes every operational witness first.
Actual native normalization retains the original guard property. The
prepared numeric profile bounds an actual ordinary result's row count.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedPreparation
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) × Core))
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Retain the entire resource result and derive the original guard property. -/
theorem complete_resources_known
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (profile : SourceCurrentAllocatedNativeResourceForecast.Profile)
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (property : Constraint → Prop)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap) :
    ∃ (bound : Nat) (decoded result : Node) (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached),
      (((∀ extra, run (bound + extra) (bound + extra) uv caller before =
        ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done result heap))) ∧
      lookupNode caller.checked.native.machine.heap handle = some decoded ∧
      Post formulas solver inventory caller
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos ∧
      Packet formulas solver inventory
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos metadata entered ∧
      EnumerationDriver.RenderStable before.core entered.core ∧
      EnumerationDriver.Ready uv entered.core ∧
      entered.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
      entered.core.counter = before.core.counter ∧ entered.core.values = before.core.values ∧
      entered.expandable = before.expandable ∧ entered.waiting = before.waiting ∧
      Available heap result ∧ result.free = [] ∧
      (∀ holds ambient term,
        InternedGuardedLanguage.meaning holds ambient result term ↔
          InternedGuardedLanguage.meaning holds ambient decoded term) ∧
      ∀ holds ambient residualMeaning assignment,
        (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
          residualMeaning assignment entered.core ↔
        Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
          caller.checked.native.machine.heap) residualMeaning assignment before.core) ∧
        (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
          caller.checked.native.machine.heap) residualMeaning assignment before.core →
          InternedGuardedLanguage.meaning holds ambient result (assignment uv))) ∧
      SourceCurrentConstrainedCapGeneratedQueryResources.Fits
        (SourcePruningEnumerationSelectedValueCaller.normalizationProfile profile)
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap).checked ∧
      InternedValueMass.value result ≤
        (SourcePruningEnumerationSelectedValueCaller.normalizationProfile profile).mass) ∧
      SourceEqualityAnnotationHeap.Heap property heap := by
  obtain ⟨bound, decoded, result, heap, entered, retained⟩ :=
    complete_resources formulas solver inventory caller memos metadata before uv handle scs
      packet ready stored profile fits
  have running := retained.1.1
  have decodedLookup := retained.1.2.1
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  obtain ⟨value, lookup, available, _closed⟩ := realized uv handle scs stored
  have same : value = decoded := Option.some.inj (lookup.symm.trans decodedLookup)
  subst value
  have combined := running 0
  simp only [Nat.add_zero] at combined
  have entryExact := congrArg Prod.fst combined
  change ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
    bound uv before.core) = [.ok ((uv, handle, scs, decoded), entered.core)] at entryExact
  have nativeExact : SourcePruningEnumerationSelectedValue.run bound decoded
      caller.checked.native.machine.heap = .done result heap := by
    have observed := congrArg Prod.snd combined
    simpa only [run, entryExact, Option.some.injEq] using observed
  have invariants := SourcePruningEnumerationSelectedValue.run_invariants property bound
    decoded caller.checked.native.machine.heap result heap packet.context.ready.semantic available
    packet.context.ready.costs packet.context.probes known nativeExact
  exact ⟨bound, decoded, result, heap, entered, retained, invariants.2.2⟩

end MicroCFTA.SourcePruningEnumerationSelectedPreparation

namespace MicroCFTA.SourcePruningEnumerationPreparedReservation
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Fits" => SourceCurrentConstrainedCapGeneratedQueryResources.Fits

/-- Actual available prepared rows fit the original prepared sibling budget. -/
theorem selected_length_le {width : Nat} (seed : Seed) (caller : Caller width)
    (bounded : Fits (preparedSeed seed).2 caller.checked)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (stored selected : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (available : Available caller.checked.native.machine.heap (.node entry stored depth free))
    (lengths : selected.length ≤ stored.length) : selected.length ≤ rows seed := by
  have heapFits : SourceCurrentConstrainedCapRequiredResources.HeapFits (preparedSeed seed).2
      caller.checked.native.machine.heap :=
    SourceCurrentConstrainedCapRequiredResources.of_checked
      (profile := (preparedSeed seed).2) (before := caller.checked) bounded
  have count := SourceCurrentConstrainedCapRequiredResources.node_width heapFits available
  exact Nat.le_trans lengths (Nat.le_trans count (Nat.le_succ _))

end MicroCFTA.SourcePruningEnumerationPreparedReservation
