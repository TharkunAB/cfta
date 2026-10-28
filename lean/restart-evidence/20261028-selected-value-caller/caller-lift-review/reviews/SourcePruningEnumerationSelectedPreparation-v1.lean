import MicroCFTA.SourcePruningEnumerationSelectedValueCaller
import MicroCFTA.SourcePruningEnumerationSelectedEntry
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.EnumerationCompleteness

/-!
# Actual entry and one selected-value preparation

Entry retains the captured root, handle and suspended bucket. The native
worker prepares its decoded value once. The original context derives the
full returned caller and the same enumeration packet. No slot is written.
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

/-- Retain the complete entry observation and every actual native preparation outcome. -/
def run (entryFuel nativeFuel uv : Nat) (caller : Caller width) (before : Cached) :
    Raw × Option (MergedSourceComparison.Result Symbol Constraint Node) :=
  let raw := ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
    entryFuel uv before.core)
  (raw, match raw with
    | [.ok ((_target, _handle, _scs, value), _entered)] =>
        some (SourcePruningEnumerationSelectedValue.run nativeFuel value caller.checked.native.machine.heap)
    | _ => none)

private theorem satisfies_read (language : NodeLanguage Symbol)
    (meaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol)
    (before after : Core) (stable : EnumerationDriver.RenderStable before after) :
    Satisfies language meaning assignment after ↔ Satisfies language meaning assignment before := by
  have classes : UnionFind.Satisfies after.representatives assignment ↔
      UnionFind.Satisfies before.representatives assignment := by
    constructor
    · intro satisfied left right related
      exact satisfied left right ((stable.classes left right).mpr related)
    · intro satisfied left right related
      exact satisfied left right ((stable.classes left right).mp related)
  simp only [Satisfies, Fragments.stateSatisfies, stable.values, stable.obligations, classes]

/-- Original selected storage derives one stable preparation and its full forward-model packet. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs)) :
    ∃ (bound : Nat) (decoded result : Node) (heap : State Symbol Constraint) (entered : Cached),
      (∀ extra, run (bound + extra) (bound + extra) uv caller before =
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
          InternedGuardedLanguage.meaning holds ambient result (assignment uv)) := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨entryBound, decoded, entered, entryRun, decodedLookup, available, closed,
    counter, values, sameFlags, sameWaiting, enteredStored, enteredReady, _protected,
    enteredPaths, enteredRealized, enteredCounts, enteredFlags, _buckets, _inputs, stable⟩ :=
    SourcePruningEnumerationSelectedEntry.complete caller.checked.native.machine.heap
      before uv handle scs roots ready stored realized paths counts flags
  have enteredPacket : Packet formulas solver inventory caller memos metadata entered := by
    obtain ⟨level, frontier, ordered⟩ := packet.ordered
    refine ⟨packet.context, stable.safe,
      EnumerationReferences.pending_read before.core entered.core stable packet.pending,
      ⟨roots, enteredPaths, stable.safe.1, enteredRealized, enteredCounts, enteredFlags⟩,
      ⟨level, frontier, EnumerationOrder.stratified_read before.core entered.core level frontier stable ordered⟩,
      ?_⟩
    simpa only [counter] using packet.bounded
  obtain ⟨nativeBound, result, heap, native, post⟩ :=
    SourcePruningEnumerationSelectedValueCaller.complete formulas solver inventory caller memos decoded
      packet.context available closed
  obtain ⟨nativeRun, kept, _semantic, resultAvailable, resultClosed, exactLanguage⟩ := native
  refine ⟨entryBound + nativeBound, decoded, result, heap, entered, ?_, decodedLookup, post,
    SourcePruningEnumerationRecursive.captured_post enteredPacket post, stable, enteredReady,
    enteredStored, counter, values, sameFlags, sameWaiting, resultAvailable, resultClosed,
    exactLanguage, ?_⟩
  · intro extra
    have entryExact : ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
        (entryBound + nativeBound + extra) uv before.core) =
        [.ok ((uv, handle, scs, decoded), entered.core)] := by
      simpa only [Nat.add_assoc] using entryRun (nativeBound + extra)
    have nativeExact : SourcePruningEnumerationSelectedValue.run (entryBound + nativeBound + extra)
        decoded caller.checked.native.machine.heap = .done result heap := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using nativeRun (entryBound + extra)
    simp only [run, entryExact, nativeExact]
  · intro holds ambient residualMeaning assignment
    have exactModel :=
      (SourcePruningEnumerationNativeLanguage.satisfies_keeps holds ambient
        caller.checked.native.machine.heap heap entered.core residualMeaning assignment enteredRealized kept).trans
      (satisfies_read (SourcePruningEnumerationNativeLanguage.handles holds ambient
        caller.checked.native.machine.heap) residualMeaning assignment before.core entered.core stable)
    refine ⟨exactModel, ?_⟩
    intro original
    have originalSlot := EnumerationCompleteness.stored_satisfies
      (SourcePruningEnumerationNativeLanguage.handles holds ambient caller.checked.native.machine.heap)
      residualMeaning assignment before.core original uv _ stored
    have accepted : SourcePruningEnumerationNativeLanguage.handles holds ambient
        caller.checked.native.machine.heap handle (assignment uv) := originalSlot.1
    exact (exactLanguage holds ambient (assignment uv)).mpr
      ((SourcePruningEnumerationNativeLanguage.handles_lookup holds ambient
        caller.checked.native.machine.heap handle decoded (assignment uv) decodedLookup).mp accepted)

end MicroCFTA.SourcePruningEnumerationSelectedPreparation
