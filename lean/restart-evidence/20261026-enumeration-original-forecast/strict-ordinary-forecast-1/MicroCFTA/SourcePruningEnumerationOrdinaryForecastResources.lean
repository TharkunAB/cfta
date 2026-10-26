import MicroCFTA.SourcePruningEnumerationOrdinaryHookResources
import MicroCFTA.SourcePruningEnumerationOriginalForecast
import MicroCFTA.SourcePruningEnumerationSelectedEntry
import MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations

/-!
# Actual ordinary scans under an original numeric forecast

The original profile and guard alphabet bound every actual selected edge.
The selector does not increase the row count. The inherited length bound is
fixed before the scan. The full earlier scan conclusion remains intact.
The final caller also fits the complete original forecast.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed Reserved)
open SourcePruningEnumerationNativeBranchCompletion (cost)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume)
open SourcePruningEnumerationNativeHookResources (ReceiptAt OutputAt StoppedAt)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Result" => SourcePruningEnumerationNativeContinuations.Result
local notation "reservationAdvance" => SourcePruningEnumerationIncomingReservation.advance
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An original profile, alphabet and bucket bound derive the complete actual ordinary scan. -/
theorem ordinary_zero_complete_forecast
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (seed : Seed) (inherited : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (selected : ∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), edge ∈ storedEdges)
    (selectedLength : (edgesOf (.node parentEntry storedEdges depth free)).length ≤ storedEdges.length)
    (inheritedBound : scs.length ≤ inherited)
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (bounded : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (SourcePruningEnumerationOriginalForecast.count seed inherited))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (bound : Nat) (entered : Cached)
      (processed : List (Receipt (bits + 2))) (outputs : List (Output (bits + 2) Typing))
      (afterCaller : Caller (bits + 2)) (next : Inventory) (final : Memos)
      (result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      ((∀ extra, ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
          (bound + extra) uv before.core) =
        [.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)]) ∧
      EnumerationDriver.RenderStable before.core entered.core ∧
      entered.core.counter = before.core.counter ∧ entered.core.values = before.core.values ∧
      entered.expandable = before.expandable ∧ entered.waiting = before.waiting ∧
      Packet formulas solver inventory caller memos metadata entered ∧
      (∀ extra, run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) 0)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv edgesOf caller before memos.query =
          ([.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)], some result)) ∧
      (∀ extra, SourcePruningEnumerationNativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) 0)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs entered (edgesOf (.node parentEntry storedEdges depth free)) caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧
      Packet formulas solver next afterCaller final metadata entered ∧
      Fits (reservationAdvance seed (cost scs before.core.counter
        (edgesOf (.node parentEntry storedEdges depth free)))).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (reservationAdvance seed (cost scs before.core.counter
        (edgesOf (.node parentEntry storedEdges depth free)))).1) afterCaller.checked.native.machine.heap ∧
      (∀ index receipt, processed[index]? = some receipt →
        ReceiptAt formulas solver caller entered uv seed scs
          (edgesOf (.node parentEntry storedEdges depth free)) index receipt) ∧
      (∀ output ∈ outputs, ∃ index, index < (edgesOf (.node parentEntry storedEdges depth free)).length ∧
        OutputAt formulas solver caller entered seed scs
          (edgesOf (.node parentEntry storedEdges depth free)) index output) ∧
      (result = .complete processed outputs afterCaller final.query ∨
        ∃ current, result = .stopped processed outputs current ∧
          StoppedAt formulas solver caller entered uv seed scs
            (edgesOf (.node parentEntry storedEdges depth free)) processed.length afterCaller next final current)) ∧
      cost scs before.core.counter (edgesOf (.node parentEntry storedEdges depth free)) ≤
        SourcePruningEnumerationOriginalForecast.count seed inherited ∧
      Fits (reservationAdvance seed (SourcePruningEnumerationOriginalForecast.count seed inherited)).2
        afterCaller.checked ∧
      Heap (fun guard => guard ∈
        (reservationAdvance seed (SourcePruningEnumerationOriginalForecast.count seed inherited)).1)
        afterCaller.checked.native.machine.heap := by
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  obtain ⟨value, lookup, available, _closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry storedEdges depth free := Option.some.inj (lookup.symm.trans decoded)
  subst value
  have costBound := SourcePruningEnumerationOriginalForecast.cost_le seed inherited
    caller.checked.native.machine.heap (SourceCurrentConstrainedCapRequiredResources.of_checked bounded) known
    packet.context.ready.semantic.ready.semantic.1.normal.facts.linked parentEntry storedEdges
    (edgesOf (.node parentEntry storedEdges depth free)) depth free available selected selectedLength
    scs before.core.counter inheritedBound
  obtain ⟨bound, enteredCache, processed, outputs, afterCaller, next, final, result, full⟩ :=
    ordinary_zero_complete_resources holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      seed formulas solver inventory caller memos before uv handle scs parentEntry storedEdges depth free
      packet ready stored decoded selected incoming nonterminal bounded (reserved.prefix costBound) known
  obtain ⟨entryRun, stable, counter, values, sameFlags, sameWaiting, enteredPacket, outerRun,
    scanRun, post, captured, afterFits, afterKnown, receipts, outputPackets, shape⟩ := full
  refine ⟨bound, enteredCache, processed, outputs, afterCaller, next, final, result,
    ⟨entryRun, stable, counter, values, sameFlags, sameWaiting, enteredPacket, outerRun, scanRun,
      post, captured, afterFits, afterKnown, receipts, outputPackets, shape⟩,
    costBound, afterFits.mono (SourcePruningEnumerationIncomingReservation.advance_count_profile_mono seed costBound), ?_⟩
  intro key edge found
  obtain ⟨extra, countSame⟩ := Nat.exists_eq_add_of_le costBound
  have member := afterKnown key edge found
  rw [countSame, SourcePruningEnumerationIncomingReservation.advance_add]
  exact SourcePruningEnumerationIncomingReservation.advance_alphabet_ge _ extra member

end MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations
