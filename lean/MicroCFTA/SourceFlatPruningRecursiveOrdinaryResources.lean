import MicroCFTA.SourceFlatPruningRecursiveSiblingResources
import MicroCFTA.SourceFlatPruningFiniteContract
import MicroCFTA.SourceFlatPruningNativeOrdinaryContinuations
import MicroCFTA.SourceFlatPruningEntry
import MicroCFTA.SourcePruningEnumerationSuspendedMass
import MicroCFTA.SourcePruningEnumerationSelectedEntry
import MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations

/-!
# Actual flat ordinary entry with finite-depth callbacks

The entry runs once before the ordered sibling scan. Each completed edge
runs its callback and a finite recursive continuation before the next sibling.
The entered cache supplies each sibling. Actual native effects and full
memos pass to the suffix. Stops retain their outputs and optional endpoint.
Each related flat input replays the same entry and the same scan result.
-/
namespace MicroCFTA.SourceFlatPruningNativeOrdinaryContinuations
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationFiniteReservation (stage ScanReserved)
open SourcePruningEnumerationRecursive (Packet OutcomeResources)
open SourcePruningEnumerationNativeFiniteSiblingResources (ReceiptAt OutputAt StoppedAt)
attribute [local irreducible] SourcePruningEnumerationFiniteReservation.step
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
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original ordinary inputs derive the actual finite-depth sibling scan and its finished resources. -/
theorem ordinary_finite_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : SourceFlatPruningRecursive.Complete (bits := bits) holeKey fits admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveFuel) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (selected : ∀ edge ∈ edgesOf (.node parentEntry storedEdges depth free), edge ∈ storedEdges)
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : ScanReserved bits recursiveFuel seed capturedMass inherited
      (edgesOf (.node parentEntry storedEdges depth free)).length) :
    ∃ (bound : Nat) (entered : Cached)
      (processed : List (Receipt (bits + 2))) (outputs : List (SourcePruningEnumerationRecursive.Output (bits + 2) Typing))
      (afterCaller : Caller (bits + 2)) (next : Inventory) (final : Memos)
      (result : Result (SourcePruningEnumerationRecursive.Output (bits + 2) Typing) (SourcePruningEnumerationRecursive.Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
          (bound + extra) uv before.core) =
        [.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)]) ∧
      EnumerationDriver.RenderStable before.core entered.core ∧
      entered.core.counter = before.core.counter ∧ entered.core.values = before.core.values ∧
      entered.expandable = before.expandable ∧ entered.waiting = before.waiting ∧
      Packet formulas solver inventory caller memos metadata entered ∧
      (∀ extra, SourcePruningEnumerationNativeOrdinaryContinuations.run
        (SourcePruningEnumerationRecursive.continueWith (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv edgesOf caller before memos.query =
          ([.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)], some result)) ∧
      (∀ extra, SourcePruningEnumerationNativeContinuations.run
        (SourcePruningEnumerationRecursive.continueWith (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs entered (edgesOf (.node parentEntry storedEdges depth free)) caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧
      Packet formulas solver next afterCaller final metadata entered ∧
      Fits (stage recursiveFuel seed capturedMass inherited
        (edgesOf (.node parentEntry storedEdges depth free)).length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited
        (edgesOf (.node parentEntry storedEdges depth free)).length).1) afterCaller.checked.native.machine.heap ∧
      processed.length ≤ (edgesOf (.node parentEntry storedEdges depth free)).length ∧
      (∀ index receipt, processed[index]? = some receipt →
        ReceiptAt recursiveFuel formulas solver caller entered uv seed scs capturedMass inherited index receipt) ∧
      (∀ output ∈ outputs, ∃ index, index < (edgesOf (.node parentEntry storedEdges depth free)).length ∧
        OutputAt recursiveFuel formulas solver caller seed capturedMass inherited index output) ∧
      (result = .complete processed outputs afterCaller final.query ∨
        ∃ current, result = .stopped processed outputs current ∧
          (SourcePruningEnumerationRecursive.endpoint current = none ∨ SourcePruningEnumerationRecursive.endpoint current = some (afterCaller, final.query)) ∧
          StoppedAt recursiveFuel formulas solver caller entered uv seed scs capturedMass inherited
            processed.length outputs current) ∧
      OutcomeResources formulas solver caller
        (stage recursiveFuel seed capturedMass inherited (edgesOf (.node parentEntry storedEdges depth free)).length)
        (SourcePruningEnumerationRecursive.finish uv result) ∧
      ∀ (flat : EnumerationFlatCached.Cached Symbol Constraint),
        EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ (flatEntered : EnumerationFlatState.State Symbol Constraint)
          (flatResult : SourceFlatPruningNativeContinuations.Result
            (SourceFlatPruningRecursive.Output (bits + 2) Typing)
            (SourceFlatPruningRecursive.Failure (bits + 2) Typing) (bits + 2)),
          SourceFlatPruningNativeOrdinaryContinuations.run
            (SourceFlatPruningRecursive.continueWith
              (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                (bound + extra) recursiveFuel)
              graph templates stop order (bound + extra) metadata uv)
            checkEmpty (bound + extra) (bound + extra) (bound + extra)
            uv edgesOf caller flat memos.query =
              ([.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), flatEntered)], some flatResult) ∧
          EnumerationFlatState.Related flatEntered entered.core ∧
          SourceFlatPruningNativeContinuations.ResultRelated
            SourceFlatPruningRecursive.OutputRelated SourceFlatPruningRecursive.FailureRelated flatResult result := by
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨entryFuel, value, enteredCache, entryRun, lookup, _available, _closed, counter, values,
    sameFlags, sameWaiting, enteredStored, enteredReady, _protected, enteredPaths, enteredRealized,
    enteredCounts, enteredFlags, _bucketBounded, _retained, stable⟩ :=
    SourcePruningEnumerationSelectedEntry.complete caller.checked.native.machine.heap before uv handle scs roots
      ready stored realized paths counts flags
  have same : value = .node parentEntry storedEdges depth free :=
    Option.some.inj (lookup.symm.trans decoded)
  subst value
  have frame : EnumerationExpandableIndex.frame enteredCache.core before = enteredCache := by
    cases enteredCache with
    | mk core expandable waiting =>
        simp only [EnumerationExpandableIndex.frame] at *
        congr 1
        · exact sameFlags.symm
        · exact sameWaiting.symm
  have enteredPacket : Packet formulas solver inventory caller memos metadata enteredCache := by
    obtain ⟨level, frontier, ordered⟩ := packet.ordered
    refine ⟨packet.context, stable.safe,
      EnumerationReferences.pending_read before.core enteredCache.core stable packet.pending,
      ⟨roots, enteredPaths, stable.safe.1, enteredRealized, enteredCounts, enteredFlags⟩,
      ⟨level, frontier, EnumerationOrder.stratified_read before.core enteredCache.core level frontier stable ordered⟩,
      ?_⟩
    simpa only [counter] using packet.bounded
  have enteredMass : suspendedBound enteredCache.core ≤ capturedMass := by
    rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core enteredCache.core values]
    exact initialMass
  obtain ⟨scanBound, processed, outputs, afterCaller, next, final, result, scanRun, post,
    captured, afterFits, afterKnown, processedLength, receipts, outputPackets, shape, finished, flatScan⟩ :=
    SourceFlatPruningNativeFiniteSiblingResources.alternatives_finite_finish_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel seed formulas solver recursive inventory
      caller memos enteredCache uv handle scs parentEntry storedEdges
      (edgesOf (.node parentEntry storedEdges depth free)) depth free enteredPacket enteredReady enteredStored
      decoded selected (EnumerationReferences.incoming_read uv before.core enteredCache.core stable incoming)
      bounded known selectionMembers selectionLength capturedMass inherited enteredMass inheritedLength reserved
  have entryAt (extra : Nat) :
      ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
        (entryFuel + scanBound + extra) uv before.core) =
        [.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), enteredCache.core)] := by
    simpa only [Nat.add_assoc] using entryRun (scanBound + extra)
  have scanAt (extra : Nat) : SourcePruningEnumerationNativeContinuations.run
      (SourcePruningEnumerationRecursive.continueWith
        (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order (entryFuel + scanBound + extra) recursiveFuel)
        graph templates stop order (entryFuel + scanBound + extra) metadata uv)
      checkEmpty (entryFuel + scanBound + extra) (entryFuel + scanBound + extra)
      (entryFuel + scanBound + extra) (entryFuel + scanBound + extra) (entryFuel + scanBound + extra)
      uv scs enteredCache (edgesOf (.node parentEntry storedEdges depth free)) caller memos.query = result := by
    have actual := scanRun (entryFuel + extra)
    have fuelSame : scanBound + (entryFuel + extra) = entryFuel + scanBound + extra := by omega
    rw [fuelSame] at actual
    exact actual
  refine ⟨entryFuel + scanBound, enteredCache, processed, outputs, afterCaller, next, final, result,
    entryAt, stable, counter, values, sameFlags, sameWaiting, enteredPacket, ?_, scanAt, post, captured,
    afterFits, afterKnown, processedLength, receipts, outputPackets, shape, finished, ?_⟩
  · intro extra
    have actual := SourcePruningEnumerationNativeOrdinaryContinuations.entered
      (SourcePruningEnumerationRecursive.continueWith
        (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order (entryFuel + scanBound + extra) recursiveFuel)
        graph templates stop order (entryFuel + scanBound + extra) metadata uv)
      checkEmpty (entryFuel + scanBound + extra) (entryFuel + scanBound + extra)
      (entryFuel + scanBound + extra) (entryFuel + scanBound + extra) (entryFuel + scanBound + extra)
      uv uv handle scs parentEntry storedEdges depth free edgesOf caller before memos.query enteredCache.core
      (entryAt extra) nonterminal
    rw [frame, scanAt extra] at actual
    exact actual

  · intro flat related extra
    obtain ⟨read, flatEntry, enteredCores⟩ :=
      SourceFlatPruningEntry.enter_replays caller.checked.native.machine.heap
        (entryFuel + scanBound + extra) uv flat.core before.core
        (uv, handle, scs, .node parentEntry storedEdges depth free) enteredCache.core
        related.core (entryAt extra)
    let enteredFlat := EnumerationFlatCached.frame read flat
    have enteredRelated : EnumerationFlatCached.Related enteredFlat enteredCache := by
      rw [← frame]
      exact EnumerationFlatCached.frame_related related enteredCores
    obtain ⟨flatResult, actualScan, scanRelated⟩ :=
      flatScan enteredFlat enteredRelated (entryFuel + extra)
    have fuelSame : scanBound + (entryFuel + extra) = entryFuel + scanBound + extra := by omega
    rw [fuelSame] at actualScan
    refine ⟨read, flatResult, ?_, enteredCores, scanRelated⟩
    have actual := SourceFlatPruningNativeOrdinaryContinuations.entered
      (SourceFlatPruningRecursive.continueWith
        (SourceFlatPruningRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (entryFuel + scanBound + extra) recursiveFuel)
        graph templates stop order (entryFuel + scanBound + extra) metadata uv)
      checkEmpty (entryFuel + scanBound + extra) (entryFuel + scanBound + extra)
      (entryFuel + scanBound + extra) uv uv handle scs parentEntry storedEdges depth free edgesOf caller flat
      memos.query read flatEntry nonterminal
    rw [actualScan] at actual
    exact actual

end MicroCFTA.SourceFlatPruningNativeOrdinaryContinuations
