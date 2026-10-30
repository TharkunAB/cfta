import MicroCFTA.SourcePruningEnumerationFiniteOrdinaryResources
import MicroCFTA.SourcePruningEnumerationExecutionSiblingBridge
import MicroCFTA.SourcePruningEnumerationPathPreparedEntry

/-!
# Actual ordinary entry and sibling execution paths

The actual entry equation supplies its target.
The original resource witnesses and their complete stable result stay.
-/
namespace MicroCFTA.SourcePruningEnumerationExecutionOrdinaryBridge.Native
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationFiniteReservation (stage ScanReserved)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume endpoint OutcomeResources)
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
open SourcePruningEnumerationNativeOrdinaryContinuations (run entered)
open SourcePruningEnumerationPathTransport (StatePaths ProjectionPaths)
open SourcePruningEnumerationPathSelectedRaw (RawPaths)
open SourcePruningEnumerationExecutionPathData (OutcomePaths NativeFailurePaths)
open SourcePruningEnumerationExecutionPaths (NativeStage SiblingPaths ResumeNative)

/-- Original ordinary inputs derive the actual finite-depth sibling scan and its finished resources. -/
theorem ordinary_finite_complete_resources_paths
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : SourcePruningEnumerationRecursive.Complete (bits := bits) holeKey fits admits graph templates
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
      (edgesOf (.node parentEntry storedEdges depth free)).length)
    (P : EqualityTrie.Path → Prop) (original : StatePaths P before.core)
    (tails : ∀ index suffix, P (index :: suffix) → P suffix)
    (projected : ProjectionPaths (stage recursiveFuel seed capturedMass inherited
      (edgesOf (.node parentEntry storedEdges depth free)).length).1 P)
    (pathsIH : ∀ (nextInventory : Inventory) (nextCaller : Caller (bits + 2))
        (nextMemos : Memos) (nextCache : Cached) (nextMetadata : Metadata Typing)
        (nextSeed : Seed) (nextCeiling : Nat),
      Packet formulas solver nextInventory nextCaller nextMemos nextMetadata nextCache →
      Fits nextSeed.2 nextCaller.checked →
      Heap (fun guard => guard ∈ nextSeed.1) nextCaller.checked.native.machine.heap →
      (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
      (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
      suspendedBound nextCache.core ≤ nextCeiling →
      SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel nextSeed nextCeiling →
      StatePaths P nextCache.core →
      ProjectionPaths (SourcePruningEnumerationFiniteReservation.final recursiveFuel nextSeed nextCeiling).1 P →
      ∃ bound, ∀ extra,
        SourcePruningEnumerationExecutionPaths.Native P holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel nextMetadata nextCaller nextMemos.query nextCache) :
    ∃ (bound : Nat) (entered : Cached)
      (processed : List (Receipt (bits + 2))) (outputs : List (Output (bits + 2) Typing))
      (afterCaller : Caller (bits + 2)) (next : Inventory) (final : Memos)
      (result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
          (bound + extra) uv before.core) =
        [.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)]) ∧
      EnumerationDriver.RenderStable before.core entered.core ∧
      entered.core.counter = before.core.counter ∧ entered.core.values = before.core.values ∧
      entered.expandable = before.expandable ∧ entered.waiting = before.waiting ∧
      Packet formulas solver inventory caller memos metadata entered ∧
      (∀ extra, run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv edgesOf caller before memos.query =
          ([.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)], some result)) ∧
      (∀ extra, SourcePruningEnumerationNativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
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
          (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) ∧
          StoppedAt recursiveFuel formulas solver caller entered uv seed scs capturedMass inherited
            processed.length outputs current) ∧
      OutcomeResources formulas solver caller
        (stage recursiveFuel seed capturedMass inherited (edgesOf (.node parentEntry storedEdges depth free)).length)
        (SourcePruningEnumerationRecursive.finish uv result) ∧
      (∀ extra, NativeStage P
        (ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel) (NativeFailurePaths P)
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata uv)
        graph templates stop order checkEmpty (bound + extra) metadata uv edgesOf caller before memos.query) ∧
      OutcomePaths P (NativeFailurePaths P) (SourcePruningEnumerationRecursive.finish uv result) := by
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
    captured, afterFits, afterKnown, processedLength, receipts, outputPackets, shape, finished⟩ :=
    SourcePruningEnumerationNativeFiniteSiblingResources.alternatives_finite_finish_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel seed formulas solver recursive inventory
      caller memos enteredCache uv handle scs parentEntry storedEdges
      (edgesOf (.node parentEntry storedEdges depth free)) depth free enteredPacket enteredReady enteredStored
      decoded selected (EnumerationReferences.incoming_read uv before.core enteredCache.core stable incoming)
      bounded known selectionMembers selectionLength capturedMass inherited enteredMass inheritedLength reserved
  have enteredPathsP : StatePaths P enteredCache.core := by
    apply SourcePruningEnumerationPathPreparedEntry.enter_paths caller.checked.native.machine.heap
      entryFuel uv before.core enteredCache.core
      (uv, handle, scs, .node parentEntry storedEdges depth free) original
    change Except.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), enteredCache.core) ∈
      ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap entryFuel uv before.core)
    have actual := entryRun 0
    simp only [Nat.add_zero] at actual
    rw [actual]
    exact List.mem_singleton_self _
  obtain ⟨pathBound, _pathProcessed, _pathOutputs, _pathCaller, _pathInventory, _pathMemos,
    pathResult, pathRun, _pathPost, _pathPacket, _pathFits, _pathKnown, _pathLength,
    _pathReceipts, _pathOutputsAt, _pathShape, foldPaths, invocations⟩ :=
    SourcePruningEnumerationExecutionSiblingBridge.Native.alternatives_finite_complete_resources_paths
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel seed formulas solver recursive inventory
      caller memos enteredCache uv handle scs parentEntry storedEdges
      (edgesOf (.node parentEntry storedEdges depth free)) depth free enteredPacket enteredReady enteredStored
      decoded selected (EnumerationReferences.incoming_read uv before.core enteredCache.core stable incoming)
      bounded known selectionMembers selectionLength capturedMass inherited enteredMass inheritedLength reserved
      P enteredPathsP tails projected pathsIH
  have sameResult : pathResult = result := by
    have first := scanRun pathBound
    have second := pathRun scanBound
    have same : pathBound + scanBound = scanBound + pathBound := by omega
    rw [same] at second
    exact second.symm.trans first
  subst pathResult
  have entryAt (extra : Nat) :
      ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
        (entryFuel + scanBound + pathBound + extra) uv before.core) =
        [.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), enteredCache.core)] := by
    simpa only [Nat.add_assoc] using entryRun (scanBound + pathBound + extra)
  have scanAt (extra : Nat) : SourcePruningEnumerationNativeContinuations.run
      (continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (entryFuel + scanBound + pathBound + extra) recursiveFuel)
        graph templates stop order (entryFuel + scanBound + pathBound + extra) metadata uv)
      checkEmpty (entryFuel + scanBound + pathBound + extra) (entryFuel + scanBound + pathBound + extra)
      (entryFuel + scanBound + pathBound + extra) (entryFuel + scanBound + pathBound + extra) (entryFuel + scanBound + pathBound + extra)
      uv scs enteredCache (edgesOf (.node parentEntry storedEdges depth free)) caller memos.query = result := by
    have actual := scanRun (entryFuel + pathBound + extra)
    have fuelSame : scanBound + (entryFuel + pathBound + extra) = entryFuel + scanBound + pathBound + extra := by omega
    rw [fuelSame] at actual
    exact actual
  have outerAt (extra : Nat) : run
      (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (entryFuel + scanBound + pathBound + extra) recursiveFuel)
        graph templates stop order (entryFuel + scanBound + pathBound + extra) metadata uv)
      checkEmpty (entryFuel + scanBound + pathBound + extra) (entryFuel + scanBound + pathBound + extra)
      (entryFuel + scanBound + pathBound + extra) (entryFuel + scanBound + pathBound + extra)
      (entryFuel + scanBound + pathBound + extra) uv edgesOf caller before memos.query =
      ([.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), enteredCache.core)], some result) := by
    have actual := entered
      (continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (entryFuel + scanBound + pathBound + extra) recursiveFuel)
        graph templates stop order (entryFuel + scanBound + pathBound + extra) metadata uv)
      checkEmpty (entryFuel + scanBound + pathBound + extra) (entryFuel + scanBound + pathBound + extra)
      (entryFuel + scanBound + pathBound + extra) (entryFuel + scanBound + pathBound + extra) (entryFuel + scanBound + pathBound + extra)
      uv uv handle scs parentEntry storedEdges depth free edgesOf caller before memos.query enteredCache.core
      (entryAt extra) nonterminal
    rw [frame, scanAt extra] at actual
    exact actual
  refine ⟨entryFuel + scanBound + pathBound, enteredCache, processed, outputs, afterCaller, next, final, result,
    entryAt, stable, counter, values, sameFlags, sameWaiting, enteredPacket, outerAt, scanAt, post, captured,
    afterFits, afterKnown, processedLength, receipts, outputPackets, shape, finished, ?_,
    SourcePruningEnumerationExecutionPathData.native_finish_paths uv result foldPaths⟩
  intro extra
  unfold NativeStage
  rw [outerAt extra]
  refine ⟨?_, ?_, ?_⟩
  · intro value core member
    cases Except.ok.inj (List.mem_singleton.mp member)
    exact enteredPathsP
  · intro current found
    cases Option.some.inj found
    exact foldPaths
  · dsimp only
    rw [nonterminal]
    unfold SiblingPaths
    rw [frame]
    refine ⟨?_, ?_⟩
    · rw [scanAt extra]
      exact foldPaths
    · have current := invocations (entryFuel + scanBound + extra)
      have same : pathBound + (entryFuel + scanBound + extra) =
          entryFuel + scanBound + pathBound + extra := by omega
      rw [same] at current
      exact current

end MicroCFTA.SourcePruningEnumerationExecutionOrdinaryBridge.Native
