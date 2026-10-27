import MicroCFTA.SourceFlatPruningRecursiveOrdinaryResources

/-!
# Original row capacity for flat ordinary finite-depth callbacks

The current parent bounds the selected edge count. One original reservation
covers that count and one extra stage. Padding keeps the actual endpoint,
full memos, stopped shape and every output packet.
The actual flat execution family remains at the same shared work bound.
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

/-- An original row envelope supplies the actual ordinary scan and its finished resources. -/
theorem ordinary_finite_complete_forecast
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
      (SourceCurrentConstrainedCapTargetForecast.scalar seed.2 + 1)) :
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
      (edgesOf (.node parentEntry storedEdges depth free)).length ≤
        SourceCurrentConstrainedCapTargetForecast.scalar seed.2 + 1 ∧
      Fits (stage recursiveFuel seed capturedMass inherited
        (SourceCurrentConstrainedCapTargetForecast.scalar seed.2 + 1)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited
        (SourceCurrentConstrainedCapTargetForecast.scalar seed.2 + 1)).1)
        afterCaller.checked.native.machine.heap ∧
      OutcomeResources formulas solver caller
        (stage recursiveFuel seed capturedMass inherited (SourceCurrentConstrainedCapTargetForecast.scalar seed.2 + 1))
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
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  obtain ⟨value, lookup, available, _closed⟩ := realized uv handle scs stored
  have same : value = .node parentEntry storedEdges depth free :=
    Option.some.inj (lookup.symm.trans decoded)
  subst value
  have heapFits : SourceCurrentConstrainedCapRequiredResources.HeapFits seed.2
      caller.checked.native.machine.heap :=
    SourceCurrentConstrainedCapRequiredResources.of_checked
      (profile := seed.2) (before := caller.checked) bounded
  have rowWidth := SourceCurrentConstrainedCapRequiredResources.node_width heapFits available
  have countBound : (edgesOf (.node parentEntry storedEdges depth free)).length ≤
      SourceCurrentConstrainedCapTargetForecast.scalar seed.2 + 1 :=
    Nat.le_trans (selectionLength parentEntry storedEdges depth free)
      (Nat.le_trans rowWidth (Nat.le_succ _))
  obtain ⟨bound, enteredCache, processed, outputs, afterCaller, next, final, result,
    entryRun, stable, counter, values, sameFlags, sameWaiting, enteredPacket, outerRun,
    scanRun, post, captured, afterFits, afterKnown, processedLength, receipts, outputPackets,
    shape, finished, flatRunning⟩ :=
    ordinary_finite_complete_resources holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver recursive inventory caller memos before uv handle scs parentEntry storedEdges depth free
      packet ready stored decoded selected incoming nonterminal bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength
      (SourcePruningEnumerationFiniteReservation.ScanReserved.prefix reserved countBound)
  have growth := SourcePruningEnumerationFiniteReservation.count_mono
    recursiveFuel seed capturedMass inherited countBound
  refine ⟨bound, enteredCache, processed, outputs, afterCaller, next, final, result,
    entryRun, stable, counter, values, sameFlags, sameWaiting, enteredPacket, outerRun, scanRun,
    post, captured, afterFits, afterKnown, processedLength, receipts, outputPackets, shape, finished,
    countBound, afterFits.mono growth.1, ?_, finished.mono growth.1 growth.2, flatRunning⟩
  intro key edge found
  exact growth.2 (afterKnown key edge found)

end MicroCFTA.SourceFlatPruningNativeOrdinaryContinuations
