import MicroCFTA.SourcePruningEnumerationFiniteOrdinaryResources
import MicroCFTA.SourcePruningEnumerationFiniteSiblingHistory
import MicroCFTA.SourcePruningEnumerationOrdinaryInvocation
import MicroCFTA.SourcePruningEnumerationFiniteResources

/-!
# Actual ordinary outputs retain admitted recursive histories

The original ordinary producer supplies one entered cache and its full packet.
The actual entry row identifies that cache on every ordinary invocation path.
Each emitted output retains its full local head and false callback history.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations
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
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Result" => SourcePruningEnumerationNativeContinuations.Result
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Keep the entire ordinary resource packet and add rich receipts at actual hook inputs. -/
theorem ordinary_finite_complete_resources_with_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : SourcePruningEnumerationRecursive.CompleteWithHistory (bits := bits) holeKey fits admits graph templates
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
    (∀ extra output, output ∈ outputs →
      SourcePruningEnumerationNativeFiniteSiblingResources.InvocationHistoryAt
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
        formulas solver (bound + extra) caller memos entered uv scs
        (edgesOf (.node parentEntry storedEdges depth free)) capturedMass inherited output) := by
  obtain ⟨ordinaryBound, entered, processed, outputs, afterCaller, next, final, result,
    entryRun, stable, counter, values, sameFlags, sameWaiting, enteredPacket,
    ordinaryRun, scanRun, post, captured, returnedFits, returnedKnown, processedLength,
    receipts, outputCertificates, shape, finished⟩ :=
    ordinary_finite_complete_resources holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver recursive.forget inventory caller memos before uv handle scs parentEntry storedEdges depth free
      packet ready stored decoded selected incoming nonterminal bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  have enteredStored : entered.core.values[uv]? = some (.unenumerated (some handle) scs) := by
    simpa only [values] using stored
  have enteredRoot : IsRoot entered.core.representatives uv :=
    (enteredPacket.safe.2 uv (.unenumerated (some handle) scs) enteredStored).mp (by intro impossible; cases impossible)
  have enteredReady : EnumerationDriver.Ready uv entered.core := by
    refine ⟨enteredPacket.safe, ?_, enteredRoot, ?_⟩
    · simpa only [counter] using ready.inside
    · intro node bucket current sc member sameClass
      have previous : before.core.values[uv]? = some (.unenumerated (some node) bucket) := by
        simpa only [values] using current
      exact ready.avoids node bucket previous sc member ((stable.classes uv sc.var).mp sameClass)
  have enteredIncoming : EnumerationReferences.IncomingAvoid uv entered.core :=
    EnumerationReferences.incoming_read uv before.core entered.core stable incoming
  have enteredMass : suspendedBound entered.core ≤ capturedMass := by
    rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core entered.core values]
    exact initialMass
  obtain ⟨receiptBound, historyProcessed, historyOutputs, historyCaller, historyInventory, historyMemos, historyResult,
    historyRun, _historyPost, _historyPacket, _historyFits, _historyKnown, _historyLength,
    _historyReceipts, _historyOutputResources, historyShape, histories⟩ :=
    SourcePruningEnumerationNativeFiniteSiblingResources.alternatives_finite_complete_resources_with_history
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      seed formulas solver recursive inventory caller memos entered uv handle scs parentEntry storedEdges
      (edgesOf (.node parentEntry storedEdges depth free)) depth free enteredPacket enteredReady enteredStored decoded
      selected enteredIncoming bounded known selectionMembers selectionLength capturedMass inherited enteredMass inheritedLength reserved
  have originalOutputs : SourcePruningEnumerationHookInvocation.foldOutputs result = outputs := by
    rcases shape with completed | ⟨current, stopped, _endpoint, _certificate⟩
    · rw [completed]
      rfl
    · rw [stopped]
      rfl
  have actualOutputs : SourcePruningEnumerationHookInvocation.foldOutputs historyResult = historyOutputs := by
    rcases historyShape with completed | ⟨current, stopped, _endpoint, _certificate⟩
    · rw [completed]
      rfl
    · rw [stopped]
      rfl
  have entryAt (extra : Nat) : ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
      (ordinaryBound + receiptBound + extra) uv before.core) =
      [.ok ((uv, handle, scs, .node parentEntry storedEdges depth free), entered.core)] := by
    simpa only [Nat.add_assoc] using entryRun (receiptBound + extra)
  refine ⟨ordinaryBound + receiptBound, entered, processed, outputs, afterCaller, next, final, result,
    entryAt, stable, counter, values, sameFlags, sameWaiting, enteredPacket, ?_, ?_, post, captured,
    returnedFits, returnedKnown, processedLength, receipts, outputCertificates, shape, finished, ?_⟩
  · intro extra
    simpa only [Nat.add_assoc] using ordinaryRun (receiptBound + extra)
  · intro extra
    simpa only [Nat.add_assoc] using scanRun (receiptBound + extra)
  · intro extra output member
    have originalRun := scanRun (receiptBound + extra)
    have actualRun := historyRun (ordinaryBound + extra)
    have common : receiptBound + (ordinaryBound + extra) = ordinaryBound + receiptBound + extra := by omega
    rw [common] at actualRun
    rw [← Nat.add_assoc] at originalRun
    have resultSame : result = historyResult := originalRun.symm.trans actualRun
    have historyMember : output ∈ historyOutputs := by
      rw [← actualOutputs, ← resultSame, originalOutputs]
      exact member
    have actual := histories (ordinaryBound + extra) output historyMember
    rw [common] at actual
    exact actual

end MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations
