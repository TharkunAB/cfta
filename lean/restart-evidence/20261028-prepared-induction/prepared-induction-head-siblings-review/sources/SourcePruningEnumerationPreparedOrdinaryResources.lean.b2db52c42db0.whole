import MicroCFTA.SourcePruningEnumerationPreparedFiniteSiblingFinishResources
import MicroCFTA.SourcePruningEnumerationPreparedPreparationResources
import MicroCFTA.SourcePruningEnumerationSelectedContinuations
import MicroCFTA.SourcePruningEnumerationSuspendedMass

/-!
# Actual prepared ordinary dispatch with finite recursive callbacks

The preparation producer runs once before the actual value case split.
Its entire packet remains available for every case. An ordinary prepared
parent supplies its actual rows. The captured target remains unchanged.
The native callback runs before each next sibling at its actual endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedNativeOrdinaryResources
open EnumerationState EnumerationCorrectness InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationPreparedReservation (stage ScanReserved)
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningEnumerationPreparedRecursive (Failure continueWith resume endpoint OutcomeResources)
open SourcePruningEnumerationPreparedFiniteSiblingResources (ReceiptAt OutputAt StoppedAt)
attribute [local irreducible] SourcePruningEnumerationPreparedReservation.step
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Result" => SourcePruningEnumerationNativeContinuations.Result
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original current resources fix preparation before the actual ordinary sibling result. -/
theorem complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : SourcePruningEnumerationPreparedRecursive.Complete (bits := bits)
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : ScanReserved bits recursiveFuel
      (seed.1, SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2)
      capturedMass inherited (scalar (SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2) + 1)) :
    ∃ (preparationBound : Nat) (decoded result : Node)
      (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached),
      ((((∀ extra, run (preparationBound + extra) (preparationBound + extra) uv caller before =
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
        (SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2)
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap).checked ∧
      InternedValueMass.value result ≤
        (SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2).mass) ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) heap) ∧
      (∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
        (storedEdges : List (EdgeValue Symbol Constraint))
        (depth : Nat) (free : List InternedBinderProtocol.Reference),
        result = .node parentEntry storedEdges depth free →
        scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false →
        ∃ (scanBound : Nat) (processed : List (Receipt (bits + 2)))
          (outputs : List (Output (bits + 2) Typing)) (afterCaller : Caller (bits + 2))
          (next : Inventory) (final : Memos)
          (folded : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
        ((∀ extra, SourcePruningEnumerationNativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (scanBound + extra) recursiveFuel)
          graph templates stop order (scanBound + extra) metadata uv)
        checkEmpty (scanBound + extra) (scanBound + extra) (scanBound + extra) (scanBound + extra) (scanBound + extra)
        uv scs entered (edgesOf (.node parentEntry storedEdges depth free)) (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos.query = folded) ∧
      Post formulas solver next (SourcePruningEnumerationSelectedValueCaller.advance caller heap) afterCaller final ∧
      Packet formulas solver next afterCaller final metadata entered ∧
      Fits (stage recursiveFuel (seed.1, SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2) capturedMass inherited (edgesOf (.node parentEntry storedEdges depth free)).length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (stage recursiveFuel (seed.1, SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2) capturedMass inherited (edgesOf (.node parentEntry storedEdges depth free)).length).1)
        afterCaller.checked.native.machine.heap ∧
      processed.length ≤ (edgesOf (.node parentEntry storedEdges depth free)).length ∧
      (∀ index receipt, processed[index]? = some receipt →
        ReceiptAt recursiveFuel formulas solver (SourcePruningEnumerationSelectedValueCaller.advance caller heap) entered uv (seed.1, SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2) scs capturedMass inherited index receipt) ∧
      (∀ output ∈ outputs, ∃ index, index < (edgesOf (.node parentEntry storedEdges depth free)).length ∧
        OutputAt recursiveFuel formulas solver (SourcePruningEnumerationSelectedValueCaller.advance caller heap) (seed.1, SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2) capturedMass inherited index output) ∧
      (folded = .complete processed outputs afterCaller final.query ∨
        ∃ current, folded = .stopped processed outputs current ∧
          (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) ∧
          StoppedAt recursiveFuel formulas solver (SourcePruningEnumerationSelectedValueCaller.advance caller heap) entered uv (seed.1, SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2) scs capturedMass inherited processed.length outputs current) ∧
      SourcePruningEnumerationPreparedRecursive.OutcomeResources formulas solver (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
        (stage recursiveFuel (seed.1, SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2) capturedMass inherited (edgesOf (.node parentEntry storedEdges depth free)).length)
        (SourcePruningEnumerationPreparedRecursive.finish uv folded)) ∧
        (∀ extra, SourcePruningEnumerationSelectedContinuations.run
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (preparationBound + scanBound + extra) recursiveFuel)
            graph templates stop order (preparationBound + scanBound + extra) metadata uv)
          checkEmpty (preparationBound + scanBound + extra) (preparationBound + scanBound + extra)
          (preparationBound + scanBound + extra) (preparationBound + scanBound + extra)
          (preparationBound + scanBound + extra) (preparationBound + scanBound + extra)
          (preparationBound + scanBound + extra) uv edgesOf caller before memos.query =
          (([.ok ((uv, handle, scs, decoded), entered.core)],
            some (.done (.node parentEntry storedEdges depth free) heap)), some folded)) ∧
        Post formulas solver next caller afterCaller final ∧
        OutcomeResources formulas solver caller
          (stage recursiveFuel
            (seed.1, SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2)
            capturedMass inherited (edgesOf (.node parentEntry storedEdges depth free)).length)
          (SourcePruningEnumerationPreparedRecursive.finish uv folded)) := by
  obtain ⟨preparationBound, decoded, result, heap, entered, preparation, preparedKnown⟩ :=
    SourcePruningEnumerationSelectedPreparation.complete_resources_known formulas solver inventory caller memos
      metadata before uv handle scs packet ready stored seed.2 bounded (fun guard => guard ∈ seed.1) known
  have retained := And.intro preparation preparedKnown
  obtain ⟨prepared, normalizedFits, _normalizedMass⟩ := preparation
  obtain ⟨preparedRun, _lookup, preparationPost, enteredPacket, stable, enteredReady, enteredStored,
    _counter, values, sameFlags, sameWaiting, available, closed, _language, _models⟩ := prepared
  have framed : EnumerationExpandableIndex.frame entered.core before = entered := by
    cases entered with
    | mk core expandable waiting =>
        simp only [EnumerationExpandableIndex.frame] at *
        congr 1
        · exact sameFlags.symm
        · exact sameWaiting.symm
  refine ⟨preparationBound, decoded, result, heap, entered, retained, ?_⟩
  intro parentEntry storedEdges depth free same nonterminal
  subst result
  have enteredMass : suspendedBound entered.core ≤ capturedMass := by
    rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core entered.core values]
    exact initialMass
  have heapFits : SourceCurrentConstrainedCapRequiredResources.HeapFits
      (SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2) heap :=
    SourceCurrentConstrainedCapRequiredResources.of_checked
      (profile := SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2)
      (before := (SourcePruningEnumerationSelectedValueCaller.advance caller heap).checked) normalizedFits
  have rowsBound := SourceCurrentConstrainedCapRequiredResources.node_width heapFits available
  have selectedBound : (edgesOf (.node parentEntry storedEdges depth free)).length ≤
      scalar (SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2) + 1 :=
    Nat.le_trans (selectionLength parentEntry storedEdges depth free)
      (Nat.le_trans rowsBound (Nat.le_succ _))
  obtain ⟨scanBound, processed, outputs, afterCaller, next, final, folded,
    scanRun, scanPost, captured, afterFits, afterKnown, processedLength, receipts, outputPackets, shape, finished⟩ :=
    SourcePruningEnumerationPreparedFiniteSiblingResources.alternatives_finite_finish_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel
      (seed.1, SourcePruningEnumerationSelectedValueCaller.normalizationProfile seed.2)
      formulas solver recursive inventory (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
      memos entered uv handle scs parentEntry storedEdges (edgesOf (.node parentEntry storedEdges depth free))
      depth free enteredPacket enteredReady enteredStored available closed
      (selectionMembers parentEntry storedEdges depth free)
      (EnumerationReferences.incoming_read uv before.core entered.core stable incoming)
      normalizedFits preparedKnown selectionMembers selectionLength capturedMass inherited enteredMass
      inheritedLength (reserved.prefix selectedBound)
  refine ⟨scanBound, processed, outputs, afterCaller, next, final, folded,
    ⟨scanRun, scanPost, captured, afterFits, afterKnown, processedLength, receipts, outputPackets, shape, finished⟩,
    ?_, preparationPost.trans scanPost, finished.post preparationPost⟩
  intro extra
  have preparationAt : SourcePruningEnumerationSelectedPreparation.run
      (preparationBound + scanBound + extra) (preparationBound + scanBound + extra) uv caller before =
      ([.ok ((uv, handle, scs, decoded), entered.core)],
        some (.done (.node parentEntry storedEdges depth free) heap)) := by
    simpa only [Nat.add_assoc] using preparedRun (scanBound + extra)
  have scanAt := scanRun (preparationBound + extra)
  have common : scanBound + (preparationBound + extra) = preparationBound + scanBound + extra := by omega
  rw [common] at scanAt
  have dispatch := SourcePruningEnumerationSelectedContinuations.ordinary
    (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (preparationBound + scanBound + extra) recursiveFuel)
      graph templates stop order (preparationBound + scanBound + extra) metadata uv)
    checkEmpty (preparationBound + scanBound + extra) (preparationBound + scanBound + extra)
    (preparationBound + scanBound + extra) (preparationBound + scanBound + extra)
    (preparationBound + scanBound + extra) (preparationBound + scanBound + extra)
    (preparationBound + scanBound + extra) uv uv handle scs decoded parentEntry storedEdges depth free
    heap entered.core edgesOf caller before memos.query preparationAt nonterminal
  rw [framed, scanAt] at dispatch
  exact dispatch

end MicroCFTA.SourcePruningEnumerationPreparedNativeOrdinaryResources
