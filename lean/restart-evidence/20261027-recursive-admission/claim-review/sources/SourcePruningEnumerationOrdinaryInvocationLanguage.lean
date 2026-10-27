import MicroCFTA.SourcePruningEnumerationOrdinaryInvocationResources
import MicroCFTA.SourcePruningEnumerationOrdinaryReceiptLanguage

/-!
# Actual ordinary invocation language from original finite resources

The original finite producer supplies each actual entered cache and head.
The semantic law uses its own completed endpoint and original parent.
Structural gates remain explicit after the original resource result.
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

/-- Original finite resources retain the full ordinary result and each actual invocation language law. -/
theorem ordinary_finite_complete_invocation_semantics
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
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
    (∀ extra (fragment : Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached),
      SourcePruningEnumerationHookInvocation.OrdinaryInvocation
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv edgesOf caller before memos.query fragment reached saved after →
      ∃ edge ∈ edgesOf (.node parentEntry storedEdges depth free),
        ∃ (headSeed : Seed) (headInventory : Inventory) (headCaller : Caller (bits + 2))
          (headMemos : Memos) (headBound : Nat) (returnedInventory : Inventory) (returnedMemos : Memos),
          Post formulas solver headInventory caller headCaller headMemos ∧
          SourcePruningEnumerationCapturedEdge.run checkEmpty
            (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
            uv scs edge headCaller entered headMemos.query = some (.complete fragment reached saved after) ∧
          SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt headSeed inherited formulas solver
            headInventory headCaller headMemos metadata entered checkEmpty uv scs edge headBound
            fragment reached saved after returnedInventory returnedMemos) ∧
      ∀ extra (fragment : Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached),
        SourcePruningEnumerationHookInvocation.OrdinaryInvocation
          (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
            (bound + extra) recursiveFuel) graph templates stop order (bound + extra) metadata uv)
          checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          uv edgesOf caller before memos.query fragment reached saved after →
        ∃ edge ∈ edgesOf (.node parentEntry storedEdges depth free),
          EnumerationValidity.Canonical before.core →
          (∀ tries residual,
            SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
            EnumerationState.arityAllows edge.children.length
              (EnumerationCorrectness.suspendedVars before.core.counter tries) = true) →
          (∀ tries residual,
            SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
            ∀ incoming bucket,
              (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
              (match incoming with | .node _ _ _ _ => True | _ => False) ∨
                bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = []) →
          ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
            EnumerationCorrectness.Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient reached.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment after.core →
            EnumerationCorrectness.Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment before.core ∧
            InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient edge (assignment uv) ∧
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient (.node parentEntry storedEdges depth free) (assignment uv) ∧
            (∀ sc ∈ scs, EnumerationState.Suspended.Holds assignment (assignment uv) sc) ∧
            Fragments.fill assignment fragment = assignment uv := by
  obtain ⟨bound, entered, processed, outputs, afterCaller, next, final, result,
    entryRun, stable, counter, values, sameFlags, sameWaiting, enteredPacket,
    ordinaryRun, scanRun, post, captured, returnedFits, returnedKnown, processedLength,
    receipts, outputCertificates, shape, finished, rich⟩ :=
    ordinary_finite_complete_invocation_resources holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata recursiveFuel seed formulas solver inventory caller memos before uv handle scs parentEntry storedEdges
      depth free packet ready stored decoded selected incoming nonterminal bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, entered, processed, outputs, afterCaller, next, final, result,
    entryRun, stable, counter, values, sameFlags, sameWaiting, enteredPacket,
    ordinaryRun, scanRun, post, captured, returnedFits, returnedKnown, processedLength,
    receipts, outputCertificates, shape, finished, rich, ?_⟩
  intro extra fragment reached saved after invocation
  obtain ⟨edge, member, headSeed, headInventory, headCaller, headMemos, headBound,
    returnedInventory, returnedMemos, prefixPost, _headRun, receipt⟩ := rich extra fragment reached saved after invocation
  refine ⟨edge, member, ?_⟩
  intro canonical freshArity retained ambient assignment satisfied
  have entrySuccess : EnumerationCorrectness.Success
      (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap (bound + extra) uv)
      before.core (uv, handle, scs, .node parentEntry storedEdges depth free) entered.core := by
    rw [EnumerationCorrectness.Success, entryRun extra]
    exact List.mem_singleton_self _
  have localFresh : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      EnumerationState.arityAllows edge.children.length
        (EnumerationCorrectness.suspendedVars entered.core.counter tries) = true := by
    simpa only [counter] using freshArity
  have localRetained : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ incoming bucket,
        (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs entered.core.counter tries →
        (match incoming with | .node _ _ _ _ => True | _ => False) ∨
          bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = [] := by
    simpa only [counter] using retained
  obtain ⟨actualHandle, actualEntry, actualRows, actualDepth, actualFree,
    actualStored, actualDecoded, _actualSelected, sound⟩ :=
    SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt.sound_ordinary_input
      packet entrySuccess enteredPacket prefixPost receipt canonical nonterminal localFresh localRetained
  have enteredStored : entered.core.values[uv]? = some (.unenumerated (some handle) scs) := by
    simpa only [values] using stored
  have handleSame : actualHandle = handle := by
    have same := actualStored.symm.trans enteredStored
    simpa only [Option.some.injEq, UVarValue.unenumerated.injEq, true_and, and_true] using same
  subst actualHandle
  have originalDecoded := lookupNode_keeps _ _ prefixPost.effects.keeps handle _ decoded
  have parentSame := Option.some.inj (actualDecoded.symm.trans originalDecoded)
  cases parentSame
  exact sound ambient assignment satisfied

end MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations
