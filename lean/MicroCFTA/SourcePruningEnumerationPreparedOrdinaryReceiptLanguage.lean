import MicroCFTA.SourcePruningEnumerationPreparedHeadAdmission
import MicroCFTA.SourcePruningEnumerationPreparedCapturedResourcesLanguage
import MicroCFTA.SourcePruningEnumerationSelectedPreparationIdentification
import MicroCFTA.SourcePruningEnumerationPacketLanguage
import MicroCFTA.SourcePruningEnumerationObservedFramesLanguage

/-!
# Backward meaning through actual prepared ordinary entry

One actual stable preparation identifies its source and prepared parent.
The head uses the same framed cache and actual full memo state.
The callback frame restores the same original assignment.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
open EnumerationState EnumerationCorrectness EnumerationValidity InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual preparation and its completed head restore the original ordinary input. -/
theorem CompletedHeadReceipt.sound_ordinary_input
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing}
    {checkEmpty : Bool} {uv handle : Nat} {scs : List Suspended}
    {parentEntry : Cache.Interned InternedBinderProtocol.NodeKey}
    {storedEdges : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragment} {reached : Caller (bits + 2)}
    {saved : SourceEndpointMemo.Memos} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    {originalInventory : Inventory} {originalCaller : Caller (bits + 2)} {originalMemos : Memos}
    {ordinaryBefore : Cached} {preparationBound : Nat} {sourceValue : Node}
    {preparedHeap : InternedConstructorTemplates.State Symbol Constraint} {entered : Core}
    (originalPacket : SourcePruningEnumerationRecursive.Packet formulas solver originalInventory
      originalCaller originalMemos metadata ordinaryBefore)
    (originalReady : EnumerationDriver.Ready uv ordinaryBefore.core)
    (originalStored : ordinaryBefore.core.values[uv]? = some (.unenumerated (some handle) scs))
    (preparing : ∀ extra, SourcePruningEnumerationSelectedPreparation.run
      (preparationBound + extra) (preparationBound + extra) uv originalCaller ordinaryBefore =
      ([.ok ((uv, handle, scs, sourceValue), entered)],
        some (.done (.node parentEntry storedEdges depth free) preparedHeap)))
    (prefixPost : Post formulas solver inventory
      (SourcePruningEnumerationSelectedValueCaller.advance originalCaller preparedHeap) caller memos)
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata
      (EnumerationExpandableIndex.frame entered ordinaryBefore) checkEmpty uv handle scs
      parentEntry storedEdges depth free edge bound fragment reached saved after returnedInventory returnedMemos)
    (canonical : Canonical ordinaryBefore.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      arityAllows edge.children.length (EnumerationCorrectness.suspendedVars entered.counter tries) = true)
    (retained : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ incoming bucket,
        (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs entered.counter tries →
        (match incoming with | .node _ _ _ _ => True | _ => False) ∨
          bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = []) :
    entered.values[uv]? = some (.unenumerated (some handle) scs) ∧
    lookupNode caller.checked.native.machine.heap handle = some sourceValue ∧
    edge ∈ storedEdges ∧
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
      Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient reached.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment after.core →
      (Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient originalCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment ordinaryBefore.core ∧
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient edge (assignment uv) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient (.node parentEntry storedEdges depth free) (assignment uv) ∧
      (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
      Fragments.fill assignment fragment = assignment uv) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient sourceValue (assignment uv) := by
  obtain ⟨_running, sourceLookup, preparationPost, scanPacket, _stable, _ready, _stored,
    _counter, _values, _flags, _waiting, _available, _closed, exactLanguage, exactModel⟩ :=
    SourcePruningEnumerationSelectedPreparation.identify_complete formulas solver originalInventory
      originalCaller originalMemos metadata ordinaryBefore uv handle scs originalPacket originalReady originalStored
      preparationBound sourceValue (.node parentEntry storedEdges depth free) preparedHeap entered preparing
  have entryRun : ExceptT.run (SourcePruningEnumerationEntry.enter
      originalCaller.checked.native.machine.heap preparationBound uv ordinaryBefore.core) =
      [.ok ((uv, handle, scs, sourceValue), entered)] := by
    simpa only [SourcePruningEnumerationSelectedPreparation.run, Nat.add_zero] using
      congrArg Prod.fst (preparing 0)
  have entry : Success
      (SourcePruningEnumerationEntry.enter originalCaller.checked.native.machine.heap preparationBound uv)
      ordinaryBefore.core (uv, handle, scs, sourceValue) entered := by
    rw [Success, entryRun]
    exact List.mem_singleton_self _
  have enteredCanonical := (SourcePruningEnumerationEntry.enter_canonical
    originalCaller.checked.native.machine.heap preparationBound uv ordinaryBefore.core entered uv handle
    scs sourceValue canonical entry).1
  have preparedLookup := lookupNode_keeps originalCaller.checked.native.machine.heap
    (SourcePruningEnumerationSelectedValueCaller.advance originalCaller preparedHeap).checked.native.machine.heap
    preparationPost.effects.keeps handle sourceValue sourceLookup
  have headLookup := lookupNode_keeps
    (SourcePruningEnumerationSelectedValueCaller.advance originalCaller preparedHeap).checked.native.machine.heap
    caller.checked.native.machine.heap prefixPost.effects.keeps handle sourceValue preparedLookup
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := receipt.admission.packet.valid
  obtain ⟨tries, residual, projected⟩ := receipt.projected
  have reserved : SourcePruningEnumerationIncomingReservation.Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs entered.counter tries) := by
    simpa only [SourcePruningEnumerationNativeBranchCompletion.edgeCost, receipt.allowed,
      projected, ↓reduceIte, EnumerationExpandableIndex.frame] using receipt.admission.reserved
  have pending := EnumerationReferences.pending_inputs
    (EnumerationExpandableIndex.frame entered ordinaryBefore).core receipt.admission.packet.pending
    uv (some handle) scs receipt.admission.stored
  have sound := SourcePruningEnumerationCapturedEdge.diagonal_complete_sound_prepared_resources
    seed formulas solver inventory caller (EnumerationExpandableIndex.frame entered ordinaryBefore)
    checkEmpty uv handle scs parentEntry storedEdges depth free edge roots memos
    receipt.admission.packet.context receipt.admission.ready receipt.admission.stored
    sourceValue headLookup receipt.admission.parentAvailable receipt.admission.parentClosed
    (exactLanguage (SourceEqualityPCSGuard.holds formulas solver)) realized receipt.admission.selected
    paths counts flags pending receipt.allowed tries residual projected receipt.admission.bounded
    reserved receipt.admission.known enteredCanonical nonterminal (freshArity tries residual projected)
    (retained tries residual projected) receipt.running
  have captured := SourcePruningEnumerationRecursive.captured_post_semantics
    formulas solver originalInventory inventory
    (SourcePruningEnumerationSelectedValueCaller.advance originalCaller preparedHeap) caller
    originalMemos memos metadata (EnumerationExpandableIndex.frame entered ordinaryBefore) scanPacket prefixPost
  refine ⟨receipt.admission.stored, headLookup, receipt.admission.selected, ?_⟩
  intro ambient assignment satisfied
  obtain ⟨⟨headSatisfied, edgeAccepted, parentAccepted, suspended, filled⟩, sourceAccepted⟩ :=
    sound ambient assignment satisfied
  have scanSatisfied := (captured.2 ambient
    (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment).mp headSatisfied
  have originalSatisfied := (exactModel (SourceEqualityPCSGuard.holds formulas solver) ambient
    (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment).1.mp scanSatisfied
  exact ⟨⟨originalSatisfied, edgeAccepted, parentAccepted, suspended, filled⟩, sourceAccepted⟩

/-- Actual false recording and its prepared head restore the original ordinary input. -/
theorem CompletedHeadReceipt.sound_ordinary_callback_input
    {seed : Seed} {inherited : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing}
    {checkEmpty : Bool} {uv handle : Nat} {scs : List Suspended}
    {parentEntry : Cache.Interned InternedBinderProtocol.NodeKey}
    {storedEdges : List (EdgeValue Symbol Constraint)} {depth : Nat}
    {free : List InternedBinderProtocol.Reference} {edge : EdgeValue Symbol Constraint}
    {bound : Nat} {fragment : Fragment} {reached : Caller (bits + 2)}
    {saved : SourceEndpointMemo.Memos} {after : Cached}
    {returnedInventory : Inventory} {returnedMemos : Memos}
    {originalInventory : Inventory} {originalCaller : Caller (bits + 2)} {originalMemos : Memos}
    {ordinaryBefore : Cached} {preparationBound : Nat} {sourceValue : Node}
    {preparedHeap : InternedConstructorTemplates.State Symbol Constraint} {entered : Core}
    (originalPacket : SourcePruningEnumerationRecursive.Packet formulas solver originalInventory
      originalCaller originalMemos metadata ordinaryBefore)
    (originalReady : EnumerationDriver.Ready uv ordinaryBefore.core)
    (originalStored : ordinaryBefore.core.values[uv]? = some (.unenumerated (some handle) scs))
    (preparing : ∀ extra, SourcePruningEnumerationSelectedPreparation.run
      (preparationBound + extra) (preparationBound + extra) uv originalCaller ordinaryBefore =
      ([.ok ((uv, handle, scs, sourceValue), entered)],
        some (.done (.node parentEntry storedEdges depth free) preparedHeap)))
    (prefixPost : Post formulas solver inventory
      (SourcePruningEnumerationSelectedValueCaller.advance originalCaller preparedHeap) caller memos)
    (receipt : CompletedHeadReceipt seed inherited formulas solver inventory caller memos metadata
      (EnumerationExpandableIndex.frame entered ordinaryBefore) checkEmpty uv handle scs
      parentEntry storedEdges depth free edge bound fragment reached saved after returnedInventory returnedMemos)
    {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {callbackFuel : Nat} {recorded : Metadata Typing} {callbackAfter : Core}
    (recording : Success
      (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv (.inl fragment))
      after.core (false, recorded) callbackAfter)
    (canonical : Canonical ordinaryBefore.core)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      arityAllows edge.children.length (EnumerationCorrectness.suspendedVars entered.counter tries) = true)
    (retained : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ incoming bucket,
        (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs entered.counter tries →
        (match incoming with | .node _ _ _ _ => True | _ => False) ∨
          bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = []) :
    entered.values[uv]? = some (.unenumerated (some handle) scs) ∧
    lookupNode caller.checked.native.machine.heap handle = some sourceValue ∧
    edge ∈ storedEdges ∧
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
      Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient reached.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment callbackAfter →
      (Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient originalCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment ordinaryBefore.core ∧
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient edge (assignment uv) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient (.node parentEntry storedEdges depth free) (assignment uv) ∧
      (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
      Fragments.fill assignment fragment = assignment uv) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient sourceValue (assignment uv) := by
  obtain ⟨stored, decoded, selected, sound⟩ :=
    CompletedHeadReceipt.sound_ordinary_input originalPacket originalReady originalStored preparing prefixPost receipt
      canonical nonterminal freshArity retained
  refine ⟨stored, decoded, selected, ?_⟩
  intro ambient assignment satisfied
  have callbackMeaning := SourcePruningRecordTypes.recordTypes_success_semantics
    graph templates callbackFuel metadata uv (.inl fragment) after.core callbackAfter (false, recorded)
    receipt.completed.safe.1.total recording
  exact sound ambient assignment ((callbackMeaning _ _ assignment).mp satisfied)

end MicroCFTA.SourcePruningEnumerationPreparedNativeHookResources
