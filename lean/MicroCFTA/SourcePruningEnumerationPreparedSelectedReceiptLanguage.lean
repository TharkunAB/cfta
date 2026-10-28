import MicroCFTA.SourcePruningEnumerationPrefixCanonicalHistory
import MicroCFTA.SourcePruningEnumerationPreparedOrdinaryReceiptLanguage

/-!
# One actual selected prefix and its prepared ordinary callback

The prefix supplies its actual native caller and retained cache.
The same preparation identifies the original source and prepared parent.
The false callback restores the original selected input assignment.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationValidity EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual narrowed prefix and prepared ordinary callback restore the selected input. -/
theorem narrowed_receipt_sound_prepared
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller (bits + 2)) (before : Cached) (memos : Memos)
    (checked : Core)
    (prepared : MergedSourceComparison.Result Symbol Constraint
      (Node × Option (EnumerateM Symbol Constraint Unit)))
    (ordinaryInventory : Inventory) (ordinaryCaller : Caller (bits + 2))
    (ordinaryMemos : Memos) (narrowed : Cached)
    (action : Option (List (Except Error (Unit × Core))))
    (right : Option (List (Except Error ((Bool × Metadata Typing) × Core))))
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (canonical : Canonical before.core)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query))
    (actual : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before memos.query =
        .narrowed checked prepared ordinaryCaller ordinaryMemos.query action (some narrowed) right none)
    (ordinaryPost : Post formulas solver ordinaryInventory caller ordinaryCaller ordinaryMemos)
    (handle : Nat) (scs : List Suspended) (sourceValue : Node)
    (narrowedReady : EnumerationDriver.Ready uv narrowed.core)
    (narrowedStored : narrowed.core.values[uv]? = some (.unenumerated (some handle) scs))
    (preparationBound : Nat) (preparedHeap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat)
    (free : List InternedBinderProtocol.Reference)
    (preparing : ∀ extra, SourcePruningEnumerationSelectedPreparation.run
      (preparationBound + extra) (preparationBound + extra) uv ordinaryCaller narrowed =
      ([.ok ((uv, handle, scs, sourceValue), entered)],
        some (.done (.node parentEntry storedEdges depth free) preparedHeap)))
    (seed : Seed) (inherited : Nat)
    (headInventory : Inventory) (headCaller : Caller (bits + 2)) (headMemos : Memos)
    (edge : EdgeValue Symbol Constraint) (headBound : Nat)
    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2))
    (saved : SourceEndpointMemo.Memos) (after : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos)
    (prefixPost : Post formulas solver headInventory
      (SourcePruningEnumerationSelectedValueCaller.advance ordinaryCaller preparedHeap) headCaller headMemos)
    (receipt : SourcePruningEnumerationPreparedNativeHookResources.CompletedHeadReceipt seed inherited
      formulas solver headInventory headCaller headMemos metadata
      (EnumerationExpandableIndex.frame entered narrowed) checkEmpty uv handle scs parentEntry storedEdges depth free edge
      headBound fragment reached saved after returnedInventory returnedMemos)
    (callbackFuel : Nat) (recorded : Metadata Typing) (callbackAfter : Core)
    (recording : Success
      (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv (.inl fragment))
      after.core (false, recorded) callbackAfter)
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
    narrowed.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
    lookupNode headCaller.checked.native.machine.heap handle = some sourceValue ∧
    edge ∈ storedEdges ∧
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
      Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient reached.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment callbackAfter →
      (Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment before.core ∧
      InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient edge (assignment uv) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient (.node parentEntry storedEdges depth free) (assignment uv) ∧
      (∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc) ∧
      Fragments.fill assignment fragment = assignment uv) ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
        ambient sourceValue (assignment uv) := by
  have narrowedCanonical := prefix_canonical holeKey fits admits graph templates checkEmpty edgesOf stop order
    metadata formulas solver inventory fuel uv caller before memos canonical valid
  rw [actual] at narrowedCanonical
  have concreteValid := valid
  rw [actual] at concreteValid
  have cacheFacts := SourcePruningEnumerationPrefixPacket.prefix_cache_valid
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    fuel uv caller before memos
    (.narrowed checked prepared ordinaryCaller ordinaryMemos.query action (some narrowed) right none) concreteValid
  obtain ⟨cacheValid, safe, pending, counter, ordered⟩ := cacheFacts
  have narrowedPacket : SourcePruningEnumerationRecursive.Packet formulas solver ordinaryInventory
      ordinaryCaller ordinaryMemos metadata narrowed := by
    refine ⟨ordinaryPost.context, safe, pending, cacheValid, ?_, ?_⟩
    · obtain ⟨level, frontier, originalOrder⟩ := packet.ordered
      exact ⟨level, frontier, ordered level frontier originalOrder⟩
    · simpa only [counter] using packet.bounded
  have ready := SourcePruningEnumerationRecursive.packet_selected_ready formulas solver inventory stop order
    metadata caller memos before uv packet chosen
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  have meaning := prefix_semantics holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory fuel uv caller before memos packet.context ready realized valid
  rw [actual] at meaning
  obtain ⟨_stored, decoded, selected, sound⟩ :=
    SourcePruningEnumerationPreparedNativeHookResources.CompletedHeadReceipt.sound_ordinary_callback_input
      narrowedPacket narrowedReady narrowedStored preparing prefixPost receipt recording
      narrowedCanonical nonterminal freshArity retained
  refine ⟨narrowedStored, decoded, selected, ?_⟩
  intro ambient assignment satisfied
  obtain ⟨⟨narrowedHolds, edgeHolds, parentHolds, suspendedHolds, filled⟩, sourceHolds⟩ :=
    sound ambient assignment satisfied
  exact ⟨⟨meaning ambient _ assignment narrowedHolds, edgeHolds, parentHolds, suspendedHolds, filled⟩,
    sourceHolds⟩

end MicroCFTA.SourcePruningEnumerationSelectedStep
