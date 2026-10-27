import MicroCFTA.SourcePruningEnumerationPrefixCanonicalHistory
import MicroCFTA.SourcePruningEnumerationOrdinaryReceiptLanguage

/-!
# One actual selected prefix and its completed ordinary callback

The prefix receipt supplies its retained cache and native endpoint.
The ordinary entry and head receipts use that same cache.
The false callback supplies its actual returned core.
The backward law keeps the structural semantic gates explicit.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationValidity EnumerationCompressionFrame InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
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
attribute [local instance] SourcePruningEnumerationEntry.entryMonadList

private theorem entry_values
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel uv : Nat)
    (before after : Core) (target handle : Nat) (bucket : List Suspended) (decoded : Node)
    (total : UnionFind.Total before.representatives)
    (observed : Success (SourcePruningEnumerationEntry.enter heap fuel uv)
      before (target, handle, bucket, decoded) after) : after.values = before.values := by
  unfold SourcePruningEnumerationEntry.enter at observed
  obtain ⟨value, read, reading, continued⟩ := (success_bind _ _ _ _ _).mp observed
  have readFrame := (getValue_frame fuel uv before read value total reading).1
  cases value with
  | enumerated fragment => exact (reject_unsuccessful read after _ continued).elim
  | eliminated => exact (reject_unsuccessful read after _ continued).elim
  | unenumerated node scs =>
      cases node with
      | none => exact (reject_unsuccessful read after _ continued).elim
      | some storedHandle =>
          obtain ⟨found, compressed, compressing, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have fullFrame := readFrame.trans
            (representative_frame fuel uv found read compressed (readFrame.total total) compressing)
          cases lookup : lookupNode heap storedHandle with
          | none =>
              simp only [lookup] at continued
              exact (success_failure .unresolvedReference compressed after _ continued).elim
          | some actual =>
              simp only [lookup] at continued
              obtain ⟨ignored, entered, modifying, final⟩ := (success_bind _ _ _ _ _).mp continued
              cases ignored
              obtain rfl := (EnumerationDriver.modify_success _ compressed entered).mp modifying
              obtain ⟨_same, rfl⟩ := (success_pure _ _ _ _).mp final
              exact fullFrame.values

/-- A completed actual ordinary callback restores the original selected input. -/
theorem narrowed_receipt_sound
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
    (ordinaryCaller : Caller (bits + 2)) (ordinaryMemos : Memos) (narrowed : Cached)
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
    (entryFuel target entryHandle : Nat) (scs : List Suspended) (entryValue : Node) (entered : Cached)
    (entry : Success
      (SourcePruningEnumerationEntry.enter ordinaryCaller.checked.native.machine.heap entryFuel uv)
      narrowed.core (target, entryHandle, scs, entryValue) entered.core)
    (enteredPacket : SourcePruningEnumerationRecursive.Packet formulas solver inventory
      ordinaryCaller ordinaryMemos metadata entered)
    (seed : Seed) (inherited : Nat)
    (headInventory : Inventory) (headCaller : Caller (bits + 2)) (headMemos : Memos)
    (edge : EdgeValue Symbol Constraint) (headBound : Nat)
    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2))
    (saved : SourceEndpointMemo.Memos) (after : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos)
    (prefixPost : SourceCurrentAllocatedPartialInvariant.Post formulas solver headInventory
      ordinaryCaller headCaller headMemos)
    (receipt : SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt seed inherited
      formulas solver headInventory headCaller headMemos metadata entered checkEmpty target scs edge headBound
      fragment reached saved after returnedInventory returnedMemos)
    (callbackFuel : Nat) (recorded : Metadata Typing) (callbackAfter : Core)
    (recording : Success
      (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata target (.inl fragment))
      after.core (false, recorded) callbackAfter)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (freshArity : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      arityAllows edge.children.length (EnumerationCorrectness.suspendedVars entered.core.counter tries) = true)
    (retained : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ incoming bucket,
        (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs entered.core.counter tries →
        (match incoming with | .node _ _ _ _ => True | _ => False) ∨
          bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ bucket = []) :
    ∃ (handle : Nat) (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (storedEdges : List (EdgeValue Symbol Constraint)) (depth : Nat)
      (free : List InternedBinderProtocol.Reference),
      narrowed.core.values[target]? = some (.unenumerated (some handle) scs) ∧
      lookupNode headCaller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free) ∧
      edge ∈ storedEdges ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient reached.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment callbackAfter →
        Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment before.core ∧
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment target) ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient (.node parentEntry storedEdges depth free) (assignment target) ∧
        (∀ sc ∈ scs, Suspended.Holds assignment (assignment target) sc) ∧
        Fragments.fill assignment fragment = assignment target := by
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
  have narrowedPacket : SourcePruningEnumerationRecursive.Packet formulas solver inventory
      ordinaryCaller ordinaryMemos metadata narrowed := by
    refine ⟨enteredPacket.context, safe, pending, cacheValid, ?_, ?_⟩
    · obtain ⟨level, frontier, originalOrder⟩ := packet.ordered
      exact ⟨level, frontier, ordered level frontier originalOrder⟩
    · simpa only [counter] using packet.bounded
  have ready := SourcePruningEnumerationRecursive.packet_selected_ready formulas solver inventory stop order
    metadata caller memos before uv packet chosen
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  have meaning := prefix_semantics holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory fuel uv caller before memos packet.context ready realized valid
  rw [actual] at meaning
  obtain ⟨handle, parentEntry, storedEdges, depth, free, stored, decoded, selected, sound⟩ :=
    SourcePruningEnumerationNativeHookResources.CompletedHeadReceipt.sound_ordinary_callback_input
      narrowedPacket entry enteredPacket prefixPost receipt recording narrowedCanonical nonterminal freshArity retained
  have values := entry_values ordinaryCaller.checked.native.machine.heap entryFuel uv narrowed.core
    entered.core target entryHandle scs entryValue narrowedPacket.safe.1.total entry
  have originalStored : narrowed.core.values[target]? = some (.unenumerated (some handle) scs) := by
    simpa only [values] using stored
  refine ⟨handle, parentEntry, storedEdges, depth, free, originalStored, decoded, selected, ?_⟩
  intro ambient assignment satisfied
  obtain ⟨narrowedHolds, edgeHolds, parentHolds, suspendedHolds, filled⟩ := sound ambient assignment satisfied
  exact ⟨meaning ambient _ assignment narrowedHolds, edgeHolds, parentHolds, suspendedHolds, filled⟩

end MicroCFTA.SourcePruningEnumerationSelectedStep
