import MicroCFTA.SourcePruningEnumerationPrefixRightIdentity
import MicroCFTA.SourcePruningEnumerationRecursivePrefixLanguage
import MicroCFTA.SourcePruningEnumerationBoundaryAction
import MicroCFTA.SourcePruningEnumerationBoundaryFreshness

/-!
# Exact indexed-prefix state at a retained recursive boundary

Original prefix resources identify the actual action and both index tables.
The native boundary result retains the checked handle and its heap.
The Right event retains the checked core and the original metadata.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- An actual retained boundary prefix supplies the same checked key, packet, and exact Right endpoint. -/
theorem narrowed_boundary_identity
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (checked : Core) (value : Node) (selectedAction : EnumerateM Symbol Constraint Unit)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (reached : Caller width) (queries : SourceEndpointMemo.Memos)
    (actionRaw : Option (List (Except Error (Unit × Core))))
    (after : Cached) (updated : Metadata Typing) (rightCore : Core)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query))
    (observed : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before memos.query =
        .narrowed checked (.done (value, some selectedAction) heap) reached queries actionRaw (some after)
          (some [.ok ((false, updated), rightCore)]) none)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true) :
    heap = caller.checked.native.machine.heap ∧ reached = caller ∧ queries = memos.query ∧
      selectedAction = pure () ∧ actionRaw = some [.ok ((), checked)] ∧
      after = EnumerationExpandableIndex.frame checked before ∧ updated = metadata ∧ rightCore = checked ∧
      Packet formulas solver inventory caller memos metadata after ∧ EnumerationDriver.Ready uv after.core ∧
      ∃ (handle : Nat) (scs : List Suspended) (readAfter : Core),
        before.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
        readAfter.values[uv]? = some (.unenumerated (some handle) scs) ∧
        after.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
        lookupNode caller.checked.native.machine.heap handle = some value ∧ encodeNode value = some handle ∧
        ExceptT.run (getValue fuel uv before.core) = [.ok (.unenumerated (some handle) scs, readAfter)] ∧
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          fuel uv handle scs readAfter) = [.ok (false, checked)] ∧
        Frame before.core readAfter ∧ Success (representative fuel uv) readAfter uv checked ∧
        recursionKey handle scs ∉ after.core.recursionAncestry uv := by
  have actualValid := valid
  rw [observed] at actualValid
  have full := actualValid.2.1
  simp only [finish, Valid] at full
  obtain ⟨handle, scs, readAfter, reading, checking, oldValue, ownValue, ownHeap,
    ownAction, _final, decoded, _narrowed, preparing, samePrepared, _reached,
    _queries, _post, _saved, shape⟩ := full
  have fields := MergedSourceComparison.Result.done.inj samePrepared
  have valuesSame : ownValue = value := (congrArg Prod.fst fields.1).symm
  have actionsSame : ownAction = selectedAction := (Option.some.inj (congrArg Prod.snd fields.1)).symm
  have heapsSame : ownHeap = heap := fields.2.symm
  subst ownValue
  subst ownAction
  subst ownHeap
  rcases shape with ⟨_empty, _raw, noCache, _right, _ordinary⟩ |
    ⟨newHandle, cached, _nonempty, encoded, _raw, candidate, cacheValid, safe,
      pending, readyAfter, storedAfter, _waiting, _right, _ordinary⟩
  · cases noCache
  · have cachedSame : after = cached := Option.some.inj candidate
    subst cached
    have readyBefore := SourcePruningEnumerationRecursive.packet_selected_ready formulas solver inventory
      stop order metadata caller memos before uv packet chosen
    have readingSuccess : Success (getValue fuel uv) before.core (.unenumerated (some handle) scs) readAfter := by
      rw [Success, reading]
      exact List.mem_singleton_self _
    have readFrame := (getValue_frame fuel uv before.core readAfter _ packet.safe.1.total readingSuccess).1
    have readStored := (EnumerationDriver.getValue_root fuel uv before.core readAfter _
      readyBefore.safe readyBefore.inside readyBefore.root readingSuccess).2.2.2
    have originalStored : before.core.values[uv]? = some (.unenumerated (some handle) scs) := by
      simpa only [readFrame.values] using readStored
    obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
    obtain ⟨original, originalDecoded, available, closed⟩ := realized uv handle scs originalStored
    have originalSame : original = oldValue := Option.some.inj (originalDecoded.symm.trans decoded)
    subst original
    have nativeReady := packet.context.ready.semantic.ready
    have originalEncoded := SourcePruningEnumerationIdentity.lookup_encode caller.checked.native.machine.heap
      handle oldValue nativeReady.semantic.1.normal.facts.coherent decoded
    have retained := SourcePruningEnumerationAction.prepare_boundary_retained holeKey fits admits metadata
      fuel fuel uv handle scs oldValue caller.checked.native.machine.heap value (some selectedAction) heap
      nativeReady available closed originalEncoded preparing boundary
    have pureAction : selectedAction = pure () := Option.some.inj retained.2.2
    have publicEncoded : encodeNode value = some handle := by
      simpa only [retained.1] using originalEncoded
    have handleSame : newHandle = handle := Option.some.inj (encoded.symm.trans publicEncoded)
    subst newHandle
    have raw : ExceptT.run (selectedAction checked) = [.ok ((), checked)] := by
      rw [pureAction]
      rfl
    have adapted : SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv handle handle scs before checked =
        some (EnumerationExpandableIndex.frame checked before) := by
      simp only [SourcePruningEnumerationNarrowAdapter.adapt, ↓reduceIte]
    have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv
        (.inr handle) (EnumerationExpandableIndex.frame checked before).core) =
        [.ok ((false, metadata), checked)] := by
      rw [SourcePruningRecordTypes.recordTypes_inr]
      rfl
    have advanced : SourceCurrentAllocatedPartialState.advance caller
        (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge = caller := by
      rw [retained.2.1]
      rfl
    have exactPrefix : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query =
        .narrowed checked (.done (value, some selectedAction) heap) caller memos.query
          (some [.ok ((), checked)]) (some (EnumerationExpandableIndex.frame checked before))
          (some [.ok ((false, metadata), checked)]) none := by
      simp only [runPrefix, reading, checking, decoded, preparing, raw, publicEncoded, adapted, recorded,
        MergedSourceComparison.Result.state]
      rw [advanced]
      rfl
    obtain ⟨_checked, _prepared, reachedSame, queriesSame, rawSame, cacheEqual, rightEqual, _ordinary⟩ :=
      Result.narrowed.inj (observed.symm.trans exactPrefix)
    have cacheSame : after = EnumerationExpandableIndex.frame checked before := Option.some.inj cacheEqual
    have rowSame := Except.ok.inj (List.cons.inj (Option.some.inj rightEqual)).1
    have metadataSame : updated = metadata :=
      congrArg (fun packet : (Bool × Metadata Typing) × Core => packet.1.2) rowSame
    have coreSame : rightCore = checked := congrArg Prod.snd rowSame
    have endpointPacket : Packet formulas solver inventory caller memos metadata after := by
      refine ⟨packet.context, safe, pending, ?_, ?_, ?_⟩
      · simpa only [reachedSame] using cacheValid
      · obtain ⟨level, frontier, ordered⟩ := packet.ordered
        exact ⟨level, frontier, actualValid.2.2.2 level frontier ordered⟩
      · simpa only [actualValid.2.2.1] using packet.bounded
    have checkingSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
        fuel uv handle scs) readAfter false checked := by
      rw [Success, checking]
      exact List.mem_singleton_self _
    have oldBoundary : MergedOrdinaryHeight.recursiveBoundary oldValue = true := by
      simpa only [retained.1] using boundary
    obtain ⟨root, resolving, fresh⟩ := SourcePruningEnumerationRecursionOrder.checkRepeated_false_fresh
      caller.checked.native.machine.heap fuel uv handle scs oldValue readAfter checked decoded oldBoundary checkingSuccess
    have readReady := (EnumerationDriver.getValue_ready fuel uv before.core readAfter _ readyBefore readingSuccess).1
    have rootSame := (EnumerationDriver.representative_root fuel uv root readAfter checked
      readReady.safe readReady.inside readReady.root resolving).1
    subst root
    refine ⟨retained.2.1, reachedSame, queriesSame, pureAction, rawSame, cacheSame,
      metadataSame, coreSame, endpointPacket, readyAfter, handle, scs, readAfter,
      originalStored, readStored, storedAfter, ?_, publicEncoded, reading, checking, readFrame, resolving, ?_⟩
    · simpa only [retained.1] using decoded
    · simpa only [cacheSame, EnumerationExpandableIndex.frame] using fresh

end MicroCFTA.SourcePruningEnumerationSelectedStep
