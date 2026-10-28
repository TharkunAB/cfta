import MicroCFTA.SourcePruningEnumerationPreparedHistoryBackwardArity
import MicroCFTA.SourcePruningEnumerationPreparedArityHeapHead
import MicroCFTA.SourcePruningEnumerationPreparedOrdinaryReceiptLanguage
import MicroCFTA.SourcePruningEnumerationPreparedOpaquePointLanguage
import MicroCFTA.SourcePruningEnumerationPreparedDischargedRetention
import MicroCFTA.SourcePruningEnumerationPreparedOpaqueHistoryAttachment
import MicroCFTA.SourcePruningEnumerationPreparedParkedMarkerAttachment
import MicroCFTA.SourcePruningEnumerationPreparedResourceHistoryCanonical
import MicroCFTA.SourcePruningEnumerationPrefixLanguage

/-!
# Backward assignment meaning of the actual prepared history

The same final output supplies its arity heap and structural discharge.
Actual native Posts reflect that arity to each earlier ordinary head input.
The recorded tail and discharge derive the local retention conditions.
Actual callback frames restore the same complete assignment.
The finite resource producer must derive the final arity heap separately.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationValidity InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Output)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "ArityHeap" => SourcePruningEnumerationArityOrigins.Heap
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
variable {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
variable {checkEmpty : Bool} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
variable {stop : Option (Metadata Typing → Nat → Bool)}
variable {order : Metadata Typing → List Nat → Option Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {workFuel recursiveFuel : Nat} {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos}
variable {metadata : Metadata Typing} {before : Cached} {seed : Seed} {ceiling : Nat}
variable {next : Option Next} {output : Output (bits + 2) Typing}
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
attribute [local irreducible] SourcePruningEnumerationSelectedValueCaller.normalizationProfile

/-- A discharged actual history restores the original whole assignment from its own output model. -/
theorem ResourceHistory.sound
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (actualNext : next = SourcePruningEnumerationRestart.decision stop order metadata before)
    (canonical : Canonical before.core)
    (finalOutputHeap : ArityHeap output.caller.checked.native.machine.heap)
    (discharged : SourcePruningEnumerationRendering.Discharged output.cache.core) :
    ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
      Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient output.caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment output.cache.core →
      Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        assignment before.core := by
  revert actualNext canonical finalOutputHeap discharged
  induction history with
  | stopped _admission =>
      intro _actualNext _canonical _finalOutputHeap _discharged ambient assignment satisfied
      exact satisfied
  | done _admission =>
      intro _actualNext _canonical _finalOutputHeap _discharged ambient assignment satisfied
      exact satisfied
  | @parked fuel inventory caller memos metadata before seed ceiling uv checked parked updated next core
      tailSeed tailCeiling output admission valid observed tail _ih =>
      intro actualNext _canonical _finalOutputHeap discharged
      obtain ⟨_handle, _bucket, _value, _stored, _decoded, _boundary, _created, _retained,
        _outputDecoded, impossible⟩ := parked_tail_created_isolated
        holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel fuel
        inventory caller memos metadata updated before parked uv checked core next tailSeed tailCeiling output
        admission.1 actualNext.symm valid observed tail
      exact False.elim (impossible discharged)
  | @selected fuel inventory caller memos metadata before seed ceiling uv checked prefixPrepared ordinaryInventory
      ordinaryCaller ordinaryMemos action narrowed updated rightCore fragment returnedInventory headCaller
      returnedMemos headCache recorded callbackCore callbackSeed callbackCeiling output
      admission valid observed _prefixPost _invocation receipt _callbackAdmission callback tail ih =>
      intro actualNext canonical finalOutputHeap discharged
      have chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv) :=
        actualNext.symm
      have narrowedCanonical := SourcePruningEnumerationSelectedStep.prefix_canonical
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos canonical valid
      rw [observed] at narrowedCanonical
      have callbackSuccess : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
          (.inl fragment)) headCache.core (false, recorded) callbackCore := by
        rw [Success, callback]
        exact List.mem_singleton_self _
      have callbackCanonical := receipt.canonical_after_callback graph templates workFuel
        (false, recorded) callbackCore narrowedCanonical callbackSuccess
      have tailMeaning := ih rfl callbackCanonical finalOutputHeap discharged
      have callbackArity := tail.arity_before finalOutputHeap
      have ready := SourcePruningEnumerationRecursive.packet_selected_ready
        formulas solver inventory stop order metadata caller memos before uv admission.1 chosen
      obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := admission.1.valid
      have prefixMeaning := SourcePruningEnumerationSelectedStep.prefix_semantics
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos admission.1.context ready realized valid
      rw [observed] at prefixMeaning
      have narrowedValid := valid
      rw [observed] at narrowedValid
      have opaqueMeaning := admission.prepared_opaque_sound_retained _ narrowedValid observed
      obtain ⟨entered, handle, scs, decoded, prepared, heap, preparationBound,
        original, originalReady, originalStored, preparing, point, _lookup, _preparationPost,
        enteredPacket, _stable, enteredReady, _enteredStored, _counter, _values,
        flags, waiting, available, closed, _language, branches⟩ := receipt
      intro ambient assignment satisfied
      have callbackSatisfied := tailMeaning ambient assignment satisfied
      rcases branches with ordinary | otherBranch
      · obtain ⟨parentEntry, edges, depth, free, edge, headSeed, inherited,
          headInventory, localHeadCaller, headMemos, headBound, preparedIs,
          nonterminal, headPost, _captured, completed⟩ := ordinary
        subst prepared
        have localHeap := completed.post.arity_before callbackArity
        have ownArity := completed.freshArity_of_origin_heap localHeap
        have retained := SourcePruningEnumerationPreparedOpaqueEvent.completed_head_output_retained
          headSeed inherited formulas solver headInventory localHeadCaller headMemos updated entered checkEmpty
          uv handle scs parentEntry edges depth free edge headBound fragment headCaller returnedMemos.query headCache
          returnedInventory returnedMemos completed holeKey fits admits graph templates edgesOf stop order
          workFuel fuel recorded callbackCore callbackSeed callbackCeiling output callback tail discharged
        have enteredSame : entered = EnumerationExpandableIndex.frame entered.core narrowed := by
          cases entered with
          | mk core expandable waitingIndex =>
              change expandable = narrowed.expandable at flags
              change waitingIndex = narrowed.waiting at waiting
              subst expandable
              subst waitingIndex
              rfl
        have preparedHead := completed
        rw [enteredSame] at preparedHead
        obtain ⟨_stored, _decoded, _selected, localMeaning⟩ :=
          SourcePruningEnumerationPreparedNativeHookResources.CompletedHeadReceipt.sound_ordinary_callback_input
            original originalReady originalStored preparing headPost preparedHead callbackSuccess
            narrowedCanonical nonterminal ownArity retained
        have narrowedSatisfied := (localMeaning ambient assignment callbackSatisfied).1.1
        exact prefixMeaning ambient _ assignment narrowedSatisfied
      · obtain ⟨gate, running, _post, _captured, completed, _admitted, _pending, _history⟩ := otherBranch
        have retained : (match (generalizing := false) prepared with
            | .node _ _ _ _ => True | _ => False) ∨
            scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨ scs = [] := by
          by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
          · exact .inr (.inl terminal)
          · have nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false := by
              simpa only [Bool.not_eq_true] using terminal
            have impossible := SourcePruningEnumerationSelectedOpaqueDispatch.completed_opaque_output_not_discharged
              formulas solver ordinaryInventory
              (SourcePruningEnumerationSelectedValueCaller.advance ordinaryCaller heap) ordinaryMemos updated
              entered checkEmpty workFuel uv scs prepared enteredPacket enteredReady.inside available closed
              nonterminal fragment headCaller headCache returnedInventory returnedMemos running completed
              holeKey fits admits graph templates edgesOf stop order fuel recorded callbackCore
              callbackSeed callbackCeiling output callback tail
            exact False.elim (impossible discharged)
        have recordedMeaning := SourcePruningRecordTypes.recordTypes_success_semantics
          graph templates workFuel updated uv (.inl fragment) headCache.core callbackCore (false, recorded)
          completed.safe.1.total callbackSuccess
        have headSatisfied := (recordedMeaning
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient headCaller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment).mp callbackSatisfied
        have narrowedSatisfied := (opaqueMeaning ordinaryInventory ordinaryMemos updated original
          handle scs decoded prepared heap entered preparationBound originalReady originalStored preparing point
          enteredPacket gate fragment headCaller headCache returnedMemos running retained ambient
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment headSatisfied).1
        exact prefixMeaning ambient _ assignment narrowedSatisfied

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
