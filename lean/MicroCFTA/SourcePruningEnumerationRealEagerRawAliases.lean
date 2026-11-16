import MicroCFTA.SourcePruningEnumerationSharedEagerReservation
import MicroCFTA.SourcePruningEnumerationRealCapturedRestartAliases
import MicroCFTA.SourcePruningEnumerationSelectedPrefixRawAliases
import MicroCFTA.SourcePruningEnumerationCapturedFinalizeRawAliases
import MicroCFTA.SourcePruningEnumerationSharedChildRawAliasGrowth
import MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted continueWith)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (runEagerWithNarrow runWithNarrow resumeWithNarrow)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs scan_output_origin)
open SourcePruningEnumerationRawAliasPrimitives
open SourcePruningEnumerationCapturedFinalizeRawAliases
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {bits : Nat}
local notation "Hook" => NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
local notation "Fold" => NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
attribute [local instance] SourcePruningEnumerationEntry.entryMonadList
set_option autoImplicit false

/- Note [Whole eager raw alias growth]
Each actual prefix and selected entry retains every input raw alias.
Only the actual producing row supplies the recursive callback input.
The callback origin fixes that input and its output occurrence together.
Depth induction transports aliases from that input to the same emitted output.
Sibling rows keep their captured enumeration cache.
Stopped outcomes retain their actual earlier outputs.
The work fuel stays fixed throughout the induction.
-/

section AliasWorkerProof

private theorem alias_entry_forward
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel uv : Nat)
    (before after : Core) (result : Nat × Nat × List Suspended × Node)
    (actual : Success (SourcePruningEnumerationEntry.enter heap fuel uv) before result after) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right := by
  unfold SourcePruningEnumerationEntry.enter at actual
  obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp actual
  have first : ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass middle.representatives left right := by
    obtain ⟨found, lookup, _stored, rfl⟩ := (getValue_success fuel uv before middle value).mp reading
    exact findRoot_sameClass_forward fuel uv before.representatives found lookup
  cases value with
  | eliminated | enumerated _ => simp [Success, reject, ExceptT.run] at continued
  | unenumerated node scs =>
      cases node with
      | none => simp [Success, reject, ExceptT.run] at continued
      | some handle =>
          obtain ⟨target, compressed, represented, final⟩ := (success_bind _ _ _ _ _).mp continued
          have second := representative_sameClass_forward fuel uv target middle compressed represented
          cases decoded : lookupNode heap handle with
          | none =>
              simp only [decoded] at final
              exact (success_failure .unresolvedReference compressed after result final).elim
          | some decodedValue =>
              simp only [decoded] at final
              obtain ⟨token, written, writing, finished⟩ := (success_bind _ _ _ _ _).mp final
              cases token
              have shape := (EnumerationDriver.modify_success _ compressed written).mp writing
              have forest : written.representatives = compressed.representatives := by
                simpa only using congrArg (fun state : Core => state.representatives) shape
              obtain ⟨_resultSame, afterSame⟩ := (success_pure _ result written after).mp finished
              subst after
              intro left right same
              rw [forest]
              exact second left right (first left right same)

private theorem alias_empty (before : Cached) (caller : Caller (bits + 2)) (queries : Queries) :
    ∀ output ∈ emitted (.complete [] caller queries : Hook),
      ∀ left right, UnionFind.SameClass before.core.representatives left right →
        UnionFind.SameClass output.cache.core.representatives left right := by
  intro output impossible
  cases impossible

private theorem alias_stopped (before : Cached) (reason : Failure (bits + 2) Typing)
    (endpoint : Option (Caller (bits + 2) × Queries)) :
    ∀ output ∈ emitted (.stopped [] reason endpoint : Hook),
      ∀ left right, UnionFind.SameClass before.core.representatives left right →
        UnionFind.SameClass output.cache.core.representatives left right := by
  intro output impossible
  cases impossible

private theorem alias_single (metadata : Option (Metadata Typing)) (before : Cached)
    (caller : Caller (bits + 2)) (queries : Queries) :
    ∀ output ∈ emitted (.complete [⟨metadata, before, caller, queries⟩] caller queries : Hook),
      ∀ left right, UnionFind.SameClass before.core.representatives left right →
        UnionFind.SameClass output.cache.core.representatives left right := by
  intro output member left right same
  have equal := List.mem_singleton.mp member
  subst output
  exact same

private theorem alias_finish (uv : Nat) (before : Cached) (actual : Fold)
    (good : ∀ output ∈ outputs actual, ∀ left right,
      UnionFind.SameClass before.core.representatives left right →
        UnionFind.SameClass output.cache.core.representatives left right) :
    ∀ output ∈ emitted (SourcePruningEnumerationSharedPreparedRecursive.finish uv actual),
      ∀ left right, UnionFind.SameClass before.core.representatives left right →
        UnionFind.SameClass output.cache.core.representatives left right := by
  cases actual <;> exact good

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem alias_opaque_complete
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (caller reached : Caller (bits + 2)) (before finished : Cached) (queries saved : Queries)
    (fragment : Fragment)
    (actual : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target
      scs value caller before queries = some (.complete fragment reached saved finished)) :
    ∀ left right, UnionFind.SameClass before.core.representatives left right →
      UnionFind.SameClass finished.core.representatives left right := by
  cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;> cases value <;>
    simp only [SourcePruningEnumerationSharedSelectedOpaqueDispatch.run, Option.some.injEq, reduceCtorEq,
      terminal, Bool.not_true, Bool.not_false, ↓reduceIte] at actual
  all_goals
    split at actual
    · rename_i childFragment childReturned childCaller childQueries read waiting after called
      split at actual
      · rename_i finalCache finalized
        have receiptSame := Option.some.inj actual
        have cacheSame : finalCache = finished :=
          (SelectedEdge.Result.complete.inj receiptSame).2.2.2
        have childAliases := SourcePruningEnumerationSharedChildRawAliasGrowth.successful_sameClass_forward
          checkEmpty r n p h k scs _ caller childCaller before after queries childQueries
          childFragment childReturned read waiting called
        have finalAliases := finalize_sameClass_forward childCaller.checked.native.machine.heap
          k target childFragment after finalCache finalized
        intro left right same
        rw [← cacheSame]
        exact finalAliases left right (childAliases.2 left right same).2
      · cases actual
    · cases actual

private theorem alias_continue
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat)
    (smallerDepth : ∀ (metadata : Metadata Typing) (caller : Caller (bits + 2))
        (queries : Queries) (before : Cached) (decision : Option Next),
      ∀ output ∈ emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before decision),
        ∀ left right, UnionFind.SameClass before.core.representatives left right →
          UnionFind.SameClass output.cache.core.representatives left right)
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached) :
    ∀ output ∈ emitted (continueWith
      (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth)
      graph templates stop order workFuel metadata uv fragment caller queries before),
      ∀ left right, UnionFind.SameClass before.core.representatives left right →
        UnionFind.SameClass output.cache.core.representatives left right := by
  unfold continueWith
  dsimp only
  generalize recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
    graph templates workFuel metadata uv (.inl fragment) before.core) = raw
  cases raw with
  | nil => intro output impossible; cases impossible
  | cons first rest =>
      cases first with
      | error fault => intro output impossible; cases impossible
      | ok pair =>
          obtain ⟨⟨pruned, updated⟩, callbackCore⟩ := pair
          cases rest with
          | cons second remaining =>
              cases pruned <;> intro output impossible <;> cases impossible
          | nil =>
              cases pruned with
              | true => intro output impossible; cases impossible
              | false =>
                  have callbackAliases := false_recordTypes_sameClass_forward graph templates workFuel uv
                    metadata updated fragment before callbackCore recorded
                  intro output member left right same
                  exact smallerDepth updated caller queries (EnumerationExpandableIndex.frame callbackCore before)
                    (SourcePruningEnumerationRestart.decision stop order updated
                      (EnumerationExpandableIndex.frame callbackCore before)) output member left right
                    (callbackAliases left right same)

private theorem alias_opaque_outputs
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat)
    (smallerDepth : ∀ (metadata : Metadata Typing) (caller : Caller (bits + 2))
        (queries : Queries) (before : Cached) (decision : Option Next),
      ∀ output ∈ emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before decision),
        ∀ left right, UnionFind.SameClass before.core.representatives left right →
          UnionFind.SameClass output.cache.core.representatives left right)
    (metadata : Metadata Typing) (uv target : Nat) (scs : List Suspended) (value : Node)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached) :
    let hook := continueWith
      (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth)
      graph templates stop order workFuel metadata uv
    ∀ output ∈ outputs (SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
        (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty workFuel workFuel workFuel workFuel workFuel
          target scs value caller before queries)),
      ∀ left right, UnionFind.SameClass before.core.representatives left right →
        UnionFind.SameClass output.cache.core.representatives left right := by
  dsimp only
  generalize receiptRun : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run
    checkEmpty workFuel workFuel workFuel workFuel workFuel target scs value caller before queries = receipt
  cases receipt with
  | none => intro output impossible; cases impossible
  | some receipt =>
      cases receipt with
      | unhandled => intro output impossible; cases impossible
      | rejected reached saved after => intro output impossible; cases impossible
      | finalizeStopped fragment reached saved after => intro output impossible; cases impossible
      | stopped completed observation candidate =>
          unfold SourcePruningEnumerationSharedReceiptContinuation.run
          dsimp only
          cases advanced : NativeContinuations.advance (.stopped completed observation candidate) with
          | none => intro output impossible; cases impossible
          | some endpoint =>
              obtain ⟨reached, saved⟩ := endpoint
              intro output impossible
              cases impossible
      | complete fragment reached saved after =>
          have receiptAliases := alias_opaque_complete checkEmpty workFuel workFuel workFuel workFuel workFuel
            target scs value caller reached before after queries saved fragment receiptRun
          have continued := alias_continue holeKey fits admits graph templates checkEmpty edgesOf stop order
            workFuel recursiveDepth smallerDepth metadata uv fragment reached saved after
          unfold SourcePruningEnumerationSharedReceiptContinuation.run
          dsimp only
          generalize called : continueWith
            (resumeWithNarrow
              (SourcePruningEnumerationSharedEagerChildren.eagerChild
                checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
              (SourcePruningOuterNarrow.narrow holeKey fits admits)
              graph templates checkEmpty edgesOf stop order workFuel recursiveDepth)
            graph templates stop order workFuel metadata uv fragment reached saved after = actual at continued ⊢
          cases actual with
          | complete produced finalCaller finalQueries =>
              intro output member left right same
              exact continued output member left right (receiptAliases left right same)
          | stopped produced reason endpoint =>
              intro output member left right same
              exact continued output member left right (receiptAliases left right same)

private theorem alias_prepared_outputs
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat)
    (smallerDepth : ∀ (metadata : Metadata Typing) (caller : Caller (bits + 2))
        (queries : Queries) (before : Cached) (decision : Option Next),
      ∀ output ∈ emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before decision),
        ∀ left right, UnionFind.SameClass before.core.representatives left right →
          UnionFind.SameClass output.cache.core.representatives left right)
    (metadata : Metadata Typing) (uv : Nat)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached) :
    let actual := SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (continueWith
        (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth)
        graph templates stop order workFuel metadata uv)
      checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries
    ∀ folded, actual.2 = some folded → ∀ output ∈ outputs folded,
      ∀ left right, UnionFind.SameClass before.core.representatives left right →
        UnionFind.SameClass output.cache.core.representatives left right := by
  dsimp only
  unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
  dsimp only
  generalize preparation : SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before = observation
  intro folded observed
  obtain ⟨raw, native⟩ := observation
  cases native with
  | none => cases observed
  | some native =>
      cases native with
      | failed fault heap => cases observed
      | done value heap =>
          cases raw with
          | nil => cases observed
          | cons row rest =>
              cases row with
              | error fault => cases observed
              | ok pair =>
                  obtain ⟨⟨target, handle, scs, decoded⟩, entered⟩ := pair
                  cases rest with
                  | cons second remaining => cases observed
                  | nil =>
                      have entryRun := congrArg Prod.fst preparation
                      change ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
                        workFuel uv before.core) = [.ok ((target, handle, scs, decoded), entered)] at entryRun
                      have entrySuccess : Success (SourcePruningEnumerationEntry.enter
                          caller.checked.native.machine.heap workFuel uv) before.core
                          (target, handle, scs, decoded) entered := by
                        rw [Success, entryRun]
                        exact List.mem_singleton_self _
                      have entryAliases := alias_entry_forward caller.checked.native.machine.heap workFuel uv
                        before.core entered (target, handle, scs, decoded) entrySuccess
                      have opaqueGood := alias_opaque_outputs holeKey fits admits graph templates checkEmpty edgesOf
                        stop order workFuel recursiveDepth smallerDepth metadata uv target scs value
                        (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
                        (EnumerationExpandableIndex.frame entered before)
                      dsimp only at observed opaqueGood
                      cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
                      | true =>
                          rw [terminal] at observed
                          simp only [ite_true] at observed
                          cases Option.some.inj observed
                          intro output member left right same
                          exact opaqueGood output member left right (entryAliases left right same)
                      | false =>
                          rw [terminal] at observed
                          simp only [Bool.false_eq_true, ite_false] at observed
                          cases value with
                          | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
                              cases Option.some.inj observed
                              intro output member left right same
                              exact opaqueGood output member left right (entryAliases left right same)
                          | node entry rows depth free =>
                              cases Option.some.inj observed
                              intro output member left right same
                              obtain ⟨index, indexed⟩ := List.mem_iff_getElem?.mp member
                              obtain ⟨attempted, edge, remaining, rowCaller, rowQueries, processed, earlier,
                                  rowResult, localIndex, _rowOrder, _rowPrefix, rowCall, rowHit, _offset⟩ :=
                                scan_output_origin
                                  (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
                                    (SourcePruningEnumerationSharedEagerChildren.eagerChild
                                      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                    (continueWith
                                      (resumeWithNarrow
                                        (SourcePruningEnumerationSharedEagerChildren.eagerChild
                                          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                        (SourcePruningOuterNarrow.narrow holeKey fits admits)
                                        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth)
                                      graph templates stop order workFuel metadata uv)
                                    workFuel target scs)
                                  (EnumerationExpandableIndex.frame entered before) (edgesOf (.node entry rows depth free))
                                  (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries index output indexed
                              rw [← rowCall] at rowHit
                              obtain ⟨fragment, reached, saved, beforeFinalize, finished, updated, callbackCore,
                                  _earlier, _later, callbackIndex, _finalized, _recorded, _whole, callbackHit,
                                  _callbackOffset, _invoked, restartAliases⟩ :=
                                SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.real_eager_captured_output_restart_entry_alias_origin
                                  holeKey fits admits graph templates checkEmpty edgesOf stop order
                                  workFuel recursiveDepth uv target metadata scs edge rowCaller rowQueries
                                  (EnumerationExpandableIndex.frame entered before) localIndex output rowHit
                              have recursiveMember := List.mem_of_getElem? callbackHit
                              exact smallerDepth updated reached saved (EnumerationExpandableIndex.frame callbackCore finished)
                                (SourcePruningEnumerationRestart.decision stop order updated
                                  (EnumerationExpandableIndex.frame callbackCore finished)) output recursiveMember left right
                                (restartAliases left right (entryAliases left right same))

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem alias_parked_core
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata updated : Metadata Typing) (workFuel uv : Nat) (caller : Caller (bits + 2))
    (queries : Queries) (before parked : Cached) (checked core : Core) (next : Option Next)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
      .parked checked (some parked) (some [.ok ((updated, next), core)])) :
    core = checked := by
  have restarted : ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked) =
      [.ok ((updated, next), core)] := by
    have observed := actual
    unfold SourcePruningEnumerationSelectedStep.runPrefix
      SourcePruningEnumerationSelectedStep.runPrefixWithNarrow at observed
    dsimp only at observed
    split at observed
    · rename_i handle bucket readAfter reading
      split at observed
      · rename_i actualChecked checking
        obtain ⟨checkedSame, adapted, rawSame⟩ :=
          SourcePruningEnumerationSelectedStep.Result.parked.inj observed
        subst actualChecked
        rw [adapted, Option.map_some] at rawSame
        exact Option.some.inj rawSame
      all_goals repeat first | (solve | cases observed) | split at observed
    all_goals repeat first | (solve | cases observed) | split at observed
  change ((if SourcePruningEnumerationRestart.decision stop order metadata parked = some .stuck then []
    else [Except.ok ((metadata, SourcePruningEnumerationRestart.decision stop order metadata parked), checked)]) :
      List (Except EnumerationState.Error ((Metadata Typing × Option Next) × Core))) =
        [Except.ok ((updated, next), core)] at restarted
  split at restarted
  · cases restarted
  · have rowSame := Except.ok.inj (List.cons.inj restarted).1
    exact (congrArg Prod.snd rowSame).symm

private theorem alias_whole_resume
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat) :
    ∀ (metadata : Metadata Typing) (caller : Caller (bits + 2)) (queries : Queries)
        (before : Cached) (decision : Option Next),
      ∀ output ∈ emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before decision),
        ∀ left right, UnionFind.SameClass before.core.representatives left right →
          UnionFind.SameClass output.cache.core.representatives left right := by
  induction recursiveDepth with
  | zero =>
      intro metadata caller queries before decision
      cases decision with
      | none => exact alias_single (some metadata) before caller queries
      | some decision =>
          cases decision with
          | done => exact alias_single none before caller queries
          | stuck => exact alias_empty before caller queries
          | expand uv => exact alias_stopped before _ _
  | succ fuel ih =>
      intro metadata caller queries before decision
      cases decision with
      | none => exact alias_single (some metadata) before caller queries
      | some decision =>
          cases decision with
          | done => exact alias_single none before caller queries
          | stuck => exact alias_empty before caller queries
          | expand uv =>
              rw [resumeWithNarrow]
              dsimp only
              have prefixAliases := SourcePruningEnumerationSelectedPrefixRawAliases.runPrefix_sameClass_forward
                holeKey fits admits graph templates stop order metadata
                workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries
              dsimp only [SourcePruningEnumerationSelectedStep.runPrefix] at prefixAliases
              generalize prefixObserved : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
                (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
                workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries = actual at prefixAliases ⊢
              cases actual with
              | stopped read checked => exact alias_stopped before _ _
              | parked checked candidate raw =>
                  cases candidate with
                  | none => exact alias_stopped before _ _
                  | some parked =>
                      cases raw with
                      | none => exact alias_stopped before _ _
                      | some rows =>
                          cases rows with
                          | nil => exact alias_empty before caller queries
                          | cons row rest =>
                              cases row with
                              | error fault => exact alias_stopped before _ _
                              | ok pair =>
                                  obtain ⟨⟨updated, next⟩, core⟩ := pair
                                  cases rest with
                                  | cons second remaining => exact alias_stopped before _ _
                                  | nil =>
                                      have coreSame := alias_parked_core holeKey fits admits graph templates stop order
                                        metadata updated workFuel uv caller queries before parked checked core next prefixObserved
                                      intro output member left right same
                                      have entryAlias : UnionFind.SameClass
                                          (EnumerationExpandableIndex.frame core parked).core.representatives left right := by
                                        change UnionFind.SameClass core.representatives left right
                                        rw [coreSame]
                                        exact prefixAliases.1 left right same
                                      exact ih updated caller queries (EnumerationExpandableIndex.frame core parked) next
                                        output member left right entryAlias
              | narrowed checked prepared reached saved action candidate right ordinary =>
                  rcases action with _ | (_ | ⟨actionHead, actionTail⟩)
                  all_goals first | exact alias_empty before reached saved | skip
                  all_goals
                    cases right with
                    | none => exact alias_stopped before _ _
                    | some rows =>
                        cases rows with
                        | nil => exact alias_stopped before _ _
                        | cons row rest =>
                            cases row with
                            | error fault => exact alias_stopped before _ _
                            | ok pair =>
                                obtain ⟨⟨pruned, updated⟩, core⟩ := pair
                                cases pruned with
                                | true =>
                                    cases rest with
                                    | nil => exact alias_empty before reached saved
                                    | cons second remaining => exact alias_stopped before _ _
                                | false =>
                                    cases rest with
                                    | cons second remaining => exact alias_stopped before _ _
                                    | nil =>
                                        cases candidate with
                                        | none => exact alias_stopped before _ _
                                        | some after =>
                                            cases ordinary with
                                            | some other => exact alias_stopped before _ _
                                            | none =>
                                                have candidateAliases := prefixAliases.2 after rfl
                                                have good := alias_prepared_outputs holeKey fits admits graph templates
                                                  checkEmpty edgesOf stop order workFuel fuel ih updated uv reached saved after
                                                dsimp only at good ⊢
                                                generalize dispatched : SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
                                                  (SourcePruningEnumerationSharedEagerChildren.eagerChild
                                                    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                                  (continueWith
                                                    (resumeWithNarrow
                                                      (SourcePruningEnumerationSharedEagerChildren.eagerChild
                                                        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                                      (SourcePruningOuterNarrow.narrow holeKey fits admits)
                                                      graph templates checkEmpty edgesOf stop order workFuel fuel)
                                                    graph templates stop order workFuel updated uv)
                                                  checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv
                                                  edgesOf reached after saved = executed at good ⊢
                                                obtain ⟨preparation, folded⟩ := executed
                                                dsimp only at good ⊢
                                                cases folded with
                                                | none => exact alias_stopped before _ _
                                                | some folded =>
                                                    have continued := alias_finish uv after folded (good folded rfl)
                                                    intro output member left right same
                                                    exact continued output member left right (candidateAliases left right same)

end AliasWorkerProof

variable [DecidableEq (EdgeKey Symbol Constraint)]

theorem runEager_real_entry_aliases_at_any_budget
    [DecidableEq Symbol] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveFuel seed ceiling) (workFuel : Nat) :
    let outcome := runEagerWithNarrow (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel recursiveFuel metadata caller memos.query before
    ∀ output ∈ emitted outcome,
      ∀ (left right : Nat), UnionFind.SameClass before.core.representatives left right →
        UnionFind.SameClass output.cache.core.representatives left right := by
  have _ := packet
  have _ := bounded
  have _ := known
  have _ := selectionMembers
  have _ := selectionLength
  have _ := initialMass
  have _ := reserved
  clear packet bounded known selectionMembers selectionLength initialMass reserved
  dsimp only
  unfold runEagerWithNarrow runWithNarrow
  exact alias_whole_resume holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel recursiveFuel metadata caller memos.query before
    (SourcePruningEnumerationRestart.decision stop order metadata before)

end MicroCFTA.SourcePruningEnumerationSharedEagerReservation

namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (resumeWithNarrow)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
set_option autoImplicit false

/-- Preserve entry aliases through the actual restart at its supplied decision. -/
theorem resumeWithNarrow_real_entry_aliases_at_any_budget
    [DecidableEq Symbol] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat) :
    ∀ (metadata : Metadata Typing) (caller : Caller (bits + 2)) (queries : Queries)
        (before : Cached) (decision : Option Next),
      ∀ output ∈ emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before decision),
        ∀ left right, UnionFind.SameClass before.core.representatives left right →
          UnionFind.SameClass output.cache.core.representatives left right := by
  exact alias_whole_resume (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel recursiveDepth

end MicroCFTA.SourcePruningEnumerationSharedEagerReservation
