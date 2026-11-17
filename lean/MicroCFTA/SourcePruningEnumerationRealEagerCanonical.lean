import MicroCFTA.SourcePruningEnumerationObservedEntryCanonical
import MicroCFTA.SourcePruningEnumerationSharedChildCanonical
import MicroCFTA.SourcePruningEnumerationInvocationCanonical
import MicroCFTA.SourcePruningEnumerationOwnFinalizeCanonical
import MicroCFTA.SourcePruningEnumerationPathRecordingValues
import MicroCFTA.SourcePruningEnumerationRealEagerCapturedCausalCallbackOrigin
import MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins

namespace MicroCFTA.SourcePruningEnumerationRealEagerCanonical
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationSemantics EnumerationValidity
open InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted continueWith)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (runEagerWithNarrow runWithNarrow resumeWithNarrow)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs scan_output_origin)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {bits : Nat}
local notation "Hook" => NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
local notation "Fold" => NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
attribute [local instance] SourcePruningEnumerationEntry.entryMonadList
set_option autoImplicit false
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/- Note [Canonicality through the actual real eager worker]
The proof follows the checked whole raw-alias proof structure locally.
It adds no runtime function and changes no supplied fuel.
Initial canonicality passes through the actual selected prefix and entry.
The producing captured row fixes the same selected trace and callback input.
Canonicality follows that trace, its finalizer and its false callback.
The genuine smaller-depth hypothesis applies to that exact restart suffix.
Sibling rows retain the same captured enumeration cache.
Stopped outcomes retain their actual earlier emissions.
These facts concern stored trie representation, not a joint semantic model.
-/

section CanonicalWorkerProof

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem canonical_empty (caller : Caller (bits + 2)) (queries : Queries) :
    ∀ output ∈ emitted (.complete [] caller queries : Hook), Canonical output.cache.core := by
  intro output impossible
  cases impossible

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem canonical_stopped (reason : Failure (bits + 2) Typing)
    (endpoint : Option (Caller (bits + 2) × Queries)) :
    ∀ output ∈ emitted (.stopped [] reason endpoint : Hook), Canonical output.cache.core := by
  intro output impossible
  cases impossible

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem canonical_single (metadata : Option (Metadata Typing)) (before : Cached)
    (caller : Caller (bits + 2)) (queries : Queries) (canonical : Canonical before.core) :
    ∀ output ∈ emitted (.complete [⟨metadata, before, caller, queries⟩] caller queries : Hook),
      Canonical output.cache.core := by
  intro output member
  have equal := List.mem_singleton.mp member
  subst output
  exact canonical

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem canonical_finish (uv : Nat) (actual : Fold)
    (good : ∀ output ∈ outputs actual, Canonical output.cache.core) :
    ∀ output ∈ emitted (SourcePruningEnumerationSharedPreparedRecursive.finish uv actual),
      Canonical output.cache.core := by
  cases actual <;> exact good

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem canonical_false_recordTypes
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel uv : Nat) (metadata updated : Metadata Typing) (fragment : Fragment)
    (before : Cached) (after : Core) (canonical : Canonical before.core)
    (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv
      (.inl fragment) before.core) = [.ok ((false, updated), after)]) :
    Canonical (EnumerationExpandableIndex.frame after before).core := by
  have successful : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv
      (.inl fragment)) before.core (false, updated) after := by
    rw [Success, recorded]
    exact List.mem_singleton_self _
  have values := SourcePruningEnumerationPathRecordingValues.recordTypes_values
    graph templates fuel metadata uv (.inl fragment) before.core after (false, updated) successful
  intro value member
  change value ∈ after.values at member
  rw [values] at member
  exact canonical value member

private theorem canonical_opaque_complete
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (caller reached : Caller (bits + 2)) (before finished : Cached) (queries saved : Queries)
    (fragment : Fragment)
    (canonical : Canonical before.core) (valid : ValidSuspended scs)
    (actual : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target
      scs value caller before queries = some (.complete fragment reached saved finished)) : Canonical finished.core := by
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
        have childCanonical := SourcePruningEnumerationSharedChildCanonical.successful_canonical
          checkEmpty r n p h k scs _ caller childCaller before after queries childQueries
          childFragment childReturned read waiting canonical valid called
        rw [← cacheSame]
        exact SourcePruningEnumerationFinalize.run_canonical childCaller.checked.native.machine.heap
          k target childFragment after finalCache childCanonical finalized
      · cases actual
    · cases actual

private theorem canonical_continue
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat)
    (smallerDepth : ∀ (metadata : Metadata Typing) (caller : Caller (bits + 2))
        (queries : Queries) (before : Cached) (decision : Option Next),
      Canonical before.core →
      ∀ output ∈ emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before decision),
        Canonical output.cache.core)
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached)
    (canonical : Canonical before.core) :
    ∀ output ∈ emitted (continueWith
      (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth)
      graph templates stop order workFuel metadata uv fragment caller queries before),
      Canonical output.cache.core := by
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
                  have callbackCanonical := canonical_false_recordTypes graph templates workFuel uv
                    metadata updated fragment before callbackCore canonical recorded
                  exact smallerDepth updated caller queries (EnumerationExpandableIndex.frame callbackCore before)
                    (SourcePruningEnumerationRestart.decision stop order updated
                      (EnumerationExpandableIndex.frame callbackCore before)) callbackCanonical

private theorem canonical_opaque_outputs
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat)
    (smallerDepth : ∀ (metadata : Metadata Typing) (caller : Caller (bits + 2))
        (queries : Queries) (before : Cached) (decision : Option Next),
      Canonical before.core →
      ∀ output ∈ emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before decision),
        Canonical output.cache.core)
    (metadata : Metadata Typing) (uv target : Nat) (scs : List Suspended) (value : Node)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached)
    (canonical : Canonical before.core) (valid : ValidSuspended scs) :
    let hook := continueWith
      (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth)
      graph templates stop order workFuel metadata uv
    ∀ output ∈ outputs (SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
        (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty workFuel workFuel workFuel workFuel workFuel
          target scs value caller before queries)), Canonical output.cache.core
 := by
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
          have receiptCanonical := canonical_opaque_complete checkEmpty workFuel workFuel workFuel workFuel workFuel
            target scs value caller reached before after queries saved fragment canonical valid receiptRun
          have continued := canonical_continue holeKey fits admits graph templates checkEmpty edgesOf stop order
            workFuel recursiveDepth smallerDepth metadata uv fragment reached saved after receiptCanonical
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
              exact continued
          | stopped produced reason endpoint =>
              exact continued

private theorem canonical_prepared_outputs
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat)
    (smallerDepth : ∀ (metadata : Metadata Typing) (caller : Caller (bits + 2))
        (queries : Queries) (before : Cached) (decision : Option Next),
      Canonical before.core →
      ∀ output ∈ emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before decision),
        Canonical output.cache.core)
    (metadata : Metadata Typing) (uv : Nat)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached)
    (canonical : Canonical before.core) :
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
    ∀ folded, actual.2 = some folded → ∀ output ∈ outputs folded, Canonical output.cache.core
 := by
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
                      have entryFacts :=
                        SourcePruningEnumerationObservedEntryCanonical.successful_preparation_bucket_valid
                          workFuel workFuel uv target handle scs caller before entered decoded value heap
                          canonical preparation
                      have opaqueGood := canonical_opaque_outputs holeKey fits admits graph templates checkEmpty edgesOf
                        stop order workFuel recursiveDepth smallerDepth metadata uv target scs value
                        (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
                        (EnumerationExpandableIndex.frame entered before) entryFacts.1 entryFacts.2
                      dsimp only at observed opaqueGood
                      cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
                      | true =>
                          rw [terminal] at observed
                          simp only [ite_true] at observed
                          cases Option.some.inj observed
                          exact opaqueGood
                      | false =>
                          rw [terminal] at observed
                          simp only [Bool.false_eq_true, ite_false] at observed
                          cases value with
                          | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
                              cases Option.some.inj observed
                              exact opaqueGood
                          | node entry rows depth free =>
                              cases Option.some.inj observed
                              intro output member
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
                                  _earlier, _later, callbackIndex, finalized, recorded, _whole, callbackHit,
                                  _callbackOffset, invoked⟩ :=
                                SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.real_eager_captured_output_causal_callback_restart_origin
                                  holeKey fits admits graph templates checkEmpty edgesOf stop order
                                  workFuel recursiveDepth uv target metadata scs edge rowCaller rowQueries
                                  (EnumerationExpandableIndex.frame entered before) localIndex output rowHit
                              have actualInvocation := invoked
                              dsimp only [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.CapturedCallbackInvocationAt]
                                at actualInvocation
                              obtain ⟨selected, _rowWhole, _rowHit, _rowOffset, _sameFinalized, _sameRecorded⟩ :=
                                actualInvocation
                              have selectedCanonical :=
                                SourcePruningEnumerationInvocationCanonical.selected_complete_canonical
                                  checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf .eager _
                                  scs edge rowCaller reached (EnumerationExpandableIndex.frame entered before)
                                  beforeFinalize rowQueries saved localIndex output fragment callbackIndex
                                  entryFacts.1 entryFacts.2 selected
                              have finishedCanonical := SourcePruningEnumerationFinalize.run_canonical
                                reached.checked.native.machine.heap workFuel target fragment
                                beforeFinalize finished selectedCanonical finalized
                              have callbackCanonical := canonical_false_recordTypes graph templates workFuel uv
                                metadata updated fragment finished callbackCore finishedCanonical recorded
                              have recursiveMember := List.mem_of_getElem? callbackHit
                              exact smallerDepth updated reached saved (EnumerationExpandableIndex.frame callbackCore finished)
                                (SourcePruningEnumerationRestart.decision stop order updated
                                  (EnumerationExpandableIndex.frame callbackCore finished)) callbackCanonical
                                output recursiveMember

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem canonical_parked_core
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

private theorem canonical_whole_resume
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat) :
    ∀ (metadata : Metadata Typing) (caller : Caller (bits + 2)) (queries : Queries)
        (before : Cached) (decision : Option Next),
      Canonical before.core →
      ∀ output ∈ emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before decision),
        Canonical output.cache.core
 := by
  induction recursiveDepth with
  | zero =>
      intro metadata caller queries before decision canonical
      cases decision with
      | none => exact canonical_single (some metadata) before caller queries canonical
      | some decision =>
          cases decision with
          | done => exact canonical_single none before caller queries canonical
          | stuck => exact canonical_empty caller queries
          | expand uv => exact canonical_stopped _ _
  | succ fuel ih =>
      intro metadata caller queries before decision canonical
      cases decision with
      | none => exact canonical_single (some metadata) before caller queries canonical
      | some decision =>
          cases decision with
          | done => exact canonical_single none before caller queries canonical
          | stuck => exact canonical_empty caller queries
          | expand uv =>
              rw [resumeWithNarrow]
              dsimp only
              have prefixCanonical := SourcePruningEnumerationObservedEntryCanonical.runPrefix_canonical
                holeKey fits admits graph templates stop order metadata
                workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries canonical
              dsimp only [SourcePruningEnumerationSelectedStep.runPrefix] at prefixCanonical
              generalize prefixObserved : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
                (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
                workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries = actual at prefixCanonical ⊢
              cases actual with
              | stopped read checked => exact canonical_stopped _ _
              | parked checked candidate raw =>
                  cases candidate with
                  | none => exact canonical_stopped _ _
                  | some parked =>
                      cases raw with
                      | none => exact canonical_stopped _ _
                      | some rows =>
                          cases rows with
                          | nil => exact canonical_empty caller queries
                          | cons row rest =>
                              cases row with
                              | error fault => exact canonical_stopped _ _
                              | ok pair =>
                                  obtain ⟨⟨updated, next⟩, core⟩ := pair
                                  cases rest with
                                  | cons second remaining => exact canonical_stopped _ _
                                  | nil =>
                                      have coreSame := canonical_parked_core holeKey fits admits graph templates stop order
                                        metadata updated workFuel uv caller queries before parked checked core next prefixObserved
                                      have entryCanonical : Canonical
                                          (EnumerationExpandableIndex.frame core parked).core := by
                                        change Canonical core
                                        rw [coreSame]
                                        exact prefixCanonical.1
                                      exact ih updated caller queries (EnumerationExpandableIndex.frame core parked) next
                                        entryCanonical
              | narrowed checked prepared reached saved action candidate right ordinary =>
                  rcases action with _ | (_ | ⟨actionHead, actionTail⟩)
                  all_goals first | exact canonical_empty reached saved | skip
                  all_goals
                    cases right with
                    | none => exact canonical_stopped _ _
                    | some rows =>
                        cases rows with
                        | nil => exact canonical_stopped _ _
                        | cons row rest =>
                            cases row with
                            | error fault => exact canonical_stopped _ _
                            | ok pair =>
                                obtain ⟨⟨pruned, updated⟩, core⟩ := pair
                                cases pruned with
                                | true =>
                                    cases rest with
                                    | nil => exact canonical_empty reached saved
                                    | cons second remaining => exact canonical_stopped _ _
                                | false =>
                                    cases rest with
                                    | cons second remaining => exact canonical_stopped _ _
                                    | nil =>
                                        cases candidate with
                                        | none => exact canonical_stopped _ _
                                        | some after =>
                                            cases ordinary with
                                            | some other => exact canonical_stopped _ _
                                            | none =>
                                                have candidateCanonical := prefixCanonical.2 after rfl
                                                have good := canonical_prepared_outputs holeKey fits admits graph templates
                                                  checkEmpty edgesOf stop order workFuel fuel ih updated uv reached saved after candidateCanonical
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
                                                | none => exact canonical_stopped _ _
                                                | some folded =>
                                                    exact canonical_finish uv folded (good folded rfl)


end CanonicalWorkerProof

theorem resumeWithNarrow_real_canonical_at_any_budget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat) :
    ∀ (metadata : Metadata Typing) (caller : Caller (bits + 2)) (queries : Queries)
        (before : Cached) (decision : Option Next),
      Canonical before.core →
      ∀ output ∈ emitted (resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before decision),
        Canonical output.cache.core
 := by
  exact canonical_whole_resume holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel recursiveDepth

theorem runEager_real_canonical_at_any_budget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat)
    (metadata : Metadata Typing) (caller : Caller (bits + 2)) (queries : Queries) (before : Cached)
    (canonical : Canonical before.core) :
    let outcome := runEagerWithNarrow (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before
    ∀ output ∈ emitted outcome, Canonical output.cache.core
 := by
  dsimp only
  unfold runEagerWithNarrow runWithNarrow
  exact canonical_whole_resume holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel recursiveDepth metadata caller queries before
    (SourcePruningEnumerationRestart.decision stop order metadata before) canonical

end MicroCFTA.SourcePruningEnumerationRealEagerCanonical
