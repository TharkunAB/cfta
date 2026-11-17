import MicroCFTA.SourcePruningEnumerationSharedEagerReservation
import MicroCFTA.SourcePruningEnumerationJointCausalEventLedger
import MicroCFTA.SourcePruningEnumerationInvocationEventAuthenticity

namespace MicroCFTA.SourcePruningEnumerationHeldJointCausalEventLedger
open SourcePruningEnumerationRealEagerCausalOutputHistory
open SourcePruningEnumerationParkedOuterHeldHistory
open SourcePruningEnumerationJointCausalEventLedger
open SourcePruningEnumerationCausalHistoryInputInvariants
open EnumerationValidity EnumerationCorrectness EnumerationSchedule EnumerationSemantics
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted continueWith)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (resumeWithNarrow CapturedCallbackInvocationAt)
open SourcePruningEnumerationSharedChildVisitors (visitCapturedWith)
open SourcePruningEnumerationSharedBranching (scan)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {bits : Nat}
local notation "Fold" => NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
local notation "Prepared" => MergedSourceComparison.Result Symbol Constraint (Node × Option (EnumerateM Symbol Constraint Unit))
local notation "ActionRaw" => List (Except EnumerationState.Error (Unit × Core))
set_option autoImplicit false

/- Note [One held derivation supplies one event list]
The mutual induction eliminates one Held qualification derivation.
Each case retains that constructor's actual cache, row, receipt and index.
It derives Canonical and Total from those same literal operation receipts.
The event list and its outer-entry protection are constructed together.
No second Qualified history is eliminated to obtain hidden witnesses.

The local Canonical operation proofs are reused from
SourcePruningEnumerationCausalHistoryInputInvariants.
The captured event helper is reused from
SourcePruningEnumerationJointCausalEventLedger.
Those helpers are private in their owners. Their proof text is local here.
The runtime visitors and resource engine are not copied or changed.
The worker-facing theorem must derive the Held input internally.
-/

/-- Retain held protection at every visible outer operation entry. -/
def OuterEntriesHeld {Typing : Type} {width : Nat}
    (held heldHandle : Nat) (anchor : Core) (events : List (Operation Typing width)) : Prop :=
  ∀ event ∈ events,
    match event with
    | .parked _ _ _ entry _ _ _ _ _ _ =>
        EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor entry.core
    | .selected _ _ _ entry _ _ _ _ _ _ _ _ _ =>
        EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor entry.core
    | .prepare _ _ entry _ _ _ _ _ _ _ =>
        EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor entry.core
    | .opaque .. | .finalize .. | .recordTypes .. | .nested .. => True

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

open SourcePruningEnumerationCapturedFinalizeRawAliases

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


omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem forward_total (before after : Core)
    (total : UnionFind.Total before.representatives)
    (aliases : ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right) :
    UnionFind.Total after.representatives := by
  exact SourcePruningEnumerationStagedChildRoots.total_of_sameClass_forward
    before.representatives after.representatives total aliases

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem finalized_invariants
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel target : Nat) (fragment : Fragment) (before after : Cached)
    (input : CanonicalTotal before.core)
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    CanonicalTotal after.core := by
  exact ⟨SourcePruningEnumerationFinalize.run_canonical heap fuel target fragment before after input.1 observed,
    forward_total before.core after.core input.2
      (finalize_sameClass_forward heap fuel target fragment before after observed)⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem callback_invariants
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel uv : Nat) (metadata updated : Metadata Typing) (fragment : Fragment)
    (before : Cached) (after : Core) (input : CanonicalTotal before.core)
    (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv
      (.inl fragment) before.core) = [.ok ((false, updated), after)]) :
    CanonicalTotal (EnumerationExpandableIndex.frame after before).core := by
  exact ⟨canonical_false_recordTypes graph templates fuel uv metadata updated fragment before after input.1 recorded,
    forward_total before.core (EnumerationExpandableIndex.frame after before).core input.2
      (false_recordTypes_sameClass_forward graph templates fuel uv metadata updated fragment before after recorded)⟩


/- See Note [One joint causal ledger] in SourcePruningEnumerationJointCausalEventLedger.
This helper uses one actual callback invocation for all nested event witnesses.
The public producer and authenticity proofs consume the same selected trace.
-/

private theorem captured_invocation_event_ledger
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth uv target : Nat) (metadata : Metadata Typing)
    (scs : List Suspended) (edge : Edge) (caller : Caller (bits + 2))
    (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing)
    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (saved : Queries)
    (beforeFinalize finished : Cached) (updated : Metadata Typing) (callbackCore : Core)
    (earlier later : List (Output (bits + 2) Typing)) (localIndex : Nat)

    (invoked : CapturedCallbackInvocationAt holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveDepth uv target metadata scs edge caller queries before index output fragment reached saved
      beforeFinalize finished updated callbackCore earlier later localIndex) :
    ∃ events, CapturedEventLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveDepth uv target metadata scs edge caller queries before index output fragment reached saved
      beforeFinalize finished updated callbackCore localIndex events
 := by
  have receipt := invoked
  dsimp only [CapturedCallbackInvocationAt] at receipt
  obtain ⟨trace, _whole, _hit, _offset, finalized, recorded⟩ := receipt
  obtain ⟨events, ledger⟩ :=
    (SourcePruningEnumerationInvocationEventLedger.invocation_event_ledgers
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf).2.2
      .eager _ scs edge caller before queries index output
      (.complete fragment reached saved beforeFinalize) localIndex trace []
  have authentic :=
    (SourcePruningEnumerationInvocationEventLedger.invocation_ledger_events_authentic
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf).2.2
      .eager _ scs edge caller before queries index output
      (.complete fragment reached saved beforeFinalize) localIndex [] events ledger
  exact ⟨events, ledger, authentic, finalized, recorded⟩

private theorem held_history_ledgers
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel held heldHandle : Nat) (anchor : Core) :
    (∀ (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) (decision : Option Next)
      (index : Nat) (output : Output (bits + 2) Typing)
      (history : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata caller queries before decision index output),
      HeldOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel held heldHandle anchor history →
      CanonicalTotal before.core →
      ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata caller queries before decision index output events ∧ OuterEntriesHeld held heldHandle anchor events) ∧
    (∀ (depth : Nat) (metadata : Metadata Typing) (uv : Nat) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing)
      (history : PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata uv caller queries before index output),
      HeldPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel held heldHandle anchor history →
      CanonicalTotal before.core →
      ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata uv caller queries before index output events ∧ OuterEntriesHeld held heldHandle anchor events) := by
  have stoppedCase (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached)
      (_past : EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor before.core) :
      CanonicalTotal before.core →
        ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata caller queries before none 0 ⟨some metadata, before, caller, queries⟩ events ∧
        OuterEntriesHeld held heldHandle anchor events := by
    intro input
    refine ⟨[], JointOutputLedgerAt.stopped depth metadata caller queries before input, ?_⟩
    intro event member
    cases member

  have doneCase (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached)
      (_past : EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor before.core) :
      CanonicalTotal before.core →
        ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata caller queries before (some .done) 0 ⟨none, before, caller, queries⟩ events ∧
        OuterEntriesHeld held heldHandle anchor events := by
    intro input
    refine ⟨[], JointOutputLedgerAt.done depth metadata caller queries before input, ?_⟩
    intro event member
    cases member

  have parkedCase
      {depth uv index : Nat} {metadata updated : Metadata Typing}
      {caller : Caller (bits + 2)} {queries : Queries} {before parkedCache : Cached}
      {checked core : Core} {next : Option Next} {output : Output (bits + 2) Typing}
      (observed : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .parked checked (some parkedCache) (some [.ok ((updated, next), core)]))
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth updated caller queries
        (EnumerationExpandableIndex.frame core parkedCache) next index output)
      (past : EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor before.core)
      (_tailPast : HeldOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order
        workFuel held heldHandle anchor tail)
      (tailIH : CanonicalTotal (EnumerationExpandableIndex.frame core parkedCache).core →
        ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          depth updated caller queries (EnumerationExpandableIndex.frame core parkedCache) next index output events ∧
          OuterEntriesHeld held heldHandle anchor events) :
      CanonicalTotal before.core →
        ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (depth + 1) metadata caller queries before (some (.expand uv)) index output events ∧
        OuterEntriesHeld held heldHandle anchor events := by
    intro input
    have prefixFacts := SourcePruningEnumerationPreparationEntryInvariants.runPrefix_entry_invariants
      holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries input.1 input.2
    have prefixObserved : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
        stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
          .parked checked (some parkedCache) (some [.ok ((updated, next), core)]) := observed
    rw [prefixObserved] at prefixFacts
    have checkedFacts : CanonicalTotal checked := ⟨prefixFacts.2.1, prefixFacts.1⟩
    have candidateFacts : CanonicalTotal parkedCache.core :=
      ⟨(prefixFacts.2.2 parkedCache rfl).2, (prefixFacts.2.2 parkedCache rfl).1⟩
    have same := canonical_parked_core holeKey fits admits graph templates stop order metadata updated
      workFuel uv caller queries before parkedCache checked core next prefixObserved
    have callbackFacts : CanonicalTotal (EnumerationExpandableIndex.frame core parkedCache).core := by
      change CanonicalTotal core
      rw [same]
      exact checkedFacts
    obtain ⟨events, ledger, retained⟩ := tailIH callbackFacts
    refine ⟨_, JointOutputLedgerAt.parked observed input checkedFacts candidateFacts callbackFacts ledger, ?_⟩
    intro event member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact past
    · exact retained event member

  have selectedCase
      {depth uv index : Nat} {metadata updated : Metadata Typing}
      {caller reached : Caller (bits + 2)} {queries saved : Queries} {before after : Cached}
      {checked rightCore : Core} {prepared : Prepared} {action : Option ActionRaw}
      {output : Output (bits + 2) Typing}
      (observed : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .narrowed checked prepared reached saved action (some after)
          (some [.ok ((false, updated), rightCore)]) none)
      (actionContinues : action ≠ some [])
      (preparedHistory : PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth updated uv reached saved after index output)
      (past : EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor before.core)
      (_preparedPast : HeldPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order
        workFuel held heldHandle anchor preparedHistory)
      (preparedIH : CanonicalTotal after.core →
        ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          depth updated uv reached saved after index output events ∧ OuterEntriesHeld held heldHandle anchor events) :
      CanonicalTotal before.core →
        ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (depth + 1) metadata caller queries before (some (.expand uv)) index output events ∧
        OuterEntriesHeld held heldHandle anchor events := by
    intro input
    have prefixFacts := SourcePruningEnumerationPreparationEntryInvariants.runPrefix_entry_invariants
      holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries input.1 input.2
    have prefixObserved : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
        stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
          .narrowed checked prepared reached saved action (some after)
            (some [.ok ((false, updated), rightCore)]) none := observed
    rw [prefixObserved] at prefixFacts
    have checkedFacts : CanonicalTotal checked := ⟨prefixFacts.2.1, prefixFacts.1⟩
    have candidateFacts : CanonicalTotal after.core :=
      ⟨(prefixFacts.2.2 after rfl).2, (prefixFacts.2.2 after rfl).1⟩
    obtain ⟨events, ledger, retained⟩ := preparedIH candidateFacts
    refine ⟨_, JointOutputLedgerAt.selected observed actionContinues input checkedFacts candidateFacts ledger, ?_⟩
    intro event member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact past
    · exact retained event member

  have opaqueCase
      {depth uv target handle index : Nat} {metadata callbackMetadata : Metadata Typing}
      {caller completedCaller : Caller (bits + 2)} {queries saved : Queries}
      {before finished : Cached} {scs : List Suspended} {decoded value : Node}
      {heap : InternedConstructorTemplates.State Symbol Constraint} {entered callbackCore : Core}
      {fragment : Fragment} {output : Output (bits + 2) Typing}
      (preparation : SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
        ([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)))
      (mode : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨
        (match value with | .node .. => False | _ => True))
      (completed : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        workFuel workFuel workFuel workFuel workFuel target scs value
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
        (EnumerationExpandableIndex.frame entered before) queries =
        some (.complete fragment completedCaller saved finished))
      (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
        (.inl fragment) finished.core) = [.ok ((false, callbackMetadata), callbackCore)])
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) index output)
      (past : EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor before.core)
      (_tailPast : HeldOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order
        workFuel held heldHandle anchor tail)
      (tailIH : CanonicalTotal (EnumerationExpandableIndex.frame callbackCore finished).core →
        ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          depth callbackMetadata completedCaller saved (EnumerationExpandableIndex.frame callbackCore finished)
          (SourcePruningEnumerationRestart.decision stop order callbackMetadata
            (EnumerationExpandableIndex.frame callbackCore finished)) index output events ∧
          OuterEntriesHeld held heldHandle anchor events) :
      CanonicalTotal before.core →
        ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          depth metadata uv caller queries before index output events ∧ OuterEntriesHeld held heldHandle anchor events := by
    intro input
    have preparationFacts := SourcePruningEnumerationPreparationEntryInvariants.successful_preparation_entry_invariants
      workFuel workFuel uv target handle scs caller before entered decoded value heap input.1 input.2 preparation
    have entryFacts : CanonicalTotal entered := ⟨preparationFacts.2.1, preparationFacts.1⟩
    have bucketValid : ValidSuspended scs := preparationFacts.2.2.1
    have finishedCanonical := canonical_opaque_complete checkEmpty workFuel workFuel workFuel workFuel workFuel
      target scs value (SourcePruningEnumerationSelectedValueCaller.advance caller heap) completedCaller
      (EnumerationExpandableIndex.frame entered before) finished queries saved fragment
      entryFacts.1 bucketValid completed
    have finishedAliases := alias_opaque_complete checkEmpty workFuel workFuel workFuel workFuel workFuel
      target scs value (SourcePruningEnumerationSelectedValueCaller.advance caller heap) completedCaller
      (EnumerationExpandableIndex.frame entered before) finished queries saved fragment completed
    have finishedFacts : CanonicalTotal finished.core :=
      ⟨finishedCanonical, forward_total entered finished.core entryFacts.2 finishedAliases⟩
    have callbackFacts := callback_invariants graph templates workFuel uv metadata callbackMetadata
      fragment finished callbackCore finishedFacts recorded
    obtain ⟨events, ledger, retained⟩ := tailIH callbackFacts
    refine ⟨_, JointPreparedLedgerAt.opaque preparation (by cases value <;> exact mode)
      completed recorded input entryFacts bucketValid finishedFacts callbackFacts ledger, ?_⟩
    intro event member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | rfl | member
    · exact past
    · trivial
    · trivial
    · exact retained event member

  have capturedCase
      {depth uv target handle index rowIndex tailIndex : Nat}
      {metadata callbackMetadata : Metadata Typing}
      {caller rowCaller completedCaller : Caller (bits + 2)} {queries rowQueries saved : Queries}
      {before beforeFinalize finished : Cached} {scs : List Suspended} {decoded : Node}
      {entry : Cache.Interned InternedBinderProtocol.NodeKey} {rows : List Edge}
      {ordinaryDepth : Nat} {free : List InternedBinderProtocol.Reference}
      {heap : InternedConstructorTemplates.State Symbol Constraint} {entered callbackCore : Core}
      {attempted remaining : List Edge} {edge : Edge}
      {processed : List (SelectedEdge.Result (bits + 2))}
      {earlier later callbackEarlier callbackLater : List (Output (bits + 2) Typing)}
      {rowResult : Fold} {fragment : Fragment} {output : Output (bits + 2) Typing}
      (actual :
        let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
          (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
        let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order workFuel depth
        let hook := continueWith recur graph templates stop order workFuel metadata uv
        let rootBefore := EnumerationExpandableIndex.frame entered before
        let rootCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
        let visit := fun edge reached saved captured =>
          visitCapturedWith child hook workFuel target scs edge reached saved captured
        SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
          ([.ok ((target, handle, scs, decoded), entered)],
            some (.done (.node entry rows ordinaryDepth free) heap)) ∧
        scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
        edgesOf (.node entry rows ordinaryDepth free) = attempted ++ edge :: remaining ∧
        scan visit rootBefore attempted rootCaller queries = .complete processed earlier rowCaller rowQueries ∧
        visit edge rowCaller rowQueries rootBefore = rowResult ∧
        (outputs rowResult)[rowIndex]? = some output ∧
        index = earlier.length + rowIndex ∧
        outputs (scan visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries) =
          earlier ++ outputs rowResult ++ later ∧
        CapturedCallbackInvocationAt holeKey fits admits graph templates checkEmpty edgesOf stop order
          workFuel depth uv target metadata scs edge rowCaller rowQueries rootBefore rowIndex output
          fragment completedCaller saved beforeFinalize finished callbackMetadata callbackCore
          callbackEarlier callbackLater tailIndex ∧
        outputs rowResult = callbackEarlier ++ emitted (recur callbackMetadata completedCaller saved
          (EnumerationExpandableIndex.frame callbackCore finished)
          (SourcePruningEnumerationRestart.decision stop order callbackMetadata
            (EnumerationExpandableIndex.frame callbackCore finished))) ++ callbackLater ∧
        rowIndex = callbackEarlier.length + tailIndex)
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) tailIndex output)
      (past : EnumerationDischargeHistory.HeldFragmentHistory held heldHandle anchor before.core)
      (_tailPast : HeldOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order
        workFuel held heldHandle anchor tail)
      (tailIH : CanonicalTotal (EnumerationExpandableIndex.frame callbackCore finished).core →
        ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          depth callbackMetadata completedCaller saved (EnumerationExpandableIndex.frame callbackCore finished)
          (SourcePruningEnumerationRestart.decision stop order callbackMetadata
            (EnumerationExpandableIndex.frame callbackCore finished)) tailIndex output events ∧
          OuterEntriesHeld held heldHandle anchor events) :
      CanonicalTotal before.core →
        ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          depth metadata uv caller queries before index output events ∧ OuterEntriesHeld held heldHandle anchor events := by
    intro input
    have receipt := actual
    dsimp only at receipt
    obtain ⟨preparation, _nonterminal, _rowOrder, _completedPrefix, _rowRun, _rowHit,
      _rowOffset, _rowWhole, invoked, _callbackWhole, _callbackOffset⟩ := receipt
    have preparationFacts := SourcePruningEnumerationPreparationEntryInvariants.successful_preparation_entry_invariants
      workFuel workFuel uv target handle scs caller before entered decoded
      (.node entry rows ordinaryDepth free) heap input.1 input.2 preparation
    have entryFacts : CanonicalTotal entered := ⟨preparationFacts.2.1, preparationFacts.1⟩
    have bucketValid : ValidSuspended scs := preparationFacts.2.2.1
    have selectedReceipt := invoked
    dsimp only [CapturedCallbackInvocationAt] at selectedReceipt
    obtain ⟨selected, _selectedWhole, _selectedHit, _selectedOffset, finalized, recorded⟩ := selectedReceipt
    have rowCanonical := SourcePruningEnumerationInvocationCanonical.selected_complete_canonical
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf .eager _ scs edge
      rowCaller completedCaller (EnumerationExpandableIndex.frame entered before) beforeFinalize
      rowQueries saved rowIndex output fragment tailIndex entryFacts.1 bucketValid selected
    have rowAliases := SourcePruningEnumerationInvocationRawAliasGrowth.selected_complete_sameClass_forward
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf .eager _ scs edge
      rowCaller completedCaller (EnumerationExpandableIndex.frame entered before) beforeFinalize
      rowQueries saved rowIndex output fragment tailIndex selected
    have rowFacts : CanonicalTotal beforeFinalize.core :=
      ⟨rowCanonical, forward_total entered beforeFinalize.core entryFacts.2 rowAliases⟩
    have finishedFacts := finalized_invariants completedCaller.checked.native.machine.heap workFuel target
      fragment beforeFinalize finished rowFacts finalized
    have callbackFacts := callback_invariants graph templates workFuel uv metadata callbackMetadata
      fragment finished callbackCore finishedFacts recorded
    obtain ⟨events, ledger, retained⟩ := tailIH callbackFacts
    obtain ⟨nestedEvents, nestedLedger⟩ := captured_invocation_event_ledger
      holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel depth uv target metadata scs edge rowCaller rowQueries
      (EnumerationExpandableIndex.frame entered before) rowIndex output fragment completedCaller saved
      beforeFinalize finished callbackMetadata callbackCore callbackEarlier callbackLater tailIndex invoked
    refine ⟨_, JointPreparedLedgerAt.captured actual input entryFacts bucketValid rowFacts finishedFacts
      callbackFacts ledger nestedLedger, ?_⟩
    intro event member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact past
    · rcases List.mem_append.mp member with nested | suffix
      · obtain ⟨nestedEvent, _nestedMember, same⟩ := List.mem_map.mp nested
        subst event
        trivial
      · simp only [List.mem_cons] at suffix
        rcases suffix with rfl | rfl | member
        · trivial
        · trivial
        · exact retained event member

  constructor
  · intro depth metadata caller queries before decision index output history qualified
    exact HeldOutputHistoryAt.rec
      (motive_1 := fun {depth} {metadata} {caller} {queries} {before} {decision} {index} {output} _history _qualified =>
        CanonicalTotal before.core →
          ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
            depth metadata caller queries before decision index output events ∧ OuterEntriesHeld held heldHandle anchor events)
      (motive_2 := fun {depth} {metadata} {uv} {caller} {queries} {before} {index} {output} _history _qualified =>
        CanonicalTotal before.core →
          ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
            depth metadata uv caller queries before index output events ∧ OuterEntriesHeld held heldHandle anchor events)
      @stoppedCase @doneCase @parkedCase @selectedCase @opaqueCase @capturedCase qualified
  · intro depth metadata uv caller queries before index output history qualified
    exact HeldPreparedHistoryAt.rec
      (motive_1 := fun {depth} {metadata} {caller} {queries} {before} {decision} {index} {output} _history _qualified =>
        CanonicalTotal before.core →
          ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
            depth metadata caller queries before decision index output events ∧ OuterEntriesHeld held heldHandle anchor events)
      (motive_2 := fun {depth} {metadata} {uv} {caller} {queries} {before} {index} {output} _history _qualified =>
        CanonicalTotal before.core →
          ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
            depth metadata uv caller queries before index output events ∧ OuterEntriesHeld held heldHandle anchor events)
      @stoppedCase @doneCase @parkedCase @selectedCase @opaqueCase @capturedCase qualified

theorem held_output_history_joint_event_ledger
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel held heldHandle : Nat) (anchor : Core)
    (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
    (queries : Queries) (before : Cached) (decision : Option Next)
    (index : Nat) (output : Output (bits + 2) Typing)
    (history : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      depth metadata caller queries before decision index output)
    (qualified : HeldOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      held heldHandle anchor history)
    (canonical : Canonical before.core) (total : UnionFind.Total before.core.representatives) :
    ∃ events, JointOutputLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      depth metadata caller queries before decision index output events ∧ OuterEntriesHeld held heldHandle anchor events := by
  exact (held_history_ledgers holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel held heldHandle anchor).1
      depth metadata caller queries before decision index output history qualified ⟨canonical, total⟩

theorem held_prepared_history_joint_event_ledger
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel held heldHandle : Nat) (anchor : Core)
    (depth : Nat) (metadata : Metadata Typing) (uv : Nat) (caller : Caller (bits + 2))
    (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing)
    (history : PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      depth metadata uv caller queries before index output)
    (qualified : HeldPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      held heldHandle anchor history)
    (canonical : Canonical before.core) (total : UnionFind.Total before.core.representatives) :
    ∃ events, JointPreparedLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      depth metadata uv caller queries before index output events ∧ OuterEntriesHeld held heldHandle anchor events := by
  exact (held_history_ledgers holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel held heldHandle anchor).2
      depth metadata uv caller queries before index output history qualified ⟨canonical, total⟩

end MicroCFTA.SourcePruningEnumerationHeldJointCausalEventLedger
