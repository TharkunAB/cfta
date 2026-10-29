import MicroCFTA.SourcePruningEnumerationConstructorStorageProgress
import MicroCFTA.SourcePruningEnumerationShallowChildLanguage
import MicroCFTA.SourcePruningEnumerationFinalizeLanguage
import MicroCFTA.EnumerationSemantics

/-!
# One assignment for actual constructor models and storage cost

The assignment is the same install witness used by the storage cost theorem.
Old storage bounds preserve the original model and suspended obligations.
The actual completed nonterminal trace supplies each fresh graph slot.
-/
namespace MicroCFTA.SourcePruningEnumerationConstructorModelProgress
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open EnumerationStorageProgress
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}
local instance constructorModelMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private theorem align_restrictions
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (assignment extended : Nat → Term Symbol) (limit : Nat)
    (agree : ∀ uv < limit, extended uv = assignment uv)
    {inputs : List (Node × List Suspended)} {terms : List (Term Symbol)}
    (accepted : All₂ (fun (input : Node × List Suspended) term =>
      InternedGuardedLanguage.meaning holds ambient input.1 term ∧
      ∀ sc ∈ input.2, Suspended.Holds assignment term sc) inputs terms) :
    ∀ fragments : List Fragment, fragments.map (Fragments.fill extended) = terms →
      (∀ incoming bucket, (incoming, bucket) ∈ inputs → ∀ sc ∈ bucket, sc.var < limit) →
      All₂ (fun (input : Node × List Suspended) fragment =>
        InternedGuardedLanguage.meaning holds ambient input.1 (Fragments.fill extended fragment) ∧
        ∀ sc ∈ input.2, Suspended.Holds extended (Fragments.fill extended fragment) sc) inputs fragments := by
  induction accepted with
  | nil =>
      intro fragments filled _bounded
      cases fragments with
      | nil => exact .nil
      | cons first rest => simp at filled
  | @cons input term inputs terms head _tail ih =>
      intro fragments filled bounded
      cases fragments with
      | nil => simp at filled
      | cons fragment fragments =>
          obtain ⟨headFill, tailFill⟩ := List.cons.inj filled
          apply All₂.cons
          · constructor
            · simpa only [headFill] using head.1
            · intro sc member path present
              have old := head.2 sc member path present
              rw [headFill, agree sc.var (bounded input.1 input.2 List.mem_cons_self sc member)]
              exact old
          · exact ih fragments tailFill (fun incoming bucket member =>
              bounded incoming bucket (List.mem_cons_of_mem _ member))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem nonterminal_models
    (checkEmpty : Bool) (r n p h k : Nat) (bucket : List Suspended) (incoming : Node)
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (fragment : Fragment) (outer : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting)
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (coherent : InternedRecordCoherence.Coherent caller.checked.native.machine.heap)
    (storage : StorageValid before.core)
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (satisfied : Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
      caller.checked.native.machine.heap) meaning assignment before.core)
    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter)
    (nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (accepted : InternedGuardedLanguage.meaning holds ambient incoming (Fragments.fill assignment fragment))
    (inherited : ∀ sc ∈ bucket, Suspended.Holds assignment (Fragments.fill assignment fragment) sc)
    (observed : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k bucket incoming caller before queries =
      ((.ok (some [.ok (fragment, after.core)]), reached, saved, outer, waiting), some after)) :
    reached = caller ∧ saved = queries ∧ after.core.counter = before.core.counter + 1 ∧
      StorageValid after.core ∧ PendingRealized caller.checked.native.machine.heap after.core ∧
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
        caller.checked.native.machine.heap) meaning assignment after.core ∧
      FragmentBound after.core.counter fragment := by
  have nonempty : incoming ≠ .empty := by
    intro same
    subst incoming
    simp [SourcePruningEnumerationChildDispatch.run] at observed
  have noHere : (bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = [] := by
    simp only [List.partition_eq_filter_filter]
    exact List.filter_eq_nil_iff.mpr (fun sc member => List.any_eq_false.mp nonterminal sc member)
  obtain ⟨handle, _encoded, _decoded, _rejected, produced, models⟩ :=
    SourcePruningEnumerationShallowChild.prepareChild_complete_semantics
      caller.checked.native.machine.heap before.core bucket incoming coherent available closed realized
      storage.aligned nonterminal
  obtain ⟨action, canonical, prepared, success, shape, _slot, counter, _aligned, afterRealized⟩ := produced nonempty
  have rawObserved := (SourcePruningEnumerationChildDispatch.erase checkEmpty r n p h k
    bucket incoming caller before queries).symm.trans (congrArg Prod.fst observed)
  cases partitioned : bucket.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
  | mk here descendants =>
      have same : here = [] := by simpa only [partitioned] using noHere
      subst here
      simp only [SourcePruningEnumerationChildDispatch.observe, ite_eq_right nonempty,
        partitioned, prepared] at rawObserved
      have callerSame : caller = reached := congrArg (fun result => result.2.1) rawObserved
      have queriesSame : queries = saved := congrArg (fun result => result.2.2.1) rawObserved
      have actionRun : ExceptT.run (action before.core) = [.ok (fragment, after.core)] :=
        Option.some.inj (Except.ok.inj (congrArg Prod.fst rawObserved))
      change (.ok (.hole before.core.counter, canonical)) ∈ ExceptT.run (action before.core) at success
      rw [actionRun] at success
      have pairSame := Except.ok.inj (List.mem_singleton.mp success)
      have fragmentSame : fragment = .hole before.core.counter := (congrArg Prod.fst pairSame).symm
      have coreSame : canonical = after.core := congrArg Prod.snd pairSame
      rw [coreSame] at shape counter afterRealized
      obtain ⟨semanticAction, semanticAfter, semanticPrepared, semanticSuccess, exactModels⟩ := models nonempty
      have actionSame : semanticAction = action := Option.some.inj (semanticPrepared.symm.trans prepared)
      subst semanticAction
      change (.ok (.hole before.core.counter, semanticAfter)) ∈ ExceptT.run (action before.core) at semanticSuccess
      rw [actionRun] at semanticSuccess
      have semanticSame : semanticAfter = after.core :=
        congrArg Prod.snd (Except.ok.inj (List.mem_singleton.mp semanticSuccess))
      subst semanticAfter
      have filled : Fragments.fill assignment fragment = assignment before.core.counter := by
        simp only [fragmentSame, Fragments.fill]
      have nativeAccepted : InternedGuardedLanguage.meaning holds ambient incoming
          (assignment before.core.counter) := by simpa only [filled] using accepted
      have oldHolds : ∀ sc ∈ bucket, Suspended.Holds assignment (assignment before.core.counter) sc := by
        simpa only [filled] using inherited
      have retainedHolds : ∀ sc ∈ (match incoming with | .node _ _ _ _ => bucket | _ => []),
          Suspended.Holds assignment (assignment before.core.counter) sc := by
        cases incoming with
        | node _ _ _ _ => exact oldHolds
        | empty => simp
        | reference _ => simp
        | union _ _ _ _ => simp
        | mu _ _ _ _ => simp
      have modelAfter : Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
          caller.checked.native.machine.heap) meaning assignment after.core := by
        apply (exactModels holds ambient meaning assignment).mpr
        refine ⟨satisfied, nativeAccepted, ?_⟩
        cases incoming <;> exact retainedHolds
      have baseStorage := allocation_storage (some handle) before.core storage
      have storageAfter : StorageValid after.core := by
        rw [shape]
        cases incoming with
        | node _ _ _ _ =>
            apply set_storage _ baseStorage before.core.counter (.unenumerated (some handle) bucket)
            intro sc member
            exact Nat.lt_trans (bounded sc member) (Nat.lt_succ_self before.core.counter)
        | empty => exact baseStorage
        | reference _ => exact baseStorage
        | union _ _ _ _ => exact baseStorage
        | mu _ _ _ _ => exact baseStorage
      refine ⟨callerSame.symm, queriesSame.symm, counter, storageAfter, afterRealized, modelAfter, ?_⟩
      simp only [fragmentSame, FragmentBound, counter]
      omega

private theorem trace_models
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller reached : Caller width} {before after : Cached} {queries saved : Queries}
    {fragments : List Fragment}
    (trace : SourcePruningEnumerationChildTraversal.Trace checkEmpty r n p h k inputs caller before queries
      fragments reached after saved) :
    ∀ (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
      (meaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
      InternedRecordCoherence.Coherent caller.checked.native.machine.heap → StorageValid before.core →
      PendingRealized caller.checked.native.machine.heap before.core →
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient caller.checked.native.machine.heap)
        meaning assignment before.core →
      (∀ incoming bucket, (incoming, bucket) ∈ inputs →
        Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
        ∀ sc ∈ bucket, sc.var < before.core.counter) →
      (∀ incoming bucket, (incoming, bucket) ∈ inputs →
        bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) →
      All₂ (fun (input : Node × List Suspended) fragment =>
        InternedGuardedLanguage.meaning holds ambient input.1 (Fragments.fill assignment fragment) ∧
        ∀ sc ∈ input.2, Suspended.Holds assignment (Fragments.fill assignment fragment) sc) inputs fragments →
      reached = caller ∧ saved = queries ∧ before.core.counter ≤ after.core.counter ∧
      StorageValid after.core ∧ PendingRealized caller.checked.native.machine.heap after.core ∧
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient caller.checked.native.machine.heap)
        meaning assignment after.core ∧ ∀ fragment ∈ fragments, FragmentBound after.core.counter fragment := by
  induction trace with
  | nil =>
      intro holds ambient meaning assignment _coherent storage realized satisfied _genuine _nonterminal _restrictions
      exact ⟨rfl, rfl, Nat.le_refl _, storage, realized, satisfied, by simp⟩
  | @cons incoming bucket rest caller middleCaller finalCaller before middle final queries middleQueries finalQueries
      fragment fragments outer waiting head _tail ih =>
      intro holds ambient meaning assignment coherent storage realized satisfied genuine nonterminal restrictions
      cases restrictions with
      | cons firstRestrictions restRestrictions =>
          obtain ⟨available, closed, bounded⟩ := genuine incoming bucket List.mem_cons_self
          obtain ⟨callerSame, querySame, counter, middleStorage, middleRealized, middleModel, headBound⟩ :=
            nonterminal_models checkEmpty r n p h k bucket incoming caller middleCaller before middle queries middleQueries
              fragment outer waiting holds ambient meaning assignment coherent storage realized satisfied
              available closed bounded (nonterminal incoming bucket List.mem_cons_self)
              firstRestrictions.1 firstRestrictions.2 head
          subst middleCaller
          have tailGenuine : ∀ value scs, (value, scs) ∈ rest →
              Available caller.checked.native.machine.heap value ∧ value.free = [] ∧
              ∀ sc ∈ scs, sc.var < middle.core.counter := by
            intro value scs member
            obtain ⟨present, closedValue, bounds⟩ := genuine value scs (List.mem_cons_of_mem _ member)
            exact ⟨present, closedValue, fun sc found => by have old := bounds sc found; omega⟩
          obtain ⟨finalCallerSame, finalQuerySame, growth, finalStorage, finalRealized, finalModel, tailBounds⟩ :=
            ih holds ambient meaning assignment coherent middleStorage middleRealized middleModel tailGenuine
              (fun value scs member => nonterminal value scs (List.mem_cons_of_mem _ member)) restRestrictions
          refine ⟨finalCallerSame, finalQuerySame.trans querySame, ?_, finalStorage, finalRealized, finalModel, ?_⟩
          · omega
          · intro child member
            rcases List.mem_cons.mp member with same | later
            · subst child
              exact fragmentBound_mono middle.core.counter final.core.counter growth fragment headBound
            · exact tailBounds child later

/-- The actual nonterminal trace shares one installed assignment between its model and its exact cost. -/
theorem trace_model_pendingSize
    {checkEmpty : Bool} {r n p h k : Nat} {inputs : List (Node × List Suspended)}
    {caller reached : Caller width} {before after : Cached} {queries saved : Queries}
    {fragments : List Fragment}
    (trace : SourcePruningEnumerationChildTraversal.Trace checkEmpty r n p h k inputs caller before queries
      fragments reached after saved)
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol) (terms : List (Term Symbol))
    (coherent : InternedRecordCoherence.Coherent caller.checked.native.machine.heap)
    (storage : StorageValid before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (satisfied : Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient caller.checked.native.machine.heap)
      meaning assignment before.core)
    (genuine : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      ∀ sc ∈ bucket, sc.var < before.core.counter)
    (nonterminal : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (accepted : All₂ (fun (input : Node × List Suspended) term =>
      InternedGuardedLanguage.meaning holds ambient input.1 term ∧
      ∀ sc ∈ input.2, Suspended.Holds assignment term sc) inputs terms) :
    ∃ extended,
      (extended = install assignment before.core.counter terms ∧
        (∀ uv < before.core.counter, extended uv = assignment uv) ∧
        after.core.counter = before.core.counter + terms.length ∧
        after.core.counter = after.core.values.length ∧
        (∀ uv < before.core.counter, after.core.values[uv]? = before.core.values[uv]?) ∧
        fragments.map (Fragments.fill extended) = terms ∧
        pendingSize after.core extended = pendingSize before.core assignment + NumberedTerms.forestSize terms) ∧
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient caller.checked.native.machine.heap)
        meaning extended before.core ∧ reached = caller ∧ saved = queries ∧ StorageValid after.core ∧
      PendingRealized reached.checked.native.machine.heap after.core ∧
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient reached.checked.native.machine.heap)
        meaning extended after.core ∧ ∀ fragment ∈ fragments, FragmentBound after.core.counter fragment := by
  obtain ⟨extended, packet⟩ := SourcePruningEnumerationConstructorStorageProgress.trace_pendingSize
    trace assignment terms accepted.length_eq.symm storage.aligned nonterminal
  have beforeModel := (state_assignment_congr _ meaning before.core storage extended assignment packet.2.1).mpr satisfied
  have restrictions := align_restrictions holds ambient assignment extended
    before.core.counter packet.2.1 accepted fragments packet.2.2.2.2.2.1
    (fun incoming bucket member => (genuine incoming bucket member).2.2)
  obtain ⟨callerSame, queriesSame, _growth, afterStorage, afterRealized, afterModel, bounds⟩ :=
    trace_models trace holds ambient meaning extended coherent storage realized beforeModel genuine nonterminal restrictions
  refine ⟨extended, packet, beforeModel, callerSame, queriesSame, afterStorage, ?_, ?_, bounds⟩
  · simpa only [callerSame] using afterRealized
  · simpa only [callerSame] using afterModel

/-- Actual residual recording and captured finalization retain that model and decrease its cost by one. -/
theorem constructor_model_pendingSize
    (checkEmpty : Bool) (r n p h k : Nat) (inputs : List (Node × List Suspended))
    (caller reached : Caller width) (before traversed after : Cached) (queries saved : Queries)
    (fragments : List Fragment) (assignment : Nat → Term Symbol) (symbol : Symbol)
    (terms : List (Term Symbol)) (target handle : Nat) (scs : List Suspended) (residual : Option Constraint)
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : Constraint → Term Symbol → Prop)
    (coherent : InternedRecordCoherence.Coherent caller.checked.native.machine.heap)
    (storage : StorageValid before.core) (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (satisfied : Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient caller.checked.native.machine.heap)
      meaning assignment before.core)
    (genuine : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      ∀ sc ∈ bucket, sc.var < before.core.counter)
    (nonterminal : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (accepted : All₂ (fun (input : Node × List Suspended) term =>
      InternedGuardedLanguage.meaning holds ambient input.1 term ∧
      ∀ sc ∈ input.2, Suspended.Holds assignment term sc) inputs terms)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (parent : assignment target = .node symbol terms)
    (guarded : ResidualHolds meaning residual (assignment target))
    (completed : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k inputs caller before queries =
      .complete fragments reached saved traversed)
    (finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target
      (.node symbol fragments) (SourcePruningEnumerationSelectedEdge.finish residual (.node symbol fragments) traversed) =
      some after) :
    ∃ extended,
      (extended = install assignment before.core.counter terms ∧
        (∀ uv < before.core.counter, extended uv = assignment uv) ∧
        Fragments.fill extended (.node symbol fragments) = assignment target ∧
        pendingSize after.core extended + 1 = pendingSize before.core assignment ∧
        pendingSize after.core extended < pendingSize before.core assignment) ∧
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient caller.checked.native.machine.heap)
        meaning extended before.core ∧ reached = caller ∧ saved = queries ∧
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient reached.checked.native.machine.heap)
        meaning extended after.core := by
  have trace := SourcePruningEnumerationChildTraversal.complete_trace checkEmpty r n p h k
    inputs caller reached before traversed queries saved fragments completed
  obtain ⟨extended, packet, oldModel, callerSame, querySame, _traversedStorage, _traversedRealized,
      traversedModel, _bounds⟩ :=
    trace_model_pendingSize trace holds ambient meaning assignment terms coherent storage realized satisfied
      genuine nonterminal accepted
  have agree := packet.2.1
  have oldSlots := packet.2.2.2.2.1
  have fills := packet.2.2.2.2.2.1
  have traversalCost := packet.2.2.2.2.2.2
  have inside : target < before.core.counter := by
    have bound := (List.getElem?_eq_some_iff.mp stored).1
    have aligned := storage.aligned
    change before.core.counter = before.core.values.length at aligned
    omega
  have filled : Fragments.fill extended (.node symbol fragments) = assignment target := by
    simp only [Fragments.fill, fills, parent]
  let recorded := SourcePruningEnumerationSelectedEdge.finish residual (.node symbol fragments) traversed
  have recording : Success (recordResidual residual (.node symbol fragments)) traversed.core () recorded.core := by
    change (.ok ((), recorded.core)) ∈ ExceptT.run (recordResidual residual (.node symbol fragments) traversed.core)
    rw [SourcePruningEnumerationSelectedEdge.finish_raw]
    exact List.mem_cons_self
  have recordedModel := (EnumerationSemantics.recordResidual_assignment
    (SourcePruningEnumerationNativeLanguage.handles holds ambient reached.checked.native.machine.heap)
    meaning extended residual (.node symbol fragments) traversed.core recorded.core recording).mpr
      ⟨traversedModel, by simpa only [filled] using guarded⟩
  have storedAfter : recorded.core.values[target]? = some (.unenumerated (some handle) scs) :=
    (oldSlots target inside).trans stored
  have coreWritten : after.core = {recorded.core with
      values := recorded.core.values.set target (.enumerated (.node symbol fragments)), expansionAncestry := []} := by
    simp only [SourcePruningEnumerationFinalize.run, Option.bind_eq_some_iff] at finalized
    obtain ⟨_old, _stored, written⟩ := finalized
    simp only [SourcePruningEnumerationNativeIndex.write, Option.bind_eq_some_iff, Option.some.injEq] at written
    obtain ⟨_flag, _classified, _removed, _removedCounts, _saved, _savedCounts, same⟩ := written
    subst after
    rfl
  have equation : Fragments.fill extended (.node symbol fragments) = extended target :=
    filled.trans (agree target inside).symm
  have afterModel := (SourcePruningEnumerationFinalize.written_semantics recorded.core after.core target
    (.node symbol fragments) ((List.getElem?_eq_some_iff.mp storedAfter).1) coreWritten
    (SourcePruningEnumerationNativeLanguage.handles holds ambient reached.checked.native.machine.heap)
    meaning extended).mpr
      ⟨EnumerationFrame.neutralize_satisfies _ meaning extended target recorded.core recordedModel, equation⟩
  have finalCost := SourcePruningEnumerationStorageProgress.finalize_pendingSize
    reached.checked.native.machine.heap k target handle (.node symbol fragments) scs recorded after extended
      storedAfter finalized
  have recordingCost : pendingSize recorded.core extended = pendingSize traversed.core extended := rfl
  rw [recordingCost] at finalCost
  have targetSame : extended target = .node symbol terms := (agree target inside).trans parent
  have decrease : pendingSize after.core extended + 1 = pendingSize before.core assignment := by
    rw [targetSame, NumberedTerms.size] at finalCost
    omega
  exact ⟨extended, ⟨packet.1, agree, filled, decrease, by omega⟩, oldModel, callerSame, querySame, afterModel⟩

end MicroCFTA.SourcePruningEnumerationConstructorModelProgress
