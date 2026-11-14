import MicroCFTA.SourceSynthesisCurrentInitialPrefixOrigin
import MicroCFTA.SourceSynthesisCurrentInitialOuterNarrowFacts
import MicroCFTA.SourcePruningEnumerationSelectedPreparation
import MicroCFTA.SourcePruningEnumerationSelectedStepCompletion

namespace MicroCFTA.SourceSynthesisCurrentInitialPrefixOrigin
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Core" => EnumerationState.State Symbol Guard
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
local notation "Metadata" => SourcePruningRecordTypes.Metadata

local instance preparationMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private theorem ordinary_encoded_lookup
    (heap : InternedConstructorTemplates.State Symbol Guard) (value : Node)
    (facts : Facts heap) (available : Available heap value)
    (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (handle : Nat) (encoded : encodeNode value = some handle) :
    lookupNode heap handle = some value := by
  cases value with
  | empty =>
      simp only [encodeNode, Option.some.injEq] at encoded
      subst handle
      rfl
  | reference | union | mu => cases ordinary
  | node entry rows depth free =>
      simp only [encodeNode, Option.some.injEq] at encoded
      subst handle
      have canonical : heap.nodes.table entry.key = some entry :=
        InternedFreshProbeKeys.resident_entry heap facts.coherent _ available.resident entry rfl
      have issued : heap.nodes.issued entry.identity = some entry.key :=
        (facts.coherent.valid.2.2 entry.key entry canonical).2
      simpa only [lookupNode, issued, canonical, ↓reduceIte] using available.resident entry rfl

private theorem false_check_safe
    (heap : InternedConstructorTemplates.State Symbol Guard) (value : Node)
    (fuel handle : Nat) (before after : Core)
    (safe : Safe before) (inside : 0 < before.counter)
    (root : IsRoot before.representatives 0)
    (decoded : lookupNode heap handle = some value)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated
      heap fuel 0 handle []) before false after) : Safe after := by
  by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
  · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded,
      boundary, ↓reduceIte] at observed
    obtain ⟨selected, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
    obtain ⟨selectedSame, resolvedSafe, _counter, _protected⟩ :=
      EnumerationDriver.representative_root fuel 0 selected before resolved safe inside root resolution
    subst selected
    obtain ⟨current, readAfter, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
    obtain ⟨currentSame, readSame⟩ := (EnumerationDriver.get_success resolved readAfter current).mp reading
    subst current
    subst readAfter
    by_cases seen : recursionKey handle [] ∈ resolved.recursionAncestry 0
    · rw [ite_eq_left seen] at continued
      obtain ⟨token, written, _writing, finished⟩ := (success_bind _ _ _ _ _).mp continued
      cases token
      have impossible := (success_pure true false written after).mp finished
      cases impossible.1
    · rw [ite_eq_right seen] at continued
      obtain ⟨_same, rfl⟩ := (success_pure false false resolved after).mp continued
      exact resolvedSafe
  · have pureRead : Success (pure false) before false after := by
      simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded,
        ite_eq_right boundary] using observed
    obtain ⟨_same, rfl⟩ := (success_pure false false before after).mp pureRead
    exact safe

private theorem entered_zero_observation
    (heap : InternedConstructorTemplates.State Symbol Guard) (value : Node)
    (fuel handle : Nat) (before after : Core)
    (entry : Nat × Nat × List Suspended × Node)
    (safe : Safe before) (inside : 0 < before.counter)
    (root : IsRoot before.representatives 0)
    (stored : before.values[0]? = some (.unenumerated (some handle) []))
    (decoded : lookupNode heap handle = some value)
    (observed : ExceptT.run (SourcePruningEnumerationEntry.enter heap fuel 0 before) =
      [.ok (entry, after)]) :
    entry = (0, handle, [], value) ∧ EnumerationDriver.RenderStable before after := by
  have success : Success (SourcePruningEnumerationEntry.enter heap fuel 0) before entry after := by
    unfold Success
    rw [observed]
    exact List.mem_cons_self
  unfold SourcePruningEnumerationEntry.enter at success
  obtain ⟨pending, readAfter, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readSafe, readCounter, readProtection, readStored⟩ :=
    EnumerationDriver.getValue_root fuel 0 before readAfter pending safe inside root reading
  have pendingSame : pending = .unenumerated (some handle) [] :=
    Option.some.inj (readStored.symm.trans (readProtection.value.trans stored))
  subst pending
  obtain ⟨target, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨targetSame, resolvedSafe, _counter, _protection⟩ :=
    EnumerationDriver.representative_root fuel 0 target readAfter resolved readSafe
      (by simpa only [readCounter] using inside) readProtection.root resolution
  subst target
  rw [decoded] at continued
  obtain ⟨token, written, writing, finished⟩ := (success_bind _ _ _ _ _).mp continued
  cases token
  have shape := (EnumerationDriver.modify_success _ resolved written).mp writing
  obtain ⟨entrySame, afterSame⟩ :=
    (success_pure (0, handle, [], value) entry written after).mp finished
  have readFrame := (getValue_frame fuel 0 before readAfter _ safe.1.total reading).1
  have resolvedFrame := representative_frame fuel 0 0 readAfter resolved readSafe.1.total resolution
  have wholeFrame := readFrame.trans resolvedFrame
  refine ⟨entrySame, ?_⟩
  rw [afterSame, shape]
  refine ⟨EnumerationDriver.ancestry_safe resolved _ resolvedSafe,
    wholeFrame.counter, wholeFrame.values, wholeFrame.obligations, ?_⟩
  intro left right
  simp only [UnionFind.SameClass, wholeFrame.reaches]

/-- Trace actual initial selected preparation to the same original source rows. -/
theorem initial_prefix_preparation_rows
    {Typing Key : Type} {width : Nat}
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : SourceSynthesisFirstOrderConstruction.Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols whole) []
      InternedConstructorTemplates.empty = .done rootValue heap)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (handle : Nat)
    (decoded : SourcePruningEnumerationNodes.lookupNode heap handle = some rootValue)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Node → Bool)
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel : Nat)
    (entryFuel preparationFuel : Nat)
    (queries : SourceEndpointMemo.Memos) :
    let caller := SourceCurrentAllocatedPartialInitialization.caller width cache heap
    let startup : Cached :=
      ⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
        fun _ => none⟩
    match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
      stop order metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel
      0 caller startup queries with
    | .narrowed _checked (.done (narrowed, some _action) narrowedHeap) reached saved
        (some [.ok ((), _actionCore)]) (some candidate)
        (some [.ok ((false, updated), callbackCore)]) none =>
        saved = queries ∧ updated = metadata ∧ callbackCore = candidate.core ∧
        reached.checked.native.machine.heap = narrowedHeap ∧
        SourceEqualityRequiredCache.Ordinary narrowed ∧
        ∃ newHandle : Nat,
          SourcePruningEnumerationNodes.encodeNode narrowed = some newHandle ∧
          SourcePruningEnumerationNodes.lookupNode narrowedHeap newHandle = some narrowed ∧
          candidate.core.values[0]? = some (.unenumerated (some newHandle) []) ∧
          match SourcePruningEnumerationSelectedPreparation.run entryFuel preparationFuel
            0 reached candidate with
          | ([.ok ((target, readHandle, scs, decodedValue), entered)],
              some (.done prepared preparedHeap)) =>
              target = 0 ∧ readHandle = newHandle ∧ scs = [] ∧
              decodedValue = narrowed ∧ prepared = narrowed ∧ preparedHeap = narrowedHeap ∧
              EnumerationDriver.RenderStable candidate.core entered ∧
              (SourcePruningEnumerationSelectedValueCaller.advance reached
                preparedHeap).checked.native.machine.heap = narrowedHeap ∧
              ∀ row ∈ InternedEdgeResidency.nodeEdges prepared,
                row ∈ InternedEdgeResidency.nodeEdges rootValue
          | _ => True
    | _ => True := by
  let caller := SourceCurrentAllocatedPartialInitialization.caller width cache heap
  let startup : Cached :=
    ⟨EnumerationState.initial handle,
      fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
      fun _ => none⟩
  dsimp only
  split
  · rename_i checked narrowed action narrowedHeap reached saved actionCore candidate updated callbackCore prefixEq
    have origin := initial_prefix_narrowed_rows (width := width) lib query signed whole accepted
      rootValue heap built cache handle decoded holeKey fits admits graph templates stop order
      metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel queries
    dsimp only at origin
    rw [prefixEq] at origin
    obtain ⟨readAfter, reading, checking, checkedFrame, prepared, native,
      reachedSame, savedSame, _ordinaryNone, included⟩ := origin
    obtain ⟨nativeFacts, nativeAvailable, ordinary⟩ :=
      SourceSynthesisCurrentInitialOuterNarrowFacts.initial_outer_narrow_facts
        lib query signed whole accepted rootValue heap built metadata holeKey fits admits
        nativeFuel narrowed narrowedHeap native
    have reachedHeap : reached.checked.native.machine.heap = narrowedHeap := by
      rw [reachedSame]
      rfl
    have copied : (match (generalizing := false)
        SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
          metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel
          0 caller startup queries with
      | .narrowed _ _ _ _ raw _ _ _ => raw
      | _ => none) = some (ExceptT.run (action checked)) := by
      unfold SourcePruningEnumerationSelectedStep.runPrefix SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      dsimp only [caller, startup, SourceCurrentAllocatedPartialInitialization.caller,
        SourceCurrentAllocatedPartialState.initial, SourceCurrentAllocatedPartialInitialization.checked,
        SourceRecursiveIntersectionThunks.initial]
      simp only [reading, checking, decoded, ← SourcePruningEnumerationAction.prepare_configured_eq, prepared]
      cases execution : ExceptT.run (action checked) with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | cons second rest =>
              cases first with
              | error error => rfl
              | ok pair =>
                  obtain ⟨token, _observed⟩ := pair
                  cases token
                  rfl
          | nil =>
              cases first with
              | error error => rfl
              | ok pair =>
                  obtain ⟨token, observed⟩ := pair
                  cases token
                  dsimp only
                  cases encodeNode narrowed with
                  | none => rfl
                  | some newHandle =>
                      dsimp only
                      cases SourcePruningEnumerationNarrowAdapter.adapt narrowedHeap indexFuel
                        0 handle newHandle [] startup observed with
                      | none => rfl
                      | some attached =>
                          rw [SourcePruningRecordTypes.recordTypes_inr]
                          rfl
    have fields := congrArg (fun observed : SourcePruningEnumerationSelectedStep.Result width Typing =>
      match (generalizing := false) observed with
      | .narrowed _ _ _ _ raw _ _ _ => raw
      | _ => none) prefixEq
    have executedRaw : ExceptT.run (action checked) = [.ok ((), actionCore)] :=
      Option.some.inj (copied.symm.trans fields)
    have executed : Success action checked () actionCore := by
      unfold Success
      rw [executedRaw]
      exact List.mem_cons_self
    have nonempty : narrowed ≠ .empty := by
      intro same
      subst narrowed
      have emptyPrepared := prepared
      simp only [SourcePruningEnumerationAction.prepare, SourcePruningEnumerationAction.prepareWithNarrow, native] at emptyPrepared
      have actionSame : (reject : EnumerateM Symbol Guard Unit) = action :=
        Option.some.inj (congrArg Prod.snd (MergedSourceComparison.Result.done.inj emptyPrepared).1)
      rw [← actionSame] at executedRaw
      change ([] : List (Except EnumerationState.Error (Unit × Core))) =
        [Except.ok ((), actionCore)] at executedRaw
      cases executedRaw
    obtain ⟨newHandle, encoded⟩ : ∃ newHandle, encodeNode narrowed = some newHandle := by
      cases narrowed with
      | empty => exact ⟨0, rfl⟩
      | node entry rows depth free => exact ⟨entry.identity + 1, rfl⟩
      | reference | union | mu => cases ordinary
    have nativeDecoded := ordinary_encoded_lookup narrowedHeap narrowed nativeFacts
      nativeAvailable ordinary newHandle encoded
    have readingSuccess : Success (getValue readFuel 0) startup.core
        (.unenumerated (some handle) []) readAfter := by
      unfold Success
      rw [reading]
      exact List.mem_cons_self
    have initialSafe : Safe startup.core := ⟨initial_storage handle, initial_live handle⟩
    have initialRoot : IsRoot startup.core.representatives 0 :=
      ⟨1, .root (UnionFind.read_initial [0] 0)⟩
    obtain ⟨readSafe, readCounter, readProtection, _readStored⟩ :=
      EnumerationDriver.getValue_root readFuel 0 startup.core readAfter _ initialSafe
        (by change 0 < 1; decide) initialRoot readingSuccess
    have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
        heap checkFuel 0 handle []) readAfter false checked := by
      unfold Success
      rw [checking]
      exact List.mem_cons_self
    have checkedSafe := false_check_safe heap rootValue checkFuel handle readAfter checked
      readSafe (by simpa only [readCounter] using (show 0 < startup.core.counter by change 0 < 1; decide))
      readProtection.root decoded checkSuccess
    have checkedRoot : IsRoot checked.representatives 0 :=
      ⟨1, (checkedFrame.reaches 0 0 1).mpr (.root (UnionFind.read_initial [0] 0))⟩
    have checkedInside : 0 < checked.counter := by rw [checkedFrame.counter]; change 0 < 1; decide
    have checkedStored : checked.values[0]? = some (.unenumerated (some handle) []) := by
      rw [checkedFrame.values]
      rfl
    have fixedPreparation := SourcePruningEnumerationSelectedStep.prepared_action
      holeKey fits admits metadata nativeFuel representativeFuel 0 handle newHandle []
      rootValue narrowed heap narrowedHeap native nonempty encoded
    have actionSame : action =
        (if newHandle = handle then (pure () : EnumerateM Symbol Guard Unit)
          else representative representativeFuel 0 >>= fun selected =>
            setValue selected (.unenumerated (some newHandle) [])) :=
      Option.some.inj (congrArg Prod.snd
        (MergedSourceComparison.Result.done.inj (prepared.symm.trans fixedPreparation)).1)
    have actionFacts : Safe actionCore ∧ 0 < actionCore.counter ∧
        IsRoot actionCore.representatives 0 ∧
        actionCore.values[0]? = some (.unenumerated (some newHandle) []) := by
      rw [actionSame] at executed
      by_cases same : newHandle = handle
      · rw [ite_eq_left same] at executed
        obtain ⟨_unit, rfl⟩ := (success_pure () () checked actionCore).mp executed
        exact ⟨checkedSafe, checkedInside, checkedRoot, by simpa only [same] using checkedStored⟩
      · rw [ite_eq_right same] at executed
        obtain ⟨selected, resolved, resolution, writing⟩ := (success_bind _ _ _ _ _).mp executed
        obtain ⟨selectedSame, resolvedSafe, resolvedCounter, protection⟩ :=
          EnumerationDriver.representative_root representativeFuel 0 selected checked resolved
            checkedSafe checkedInside checkedRoot resolution
        subst selected
        have written := EnumerationDriver.setValue_safe 0 (.unenumerated (some newHandle) [])
          resolved actionCore resolvedSafe protection.root
          (by intro impossible; cases impossible) (by intro sc member; cases member) writing
        have shape := (EnumerationDriver.modify_success _ resolved actionCore).mp writing
        have inside : 0 < resolved.values.length := by
          rw [← resolvedSafe.1.aligned, resolvedCounter]
          exact checkedInside
        refine ⟨written.1, ?_, ?_, ?_⟩
        · rw [written.2, resolvedCounter]
          exact checkedInside
        · rw [shape]
          exact protection.root
        · rw [shape]
          exact List.getElem?_set_self inside
    have actualPrefix := prefixEq
    unfold SourcePruningEnumerationSelectedStep.runPrefix SourcePruningEnumerationSelectedStep.runPrefixWithNarrow at actualPrefix
    dsimp only [SourceCurrentAllocatedPartialInitialization.caller,
      SourceCurrentAllocatedPartialState.initial, SourceCurrentAllocatedPartialInitialization.checked,
      SourceRecursiveIntersectionThunks.initial] at actualPrefix
    simp only [reading, checking, decoded, ← SourcePruningEnumerationAction.prepare_configured_eq, prepared, executedRaw, encoded] at actualPrefix
    generalize adapted : SourcePruningEnumerationNarrowAdapter.adapt narrowedHeap indexFuel
        0 handle newHandle []
        ⟨EnumerationState.initial handle,
          fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
          fun _ => none⟩ actionCore = adapter at actualPrefix
    cases adapter with
    | none =>
        cases actualPrefix
    | some attached =>
        simp only [SourcePruningRecordTypes.recordTypes_inr] at actualPrefix
        obtain ⟨_checkedAgain, _preparedAgain, _reachedAgain, _savedAgain,
          _rawAgain, candidateSame, rightSame, _ordinaryAgain⟩ :=
            SourcePruningEnumerationSelectedStep.Result.narrowed.inj actualPrefix
        have rightPair : ((false, metadata), attached.core) = ((false, updated), callbackCore) :=
          Except.ok.inj (List.cons.inj (Option.some.inj rightSame)).1
        have updatedSame : updated = metadata := (congrArg (fun pair => pair.1.2) rightPair).symm
        have callbackSame : callbackCore = attached.core := (congrArg Prod.snd rightPair).symm
        have candidateCore : candidate.core = attached.core :=
          (congrArg (fun state : Cached => state.core) (Option.some.inj candidateSame)).symm
        have attachedCore := SourcePruningEnumerationNarrowAdapter.adapt_core narrowedHeap indexFuel
          0 handle newHandle [] startup attached actionCore adapted
        have coreSame : candidate.core = actionCore := candidateCore.trans attachedCore
        have candidateSafe : Safe candidate.core := by simpa only [coreSame] using actionFacts.1
        have candidateInside : 0 < candidate.core.counter := by
          simpa only [coreSame] using actionFacts.2.1
        have candidateRoot : IsRoot candidate.core.representatives 0 := by
          simpa only [coreSame] using actionFacts.2.2.1
        have candidateStored : candidate.core.values[0]? =
            some (.unenumerated (some newHandle) []) := by
          simpa only [coreSame] using actionFacts.2.2.2
        refine ⟨savedSame, updatedSame, callbackSame.trans candidateCore.symm, reachedHeap,
          ordinary, newHandle, encoded, nativeDecoded, candidateStored, ?_⟩
        split
        · rename_i target readHandle scs decodedValue entered preparedValue preparedHeap preparationEq
          have entryRead : ExceptT.run (SourcePruningEnumerationEntry.enter
              reached.checked.native.machine.heap entryFuel 0 candidate.core) =
              [.ok ((target, readHandle, scs, decodedValue), entered)] :=
            congrArg Prod.fst preparationEq
          have enteredRead := entryRead
          rw [reachedHeap] at enteredRead
          obtain ⟨entrySame, stable⟩ := entered_zero_observation narrowedHeap narrowed
            entryFuel newHandle candidate.core entered (target, readHandle, scs, decodedValue)
            candidateSafe candidateInside candidateRoot candidateStored nativeDecoded enteredRead
          have targetSame : target = 0 := (Prod.mk.inj entrySame).1
          have handleSame : readHandle = newHandle := (Prod.mk.inj (Prod.mk.inj entrySame).2).1
          have scsSame : scs = [] := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj entrySame).2).2).1
          have decodedSame : decodedValue = narrowed :=
            (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj entrySame).2).2).2
          have preparedRead := preparationEq
          unfold SourcePruningEnumerationSelectedPreparation.run at preparedRead
          rw [entryRead] at preparedRead
          have selectedRead : SourcePruningEnumerationSelectedValue.run preparationFuel decodedValue
              reached.checked.native.machine.heap = .done preparedValue preparedHeap :=
            Option.some.inj (congrArg Prod.snd preparedRead)
          rw [reachedHeap] at selectedRead
          have selectedIdentity : SourcePruningEnumerationSelectedValue.run preparationFuel
              decodedValue narrowedHeap = .done narrowed narrowedHeap := by
            rw [decodedSame]
            cases narrowed with
            | empty | node => rfl
            | reference | union | mu => cases ordinary
          have same := MergedSourceComparison.Result.done.inj (selectedIdentity.symm.trans selectedRead)
          refine ⟨targetSame, handleSame, scsSame, decodedSame, same.1.symm, same.2.symm, stable, ?_, ?_⟩
          · rw [← same.2]
            rfl
          · rw [← same.1]
            exact included
        · trivial
  · trivial

end MicroCFTA.SourceSynthesisCurrentInitialPrefixOrigin
