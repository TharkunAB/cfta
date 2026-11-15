import MicroCFTA.SourcePruningEnumerationSharedPrefixResources
import MicroCFTA.SourcePruningEnumerationPreparedFuel
import MicroCFTA.SourcePruningEnumerationNativeIndexStability
import MicroCFTA.SourcePruningNarrowPrefixObservation
import MicroCFTA.EnumerationExecution
import MicroCFTA.EnumerationPartialExact
import MicroCFTA.MergedColdReaderTermination

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open EnumerationCompressionFrame InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

open MergedSourceExposure (Finished finished_prepend finished_canonical)

private theorem exposure_collect_stable (fuel extra : Nat)
    (state : InternedConstructorTemplates.State Symbol Constraint) (seen : List Nat) (pending : List (Value Symbol Constraint))
    (finished : MergedSourceExposure.Finished (MergedFreshOrdinaryExposure.collect fuel state seen pending)) :
    MergedFreshOrdinaryExposure.collect (fuel + extra) state seen pending = MergedFreshOrdinaryExposure.collect fuel state seen pending := by
  induction fuel generalizing state seen pending with
  | zero =>
      cases pending with
      | nil => simp [MergedFreshOrdinaryExposure.collect]
      | cons value rest => simp [MergedFreshOrdinaryExposure.collect, Finished] at finished
  | succ fuel ih =>
      cases pending with
      | nil => simp [MergedFreshOrdinaryExposure.collect]
      | cons value rest =>
          cases value with
          | empty => simpa only [Nat.succ_add, MergedFreshOrdinaryExposure.collect] using ih state seen rest finished
          | reference => simp only [Nat.succ_add, MergedFreshOrdinaryExposure.collect]
          | node entry edges depth free =>
              simp only [MergedFreshOrdinaryExposure.collect, finished_prepend] at finished
              simp only [Nat.succ_add, MergedFreshOrdinaryExposure.collect, ih state seen rest finished]
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [Nat.succ_add, MergedFreshOrdinaryExposure.collect, ite_eq_left visited] using ih state seen rest
                  (by simpa only [MergedFreshOrdinaryExposure.collect, ite_eq_left visited] using finished)
              · simpa only [Nat.succ_add, MergedFreshOrdinaryExposure.collect, ite_eq_right visited] using ih state (entry.identity :: seen) (members ++ rest)
                  (by simpa only [MergedFreshOrdinaryExposure.collect, ite_eq_right visited] using finished)
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [Nat.succ_add, MergedFreshOrdinaryExposure.collect, ite_eq_left visited] using ih state seen rest
                  (by simpa only [MergedFreshOrdinaryExposure.collect, ite_eq_left visited] using finished)
              · cases done : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
                | pending => simp only [MergedFreshOrdinaryExposure.collect, ite_eq_right visited, done, Finished] at finished
                | done result after =>
                    simpa only [Nat.succ_add, MergedFreshOrdinaryExposure.collect, ite_eq_right visited, done] using ih after (entry.identity :: seen) (result :: rest)
                      (by simpa only [MergedFreshOrdinaryExposure.collect, ite_eq_right visited, done] using finished)

/-- The complete source edge reader preserves its result and effects after sufficient proof fuel. -/
private theorem exposure_nodeEdges_stable (fuel extra : Nat)
    (value : Value Symbol Constraint) (state : InternedConstructorTemplates.State Symbol Constraint)
    (finished : MergedSourceExposure.Finished (MergedFreshOrdinaryExposure.nodeEdges fuel value state)) :
    MergedFreshOrdinaryExposure.nodeEdges (fuel + extra) value state = MergedFreshOrdinaryExposure.nodeEdges fuel value state := by
  have fallback (current : InternedConstructorTemplates.State Symbol Constraint) (root : Value Symbol Constraint)
      (complete : Finished (MergedFreshOrdinaryExposure.collect fuel current [] [root]).canonical) :
      (MergedFreshOrdinaryExposure.collect (fuel + extra) current [] [root]).canonical = (MergedFreshOrdinaryExposure.collect fuel current [] [root]).canonical :=
    congrArg MergedSourceExposure.Result.canonical (exposure_collect_stable fuel extra current [] [root] ((finished_canonical _).mp complete))
  cases value with
  | empty | reference | node => rfl
  | union => exact fallback state _ finished
  | mu entry body depth ordinary =>
      cases done : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
      | pending => simp only [MergedFreshOrdinaryExposure.nodeEdges, done]
      | done result after =>
          cases result <;> simp only [MergedFreshOrdinaryExposure.nodeEdges, done] at finished ⊢ <;>
            first | rfl | exact fallback after _ finished

omit [DecidableEq (EdgeKey Symbol Constraint)] in
private theorem observed_getValue_raw_moreFuel
    (fuel extra uv : Nat) (before after : EnumerationState.State Symbol Constraint)
    (value : UVarValue Symbol)
    (observed : Success (getValue fuel uv) before value after) :
    ExceptT.run (getValue (fuel + extra) uv before) =
      ExceptT.run (getValue fuel uv before) := by
  have retained := EnumerationExecution.getValue_moreFuel fuel extra uv before value after observed
  exact (EnumerationPartialExact.getValue_exact (fuel + extra) uv before after value retained).trans
    (EnumerationPartialExact.getValue_exact fuel uv before after value observed).symm

omit [DecidableEq (EdgeKey Symbol Constraint)] in
/-- A successful native recursion check retains its complete raw result. -/
private theorem observed_checkRepeated_raw_moreFuel
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel extra uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol Constraint) (repeated : Bool)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before repeated after) :
    ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated heap
      (fuel + extra) uv handle scs before) =
      ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs before) := by
  cases decoded : lookupNode heap handle with
  | none => simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded]
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, reading, _continued⟩ := (success_bind _ _ _ _ _).mp observed
        have retained := EnumerationExecution.representative_moreFuel fuel extra uv
          before root resolved reading
        have oldExact := EnumerationPartialExact.representative_success_exact
          fuel uv before resolved root reading
        have newExact := EnumerationPartialExact.representative_success_exact
          (fuel + extra) uv before resolved root retained
        simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte]
        rw [bind_single _ _ before resolved root newExact,
          bind_single _ _ before resolved root oldExact]
      · simp [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary]


private theorem observed_success_stages
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata updated : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller reached : Caller width) (before after : Cached) (queries receivedQueries : Queries)
    (checked observed callbackCore : Core) (result : Node)
    (nextHeap : InternedConstructorTemplates.State Symbol Constraint) (action : EnumerateM Symbol Constraint Unit)
    (prefixObserved : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata readFuel checkFuel nativeFuel
      representativeFuel indexFuel callbackFuel uv caller before queries =
      .narrowed checked (.done (result, some action) nextHeap) reached receivedQueries
        (some [.ok ((), observed)]) (some after) (some [.ok ((false, updated), callbackCore)]) none)
    :
    ∃ (oldHandle newHandle : Nat) (scs : List Suspended) (oldValue : Node) (readAfter : Core),
      ExceptT.run (getValue readFuel uv before.core) = [.ok (.unenumerated (some oldHandle) scs, readAfter)] ∧
      ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
        checkFuel uv oldHandle scs readAfter) = [.ok (false, checked)] ∧
      lookupNode caller.checked.native.machine.heap oldHandle = some oldValue ∧
      SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
        uv oldHandle scs oldValue caller.checked.native.machine.heap = .done (result, some action) nextHeap ∧
      encodeNode result = some newHandle ∧
      ExceptT.run (action checked) = [.ok ((), observed)] ∧
      SourcePruningEnumerationNarrowAdapter.adapt nextHeap indexFuel uv oldHandle newHandle scs before observed = some after ∧
      after.core = observed ∧ callbackCore = observed ∧ updated = metadata ∧
      reached = SourceCurrentAllocatedPartialState.advance caller
        (advancePhysical caller.checked ⟨nextHeap, caller.checked.operations⟩) caller.fourth caller.merge ∧
      receivedQueries = queries := by
  unfold SourcePruningEnumerationSelectedStep.runPrefix SourcePruningEnumerationSelectedStep.runPrefixWithNarrow at prefixObserved
  simp only [← SourcePruningEnumerationAction.prepare_configured_eq] at prefixObserved
  generalize readEq : ExceptT.run (getValue readFuel uv before.core) = read at prefixObserved
  cases read with
  | nil => cases prefixObserved
  | cons first rest =>
      cases rest with
      | cons _ _ =>
          cases first with
          | error _ => cases prefixObserved
          | ok pair =>
              obtain ⟨value, _readAfter⟩ := pair
              cases value with
              | eliminated | enumerated _ => cases prefixObserved
              | unenumerated handle _ => cases handle <;> cases prefixObserved
      | nil =>
          cases first with
          | error _ => cases prefixObserved
          | ok pair =>
              obtain ⟨value, readAfter⟩ := pair
              cases value with
              | eliminated | enumerated _ => cases prefixObserved
              | unenumerated handle scs =>
                  cases handle with
                  | none => cases prefixObserved
                  | some oldHandle =>
                      dsimp only at prefixObserved
                      generalize checkEq : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
                        caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter) = check at prefixObserved
                      cases check with
                      | nil => cases prefixObserved
                      | cons first rest =>
                          cases rest with
                          | cons _ _ =>
                              cases first with
                              | error _ => cases prefixObserved
                              | ok pair =>
                                  obtain ⟨repeated, _checked⟩ := pair
                                  cases repeated <;> cases prefixObserved
                          | nil =>
                              cases first with
                              | error _ => cases prefixObserved
                              | ok pair =>
                                  obtain ⟨repeated, actualChecked⟩ := pair
                                  cases repeated with
                                  | true => cases prefixObserved
                                  | false =>
                                      generalize decodedEq : lookupNode caller.checked.native.machine.heap oldHandle = decoded at prefixObserved
                                      cases decoded with
                                      | none => cases prefixObserved
                                      | some oldValue =>
                                          dsimp only at prefixObserved
                                          generalize preparedEq : SourcePruningEnumerationAction.prepare holeKey fits admits metadata
                                            nativeFuel representativeFuel uv oldHandle scs oldValue
                                            caller.checked.native.machine.heap = prepared at prefixObserved
                                          cases prepared with
                                          | failed _ _ => cases prefixObserved
                                          | done pair nativeAfter =>
                                              obtain ⟨nativeResult, possibleAction⟩ := pair
                                              cases possibleAction with
                                              | none => cases prefixObserved
                                              | some actualAction =>
                                                  dsimp only at prefixObserved
                                                  generalize actionEq : ExceptT.run (actualAction actualChecked) = raw at prefixObserved
                                                  cases raw with
                                                  | nil => cases prefixObserved
                                                  | cons first rest =>
                                                      cases rest with
                                                      | cons _ _ =>
                                                          cases first with
                                                          | error _ => cases prefixObserved
                                                          | ok pair =>
                                                              obtain ⟨token, _observed⟩ := pair
                                                              cases token
                                                              cases prefixObserved
                                                      | nil =>
                                                          cases first with
                                                          | error _ => cases prefixObserved
                                                          | ok pair =>
                                                              obtain ⟨token, actualObserved⟩ := pair
                                                              cases token
                                                              dsimp only at prefixObserved
                                                              generalize encodedEq : encodeNode nativeResult = encoded at prefixObserved
                                                              cases encoded with
                                                              | none => cases prefixObserved
                                                              | some newHandle =>
                                                                  dsimp only at prefixObserved
                                                                  generalize adaptedEq : SourcePruningEnumerationNarrowAdapter.adapt nativeAfter
                                                                    indexFuel uv oldHandle newHandle scs before actualObserved = adapted at prefixObserved
                                                                  cases adapted with
                                                                  | none => cases prefixObserved
                                                                  | some attached =>
                                                                      rw [SourcePruningRecordTypes.recordTypes_inr] at prefixObserved
                                                                      have same := SourcePruningEnumerationSelectedStep.Result.narrowed.inj prefixObserved
                                                                      have checkedSame := same.1
                                                                      have preparedSame := MergedSourceComparison.Result.done.inj same.2.1
                                                                      have resultSame : nativeResult = result := congrArg Prod.fst preparedSame.1
                                                                      have actionSame := Option.some.inj (congrArg Prod.snd preparedSame.1)
                                                                      have heapSame := preparedSame.2
                                                                      have observedSame : actualObserved = observed := congrArg Prod.snd
                                                                        (Except.ok.inj (List.cons.inj (Option.some.inj same.2.2.2.2.1)).1)
                                                                      have attachedSame := Option.some.inj same.2.2.2.2.2.1
                                                                      have rightSame := Except.ok.inj
                                                                        (List.cons.inj (Option.some.inj same.2.2.2.2.2.2.1)).1
                                                                      have callbackSame : attached.core = callbackCore := congrArg Prod.snd rightSame
                                                                      have updatedSame : metadata = updated := congrArg Prod.snd (congrArg Prod.fst rightSame)
                                                                      subst actualChecked
                                                                      subst nativeResult
                                                                      subst actualAction
                                                                      subst nativeAfter
                                                                      subst actualObserved
                                                                      have attachedEq : attached = after := attachedSame
                                                                      subst attached
                                                                      have core := SourcePruningEnumerationNarrowAdapter.adapt_core nextHeap indexFuel
                                                                        uv oldHandle newHandle scs before after observed adaptedEq
                                                                      exact ⟨oldHandle, newHandle, scs, oldValue, readAfter, rfl, checkEq,
                                                                        decodedEq, preparedEq, encodedEq, actionEq, adaptedEq, core,
                                                                        callbackSame.symm.trans core, updatedSame.symm, same.2.2.1.symm, same.2.2.2.1.symm⟩

private theorem narrow_done_moreFuel
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel extra uv : Nat) (oldValue value : Node)
    (before after : InternedConstructorTemplates.State Symbol Constraint)
    (actual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv oldValue before =
      .done value after) :
    SourcePruningOuterNarrow.narrow holeKey fits admits metadata (fuel + extra) uv oldValue before =
      .done value after := by
  have fallback (input : Node)
      (observed : SourcePruningNativeView.narrowAt fits admits fuel
        (holeKey metadata.typing uv) input before = .done value after) :
      SourcePruningNativeView.narrowAt fits admits (fuel + extra)
        (holeKey metadata.typing uv) input before = .done value after := by
    unfold SourcePruningNativeView.narrowAt at observed ⊢
    cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel input before with
    | unresolved | pending | exhausted =>
        simp only [exposed] at observed
        cases observed
    | done rows middle =>
        have stable := exposure_nodeEdges_stable fuel extra input before (by rw [exposed]; trivial)
        rw [stable, exposed]
        simpa only [exposed] using observed
  cases oldValue with
  | mu entry body depth ordinary => simpa only [SourcePruningOuterNarrow.narrow] using actual
  | empty | reference | node | union =>
      by_cases typed : metadata.types.contains uv = true
      · simpa only [SourcePruningOuterNarrow.narrow, typed, ↓reduceIte] using actual
      · simp only [SourcePruningOuterNarrow.narrow] at actual ⊢
        rw [ite_eq_right typed] at actual ⊢
        exact fallback _ actual

omit [DecidableEq (EdgeKey Symbol Constraint)] in
private theorem adapted_some_moreFuel
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel extra uv oldHandle newHandle : Nat) (scs : List Suspended)
    (before after : Cached) (observed : Core)
    (actual : SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle
      scs before observed = some after) :
    SourcePruningEnumerationNarrowAdapter.adapt heap (fuel + extra) uv oldHandle newHandle
      scs before observed = some after := by
  unfold SourcePruningEnumerationNarrowAdapter.adapt at actual ⊢
  by_cases same : newHandle = oldHandle
  · simpa only [ite_eq_left same] using actual
  · rw [ite_eq_right same] at actual ⊢
    rw [Option.map_eq_some_iff] at actual ⊢
    obtain ⟨saved, written, mapped⟩ := actual
    exact ⟨saved, SourcePruningEnumerationNativeIndex.write_some_moreFuel heap fuel extra uv
      (.unenumerated (some newHandle) scs) scs scs
      (EnumerationExpandableIndex.frame observed before) saved written, mapped⟩

private theorem prepared_done_narrowed
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel representativeFuel uv oldHandle : Nat)
    (scs : List Suspended) (oldValue value : Node)
    (before after : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel representativeFuel
      uv oldHandle scs oldValue before = .done (value, some action) after) :
    SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv oldValue before =
      .done value after := by
  unfold SourcePruningEnumerationAction.prepare SourcePruningEnumerationAction.prepareWithNarrow at prepared
  cases narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv oldValue before with
  | failed =>
      simp only [narrowed] at prepared
      cases prepared
  | done actualValue actualHeap =>
      rw [narrowed] at prepared
      have parts := MergedSourceComparison.Result.done.inj prepared
      have sameValue : actualValue = value := congrArg Prod.fst parts.1
      cases sameValue
      cases parts.2
      rfl

private theorem prepared_success_nonempty
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel representativeFuel uv oldHandle : Nat)
    (scs : List Suspended) (oldValue value : Node)
    (before after : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit) (checked observed : Core)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel representativeFuel
      uv oldHandle scs oldValue before = .done (value, some action) after)
    (raw : ExceptT.run (action checked) = [.ok ((), observed)]) : value ≠ .empty := by
  intro sameValue
  have narrowed := prepared_done_narrowed holeKey fits admits metadata fuel representativeFuel
    uv oldHandle scs oldValue value before after action prepared
  have rejected : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel representativeFuel
      uv oldHandle scs oldValue before =
      .done (value, some (reject : EnumerateM Symbol Constraint Unit)) after := by
    simp only [SourcePruningEnumerationAction.prepare, SourcePruningEnumerationAction.prepareWithNarrow,
      narrowed, sameValue]
  have sameAction : action = (reject : EnumerateM Symbol Constraint Unit) :=
    Option.some.inj (congrArg Prod.snd (MergedSourceComparison.Result.done.inj
      (prepared.symm.trans rejected)).1)
  rw [sameAction] at raw
  simp only [reject, ExceptT.run] at raw
  cases raw

private theorem real_success_moreFuel
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata updated : Metadata Typing) (fuel extra uv : Nat)
    (caller reached : Caller width) (before after : Cached) (queries received : Queries)
    (checked actionCore callbackCore : Core) (value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (action : EnumerateM Symbol Constraint Unit)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      fuel fuel fuel fuel fuel fuel uv caller before queries =
      .narrowed checked (.done (value, some action) heap) reached received
        (some [.ok ((), actionCore)]) (some after) (some [.ok ((false, updated), callbackCore)]) none) :
    ∃ nextAction : EnumerateM Symbol Constraint Unit,
      SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv caller before queries =
      .narrowed checked (.done (value, some nextAction) heap) reached received
        (some [.ok ((), actionCore)]) (some after) (some [.ok ((false, updated), callbackCore)]) none := by
  obtain ⟨oldHandle, newHandle, scs, oldValue, readAfter, reading, checking, decoded,
      prepared, encoded, raw, adapted, core, callback, metadataSame, callerSame, querySame⟩ :=
    observed_success_stages holeKey fits admits graph templates stop order metadata updated
      fuel fuel fuel fuel fuel fuel uv caller reached before after queries received
      checked actionCore callbackCore value heap action actual
  have readObserved : Success (getValue fuel uv) before.core (.unenumerated (some oldHandle) scs) readAfter := by
    rw [Success, reading]
    exact List.mem_singleton_self _
  have laterReading := (observed_getValue_raw_moreFuel fuel extra uv before.core readAfter
    (.unenumerated (some oldHandle) scs) readObserved).trans reading
  have checkObserved : Success (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      fuel uv oldHandle scs) readAfter false checked := by
    rw [Success, checking]
    exact List.mem_singleton_self _
  have laterChecking := (observed_checkRepeated_raw_moreFuel caller.checked.native.machine.heap fuel extra
    uv oldHandle scs readAfter checked false checkObserved).trans checking
  have narrowed := prepared_done_narrowed holeKey fits admits metadata fuel fuel uv oldHandle scs
    oldValue value caller.checked.native.machine.heap heap action prepared
  have stable (additional : Nat) := narrow_done_moreFuel holeKey fits admits metadata fuel additional uv
    oldValue value caller.checked.native.machine.heap heap narrowed
  have nonempty := prepared_success_nonempty holeKey fits admits metadata fuel fuel uv oldHandle scs
    oldValue value caller.checked.native.machine.heap heap action checked actionCore prepared raw
  have observed : Success action checked () actionCore := by
    rw [Success, raw]
    exact List.mem_singleton_self _
  obtain ⟨nextAction, laterPrepared, laterRaw⟩ := SourcePruningEnumerationPreparedFuel.nonempty_moreFuel
    holeKey fits admits metadata fuel fuel uv oldHandle newHandle scs oldValue value
    caller.checked.native.machine.heap heap action checked actionCore narrowed stable nonempty encoded
    prepared observed extra extra
  have laterAdapted := adapted_some_moreFuel heap fuel extra uv oldHandle newHandle scs before after actionCore adapted
  have rightRaw : ExceptT.run ((pure (false, metadata) : EnumerateM Symbol Constraint (Bool × Metadata Typing))
      actionCore) = [.ok ((false, metadata), actionCore)] := rfl
  have afterFrame : EnumerationExpandableIndex.frame actionCore after = after := by
    rw [← core]
    rfl
  refine ⟨nextAction, ?_⟩
  rw [callerSame, querySame, metadataSame, callback]
  simp only [SourcePruningEnumerationSelectedStep.runPrefix, SourcePruningEnumerationSelectedStep.runPrefixWithNarrow,
    laterReading, laterChecking, decoded, ← SourcePruningEnumerationAction.prepare_configured_eq,
    laterPrepared, laterRaw, encoded, laterAdapted, SourcePruningRecordTypes.recordTypes_inr, core,
    rightRaw, MergedSourceComparison.Result.state, afterFrame]

/-- An actual successful real prefix retains its original caller and native resource bounds. -/
theorem prefix_real_narrowed_resources_at_original_budget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata updated : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller reached : Caller width) (memos : Memos) (before after : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap)
    (workFuel selected : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected))
    (checked actionCore callbackCore : Core) (value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit) (received : Queries)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel selected caller before memos.query =
      .narrowed checked (.done (value, some action) heap) reached received
        (some [.ok ((), actionCore)]) (some after) (some [.ok ((false, updated), callbackCore)]) none) :
    CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos profile property
      (.narrowed checked (.done (value, some action) heap) reached received
        (some [.ok ((), actionCore)]) (some after) (some [.ok ((false, updated), callbackCore)]) none)
 := by
  classical
  obtain ⟨bound, sufficient⟩ := prefix_complete_resources holeKey fits admits graph templates checkEmpty edgesOf
    stop order metadata formulas solver inventory caller memos before packet profile property bounded known
  obtain ⟨nextAction, replay⟩ := real_success_moreFuel holeKey fits admits graph templates stop order
    metadata updated workFuel bound selected caller reached before after memos.query received
    checked actionCore callbackCore value heap action actual
  have large := sufficient workFuel selected chosen
  have largeAt : CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos
      profile property (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
        metadata (workFuel + bound) (workFuel + bound) (workFuel + bound) (workFuel + bound)
          (workFuel + bound) (workFuel + bound) selected caller before memos.query) := by
    simpa only [Nat.add_comm bound workFuel] using large
  rw [replay] at largeAt
  obtain ⟨facts, resources⟩ := largeAt
  obtain ⟨ordinaryNone, query, witnessValue, witnessHeap, witnessAction, final,
      prepared, advanced, post, saved, shape⟩ := facts
  have parts := MergedSourceComparison.Result.done.inj prepared
  have valueSame : value = witnessValue := congrArg Prod.fst parts.1
  have heapSame : heap = witnessHeap := parts.2
  subst witnessValue
  subst witnessHeap
  exact ⟨⟨ordinaryNone, query, value, heap, action, final, rfl, advanced, post, saved, shape⟩, resources⟩

end MicroCFTA.SourcePruningEnumerationSharedRecursive
