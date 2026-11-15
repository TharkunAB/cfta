import MicroCFTA.SourcePruningEnumerationObservedRealPrefixResources
import MicroCFTA.SourcePruningEnumerationNativeIndexStability
import MicroCFTA.MergedFreshOrdinaryColdReplay
import MicroCFTA.EnumerationExecution
import MicroCFTA.EnumerationPartialExact

set_option autoImplicit false
namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open InternedProbeProvenance SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Prepared" => MergedSourceComparison.Result Symbol Constraint
  (Node × Option (EnumerateM Symbol Constraint Unit))
attribute [local instance] SourcePruningEnumerationAction.actionMonadList
variable {Typing Key : Type} {width : Nat}
private theorem continuing_getValue_raw_moreFuel
    (fuel extra uv : Nat) (before after : Core)
    (value : UVarValue Symbol)
    (observed : Success (getValue fuel uv) before value after) :
    ExceptT.run (getValue (fuel + extra) uv before) =
      ExceptT.run (getValue fuel uv before) := by
  have retained := EnumerationExecution.getValue_moreFuel fuel extra uv before value after observed
  exact (EnumerationPartialExact.getValue_exact (fuel + extra) uv before after value retained).trans
    (EnumerationPartialExact.getValue_exact fuel uv before after value observed).symm

/-- A successful native recursion check retains its complete raw result. -/
private theorem continuing_checkRepeated_raw_moreFuel
    (heap : Heap)
    (fuel extra uv handle : Nat) (scs : List Suspended)
    (before after : Core) (repeated : Bool)
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

/-- A successful indexed parked adapter retains its exact cached endpoint. -/
private theorem continuing_parked_adapt_moreFuel
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel extra uv handle : Nat) (scs : List Suspended)
    (before after : Cached)
    (checked : EnumerationState.State Symbol Constraint)
    (observed : SourcePruningEnumerationParkedRestart.adapt heap fuel uv handle scs
      before checked = some after) :
    SourcePruningEnumerationParkedRestart.adapt heap (fuel + extra) uv handle scs
      before checked = some after := by
  unfold SourcePruningEnumerationParkedRestart.adapt at observed ⊢
  rw [Option.map_eq_some_iff] at observed ⊢
  obtain ⟨saved, written, mapped⟩ := observed
  exact ⟨saved, SourcePruningEnumerationNativeIndex.write_some_moreFuel heap fuel extra uv
    (.unenumerated (some handle) []) [] scs
    (EnumerationExpandableIndex.frame checked before) saved written, mapped⟩


variable [DecidableEq (EdgeKey Symbol Constraint)]
private theorem continuing_narrow_moreFuel
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel extra uv : Nat) (oldValue value : Node)
    (before after : Heap)
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
        have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable fuel extra input before
          (by rw [exposed]; trivial)
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
private theorem continuing_write_single
    (fuel uv newHandle : Nat) (scs : List Suspended) (checked : Core) :
    ∃ row : Except EnumerationState.Error (Unit × Core),
      ExceptT.run ((representative fuel uv >>= fun selected =>
        setValue selected (.unenumerated (some newHandle) scs)) checked) = [row] := by
  cases found : UnionFind.findRoot fuel checked.representatives uv with
  | none =>
      simp [representative, found, setValue, EnumerationState.failure, bind, get, getThe,
        MonadStateOf.get, set, pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.bind, StateT.get,
        StateT.modifyGet, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run]
  | some result =>
      simp [representative, found, setValue, bind, get, getThe, MonadStateOf.get, set, pure,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.bind, StateT.get, StateT.set, StateT.pure, StateT.modifyGet,
        ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run]

private theorem continuing_parked_empty_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap)
    (workFuel selected : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected)) :
    let observed := SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel selected caller before memos.query
    match observed with
    | .parked _ (some _) _ =>
        CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos profile property observed
    | .narrowed _ _ _ _ (some []) _ _ _ =>
        CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos profile property observed
    | _ => True := by
  classical
  obtain ⟨bound, sufficient⟩ := prefix_complete_resources holeKey fits admits graph templates false (fun _ => [])
    stop order metadata formulas solver inventory caller memos before packet profile property bounded known
  have current_at (result : SourcePruningEnumerationSelectedStep.Result width Typing)
      (later : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        (workFuel + bound) (workFuel + bound) (workFuel + bound) (workFuel + bound)
        (workFuel + bound) (workFuel + bound) selected caller before memos.query = result) :
      CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos profile property result := by
    have resources := sufficient workFuel selected chosen
    have atBound : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        (bound + workFuel) (bound + workFuel) (bound + workFuel) (bound + workFuel)
        (bound + workFuel) (bound + workFuel) selected caller before memos.query = result := by
      simpa only [Nat.add_comm bound workFuel] using later
    rw [atBound] at resources
    exact resources
  dsimp only
  by_cases readable : ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
      ExceptT.run (getValue workFuel selected before.core) = [.ok (.unenumerated (some oldHandle) scs, readAfter)]
  · obtain ⟨oldHandle, scs, readAfter, reading⟩ := readable
    have readObserved : Success (getValue workFuel selected) before.core
        (.unenumerated (some oldHandle) scs) readAfter := by
      rw [Success, reading]
      exact List.mem_singleton_self _
    have laterReading := (continuing_getValue_raw_moreFuel workFuel bound selected before.core readAfter
      (.unenumerated (some oldHandle) scs) readObserved).trans reading
    by_cases repeated : ∃ checked : Core,
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          workFuel selected oldHandle scs readAfter) = [.ok (true, checked)]
    · obtain ⟨checked, checking⟩ := repeated
      have observed : Success (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          workFuel selected oldHandle scs) readAfter true checked := by
        rw [Success, checking]
        exact List.mem_singleton_self _
      have laterChecking := (continuing_checkRepeated_raw_moreFuel caller.checked.native.machine.heap
        workFuel bound selected oldHandle scs readAfter checked true observed).trans checking
      cases adapted : SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
          workFuel selected oldHandle scs before checked with
      | none =>
          simp only [SourcePruningEnumerationSelectedStep.runPrefix,
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, reading, checking, adapted, Option.map_none]
      | some parked =>
          have laterAdapted := continuing_parked_adapt_moreFuel caller.checked.native.machine.heap
            workFuel bound selected oldHandle scs before parked checked adapted
          have laterResult : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
              stop order metadata (workFuel + bound) (workFuel + bound) (workFuel + bound) (workFuel + bound)
              (workFuel + bound) (workFuel + bound) selected caller before memos.query =
              .parked checked (some parked)
                (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked))) := by
            simp only [SourcePruningEnumerationSelectedStep.runPrefix,
              SourcePruningEnumerationSelectedStep.runPrefixWithNarrow,
              laterReading, laterChecking, laterAdapted, Option.map_some]
          have resources := current_at _ laterResult
          simpa only [SourcePruningEnumerationSelectedStep.runPrefix,
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, reading, checking, adapted, Option.map_some]
            using resources
    · by_cases fresh : ∃ checked : Core,
          ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
            workFuel selected oldHandle scs readAfter) = [.ok (false, checked)]
      · obtain ⟨checked, checking⟩ := fresh
        cases decoded : lookupNode caller.checked.native.machine.heap oldHandle with
        | none =>
            simp only [SourcePruningEnumerationSelectedStep.runPrefix,
              SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, reading, checking, decoded]
        | some oldValue =>
            cases narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata workFuel selected
                oldValue caller.checked.native.machine.heap with
            | failed fault heap =>
                simp only [SourcePruningEnumerationSelectedStep.runPrefix,
                  SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, reading, checking, decoded,
                  SourcePruningEnumerationAction.prepareWithNarrow, narrowed]
            | done value heap =>
                by_cases empty : value = .empty
                · subst value
                  have oldPrepared : SourcePruningEnumerationAction.prepare (EnumGuard := Constraint)
                      holeKey fits admits metadata workFuel workFuel selected oldHandle scs oldValue
                      caller.checked.native.machine.heap = .done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap := by
                    simp only [SourcePruningEnumerationAction.prepare, SourcePruningEnumerationAction.prepareWithNarrow, narrowed]
                  have checkObserved : Success (SourcePruningEnumerationRecursion.checkRepeated
                      caller.checked.native.machine.heap workFuel selected oldHandle scs) readAfter false checked := by
                    rw [Success, checking]
                    exact List.mem_singleton_self _
                  have laterChecking := (continuing_checkRepeated_raw_moreFuel caller.checked.native.machine.heap
                    workFuel bound selected oldHandle scs readAfter checked false checkObserved).trans checking
                  have laterNarrowed := continuing_narrow_moreFuel holeKey fits admits metadata workFuel bound
                    selected oldValue .empty caller.checked.native.machine.heap heap narrowed
                  have laterPrepared : SourcePruningEnumerationAction.prepare (EnumGuard := Constraint)
                      holeKey fits admits metadata (workFuel + bound) (workFuel + bound) selected oldHandle scs oldValue
                      caller.checked.native.machine.heap = .done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap := by
                    simp only [SourcePruningEnumerationAction.prepare, SourcePruningEnumerationAction.prepareWithNarrow, laterNarrowed]
                  have laterResult : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
                      stop order metadata (workFuel + bound) (workFuel + bound) (workFuel + bound) (workFuel + bound)
                      (workFuel + bound) (workFuel + bound) selected caller before memos.query =
                      .narrowed checked (.done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap)
                        (SourceCurrentAllocatedPartialState.advance caller
                          (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
                        memos.query (some []) none none none := by
                    unfold SourcePruningEnumerationSelectedStep.runPrefix SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
                    rw [laterReading]
                    dsimp only
                    rw [laterChecking]
                    dsimp only
                    rw [decoded]
                    dsimp only
                    rw [← SourcePruningEnumerationAction.prepare_configured_eq, laterPrepared]
                    rfl
                  have oldResult : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
                      stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel
                      selected caller before memos.query =
                      .narrowed checked (.done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap)
                        (SourceCurrentAllocatedPartialState.advance caller
                          (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
                        memos.query (some []) none none none := by
                    unfold SourcePruningEnumerationSelectedStep.runPrefix SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
                    rw [reading]
                    dsimp only
                    rw [checking]
                    dsimp only
                    rw [decoded]
                    dsimp only
                    rw [← SourcePruningEnumerationAction.prepare_configured_eq, oldPrepared]
                    rfl
                  have resources := current_at _ laterResult
                  rw [oldResult]
                  exact resources
                · cases encoded : encodeNode value with
                  | none =>
                      have oldPrepared : SourcePruningEnumerationAction.prepare (EnumGuard := Constraint)
                          holeKey fits admits metadata workFuel workFuel selected oldHandle scs oldValue
                          caller.checked.native.machine.heap = .done (value, none) heap := by
                        unfold SourcePruningEnumerationAction.prepare SourcePruningEnumerationAction.prepareWithNarrow
                        rw [narrowed]
                        cases value <;> simp_all only [encodeNode, not_true_eq_false]
                      simp only [SourcePruningEnumerationSelectedStep.runPrefix,
                        SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, reading, checking, decoded,
                        ← SourcePruningEnumerationAction.prepare_configured_eq, oldPrepared]
                  | some newHandle =>
                      let action : EnumerateM Symbol Constraint Unit :=
                        if newHandle = oldHandle then pure () else
                          representative workFuel selected >>= fun selected =>
                            setValue selected (.unenumerated (some newHandle) scs)
                      have oldPrepared : SourcePruningEnumerationAction.prepare (EnumGuard := Constraint)
                          holeKey fits admits metadata workFuel workFuel selected oldHandle scs oldValue
                          caller.checked.native.machine.heap = .done (value, some action) heap :=
                        SourcePruningEnumerationSelectedStep.prepared_action holeKey fits admits metadata
                          workFuel workFuel selected oldHandle newHandle scs oldValue value
                          caller.checked.native.machine.heap heap narrowed empty encoded
                      have single : ∃ row : Except EnumerationState.Error (Unit × Core),
                          ExceptT.run (action checked) = [row] := by
                        dsimp only [action]
                        by_cases same : newHandle = oldHandle
                        · rw [ite_eq_left same]
                          exact ⟨.ok ((), checked), rfl⟩
                        · rw [ite_eq_right same]
                          exact continuing_write_single workFuel selected newHandle scs checked
                      obtain ⟨row, raw⟩ := single
                      simp only [SourcePruningEnumerationSelectedStep.runPrefix,
                        SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, reading, checking, decoded,
                        ← SourcePruningEnumerationAction.prepare_configured_eq, oldPrepared,
                        MergedSourceComparison.Result.state, raw]
                      cases row with
                      | error error => trivial
                      | ok pair =>
                          obtain ⟨token, actionCore⟩ := pair
                          cases token
                          rw [encoded]
                          cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap workFuel selected
                              oldHandle newHandle scs before actionCore with
                          | none => simp only [adapted]
                          | some after =>
                              simp only [adapted, SourcePruningRecordTypes.recordTypes_inr]
                              trivial
      · have stopped : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
            stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel selected caller before memos.query =
            .stopped (ExceptT.run (getValue workFuel selected before.core))
              (some (ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
                workFuel selected oldHandle scs readAfter))) := by
          unfold SourcePruningEnumerationSelectedStep.runPrefix SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
          rw [reading]
          dsimp only
          split
          · exact (repeated ⟨_, by assumption⟩).elim
          · exact (fresh ⟨_, by assumption⟩).elim
          · rfl
        rw [stopped]
        trivial
  · have stopped : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
        stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel selected caller before memos.query =
        .stopped (ExceptT.run (getValue workFuel selected before.core)) none := by
      unfold SourcePruningEnumerationSelectedStep.runPrefix SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      dsimp only
      split
      · exact (readable ⟨_, _, _, by assumption⟩).elim
      · rfl
    rw [stopped]
    trivial

private theorem continuing_right_receipt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata updated : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller reached : Caller width) (before : Cached) (queries receivedQueries : Queries)
    (checked callbackCore : Core) (prepared : Prepared)
    (action : Option (List (Except EnumerationState.Error (Unit × Core))))
    (candidate : Option Cached) (rejected : Bool)
    (prefixObserved : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries =
      .narrowed checked prepared reached receivedQueries action candidate
        (some [.ok ((rejected, updated), callbackCore)]) none) :
    rejected = false ∧ ∃ (value : Node) (heap : Heap)
      (selectedAction : EnumerateM Symbol Constraint Unit) (actionCore : Core) (after : Cached),
      prepared = .done (value, some selectedAction) heap ∧
      action = some [.ok ((), actionCore)] ∧ candidate = some after := by
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
                                                                      have right := Except.ok.inj
                                                                        (List.cons.inj (Option.some.inj same.2.2.2.2.2.2.1)).1
                                                                      have rejectSame : false = rejected := congrArg Prod.fst (congrArg Prod.fst right)
                                                                      exact ⟨rejectSame.symm, nativeResult, nativeAfter, actualAction, actualObserved,
                                                                        EnumerationExpandableIndex.frame attached.core attached,
                                                                        same.2.1.symm, same.2.2.2.2.1.symm, same.2.2.2.2.2.1.symm⟩

private theorem continuing_right_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap)
    (workFuel selected : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected))
    (checked callbackCore : Core) (prepared : Prepared) (reached : Caller width) (received : Queries)
    (action : Option (List (Except EnumerationState.Error (Unit × Core)))) (candidate : Option Cached)
    (rejected : Bool) (updated : Metadata Typing)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel selected caller before memos.query =
      .narrowed checked prepared reached received action candidate (some [.ok ((rejected, updated), callbackCore)]) none) :
    rejected = false ∧ ∃ after : Cached, candidate = some after ∧
      CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos profile property
        (.narrowed checked prepared reached received action candidate (some [.ok ((rejected, updated), callbackCore)]) none) := by
  obtain ⟨same, value, heap, selectedAction, actionCore, after, preparedSame, actionSame, candidateSame⟩ :=
    continuing_right_receipt holeKey fits admits graph templates stop order metadata updated
      workFuel workFuel workFuel workFuel workFuel workFuel selected caller reached before memos.query received
      checked callbackCore prepared action candidate rejected actual
  refine ⟨same, after, candidateSame, ?_⟩
  rw [preparedSame, actionSame, candidateSame, same] at actual ⊢
  exact prefix_real_narrowed_resources_at_original_budget holeKey fits admits graph templates false (fun _ => [])
    stop order metadata updated formulas solver inventory caller reached memos before after packet profile property
    bounded known workFuel selected chosen checked actionCore callbackCore value heap selectedAction received actual

/-- Every actual real prefix endpoint fits the original native resource forecast. -/
theorem prefix_real_continuing_current_at_original_budget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap)
    (workFuel selected : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected)) :
    let observed := SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel selected caller before memos.query
    match observed with
    | .parked _ (some _) (some []) =>
        CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos profile property observed
    | .parked _ (some _) (some [.ok ((_updated, _next), _core)]) =>
        CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos profile property observed
    | .narrowed _ _ _ _ (some []) _ _ _ =>
        CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos profile property observed
    | .narrowed _ _ _ _ _ _ (some [.ok ((true, _updated), _core)]) _ => False
    | .narrowed _ _ _ _ _ (some _) (some [.ok ((false, _updated), _core)]) none =>
        CurrentPrefixResources stop order metadata formulas solver inventory selected caller before memos profile property observed
    | _ => True
 := by
  have supported := continuing_parked_empty_resources holeKey fits admits graph templates stop order metadata
    formulas solver inventory caller memos before packet profile property bounded known workFuel selected chosen
  dsimp only at supported ⊢
  generalize observedEq : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
    stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel selected caller before memos.query = observed
    at supported ⊢
  cases observed with
  | stopped reading checking => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after =>
          cases raw with
          | none => trivial
          | some rows =>
              cases rows with
              | nil => exact supported
              | cons first rest =>
                  cases rest with
                  | cons second tail => cases first <;> trivial
                  | nil =>
                      cases first with
                      | error error => trivial
                      | ok pair =>
                          obtain ⟨⟨updated, next⟩, core⟩ := pair
                          exact supported
  | narrowed checked prepared reached received action candidate right ordinary =>
      have noOrdinary := SourcePruningEnumerationSelectedStep.prefix_no_ordinary holeKey fits admits
        graph templates stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel
        selected caller before memos.query
      rw [observedEq] at noOrdinary
      subst ordinary
      cases action with
      | none =>
          cases right with
          | none => trivial
          | some rows =>
              cases rows with
              | nil => trivial
              | cons first rest =>
                  cases rest with
                  | cons second tail =>
                      cases first with
                      | error error => trivial
                      | ok pair =>
                          obtain ⟨⟨rejected, _updated⟩, _core⟩ := pair
                          cases rejected <;> trivial
                  | nil =>
                      cases first with
                      | error error => trivial
                      | ok pair =>
                          obtain ⟨⟨rejected, updated⟩, callbackCore⟩ := pair
                          have current := continuing_right_resources holeKey fits admits graph templates stop order metadata
                            formulas solver inventory caller memos before packet profile property bounded known workFuel selected chosen
                            checked callbackCore prepared reached received _ candidate rejected updated observedEq
                          cases rejected with
                          | true => cases current.1
                          | false =>
                              obtain ⟨_same, after, candidateSame, resources⟩ := current
                              cases candidate with
                              | none => cases candidateSame
                              | some attached => exact resources
      | some rows =>
          cases rows with
          | nil => exact supported
          | cons first rest =>
              cases right with
              | none => trivial
              | some rows =>
                  cases rows with
                  | nil => trivial
                  | cons first rest =>
                      cases rest with
                      | cons second tail =>
                          cases first with
                          | error error => trivial
                          | ok pair =>
                              obtain ⟨⟨rejected, _updated⟩, _core⟩ := pair
                              cases rejected <;> trivial
                      | nil =>
                          cases first with
                          | error error => trivial
                          | ok pair =>
                              obtain ⟨⟨rejected, updated⟩, callbackCore⟩ := pair
                              have current := continuing_right_resources holeKey fits admits graph templates stop order metadata
                                formulas solver inventory caller memos before packet profile property bounded known workFuel selected chosen
                                checked callbackCore prepared reached received _ candidate rejected updated observedEq
                              cases rejected with
                              | true => cases current.1
                              | false =>
                                  obtain ⟨_same, after, candidateSame, resources⟩ := current
                                  cases candidate with
                                  | none => cases candidateSame
                                  | some attached => exact resources

end MicroCFTA.SourcePruningEnumerationSharedRecursive
