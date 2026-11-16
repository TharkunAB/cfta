import MicroCFTA.SourcePruningEnumerationPrefixIsolatedAtOriginalBudget
import MicroCFTA.SourcePruningEnumerationOpaqueSuffixIsolation

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame EnumerationDependencies
open InternedConstructorTemplates EnumerationDischargeHistory EnumerationDriver
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
attribute [local instance] SourcePruningEnumerationRecursion.recursionMonadList

private theorem frame_expanded_roots
    {Guard : Type} (before after : EnumerationState.State Symbol Guard)
    (roots : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol), before.values[slot]? = some (.enumerated fragment) →
      IsRoot before.representatives slot)
    (frame : Frame before after) :
    ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol), after.values[slot]? = some (.enumerated fragment) →
      IsRoot after.representatives slot := by
  intro slot fragment stored
  have original : before.values[slot]? = some (.enumerated fragment) := by
    simpa only [frame.values] using stored
  obtain ⟨size, path⟩ := roots slot fragment original
  exact ⟨size, (frame.reaches slot slot size).mpr path⟩

private theorem frame_history
    {Guard : Type} (held heldHandle : Nat) (before after : EnumerationState.State Symbol Guard)
    (isolated : IsolatedPending held heldHandle before)
    (roots : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol), before.values[slot]? = some (.enumerated fragment) →
      IsRoot before.representatives slot)
    (frame : Frame before after) : HeldFragmentHistory held heldHandle before after := by
  have protects : ∀ slot, IsRoot before.representatives slot → Protected slot before after := by
    intro slot root
    refine ⟨congrArg (fun values => values[slot]?) frame.values, ?_, ?_⟩
    · obtain ⟨size, path⟩ := root
      exact ⟨size, (frame.reaches slot slot size).mpr path⟩
    · intro other
      exact SourcePruningEnumerationNativeLanguage.frame_sameClass before after frame slot other
  refine ⟨isolated.through_frame frame, protects held isolated.root, ?_, ?_⟩
  · intro slot fragment stored
    exact protects slot (roots slot fragment stored)
  · intro slot fragment stored
    exact Or.inl (by simpa only [frame.values] using stored)

private theorem pending_write_history
    {Guard : Type} (held heldHandle uv : Nat) (oldNode newNode : Option Nat)
    (oldScs newScs : List Suspended) (before after : EnumerationState.State Symbol Guard)
    (isolated : IsolatedPending held heldHandle before)
    (roots : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol), before.values[slot]? = some (.enumerated fragment) →
      IsRoot before.representatives slot)
    (different : uv ≠ held)
    (stored : before.values[uv]? = some (.unenumerated oldNode oldScs))
    (bucketShape : newScs = [] ∨ newScs = oldScs)
    (written : Success (setValue uv (.unenumerated newNode newScs)) before () after) :
    HeldFragmentHistory held heldHandle before after := by
  have reached : IsolatedPending held heldHandle after := by
    rcases bucketShape with empty | same
    · apply isolated.through_clear held heldHandle uv newNode before after different
      simpa only [empty] using written
    · apply isolated.through_handle_write held heldHandle uv oldNode newNode oldScs
        before after different stored
      simpa only [same] using written
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  have inside : uv < before.values.length := (List.getElem?_eq_some_iff.mp stored).1
  subst after
  refine ⟨reached, ⟨?_, reached.root, fun _ => Iff.rfl⟩, ?_, ?_⟩
  · simp only [List.getElem?_set_ne different]
  · intro slot fragment expanded
    have other : uv ≠ slot := by
      intro same
      subst slot
      cases Option.some.inj (stored.symm.trans expanded)
    refine ⟨?_, roots slot fragment expanded, fun _ => Iff.rfl⟩
    simp only [List.getElem?_set_ne other]
  · intro slot fragment expanded
    by_cases same : uv = slot
    · subst slot
      rw [List.getElem?_set_self inside] at expanded
      cases Option.some.inj expanded
    · exact Or.inl (by simpa only [List.getElem?_set_ne same] using expanded)

private theorem check_repeated_history
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (held heldHandle fuel uv handle : Nat) (scs : List Suspended)
    (before after : Core) (repeated : Bool)
    (isolated : IsolatedPending held heldHandle before)
    (ready : EnumerationDriver.Ready uv before) (different : uv ≠ held)
    (stored : before.values[uv]? = some (.unenumerated (some handle) scs))
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before repeated after) : HeldFragmentHistory held heldHandle before after := by
  cases repeated with
  | false =>
      exact HeldFragmentHistory.of_frame held heldHandle before after ready.safe isolated
        (SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame heap fuel uv handle scs
          before after ready.safe.1.total observed)
  | true =>
      cases decoded : lookupNode heap handle with
      | none =>
          have impossible : Success (failure .unresolvedReference) before true after := by
            simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
          exact (success_failure .unresolvedReference before after true impossible).elim
      | some value =>
          by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
          · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
            obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
            obtain ⟨same, resolvedSafe, _counter, _protected⟩ :=
              EnumerationDriver.representative_root fuel uv root before resolved ready.safe
                ready.inside ready.root resolution
            subst root
            have frame := representative_frame fuel uv uv before resolved ready.safe.1.total resolution
            have first := HeldFragmentHistory.of_frame held heldHandle before resolved ready.safe isolated frame
            obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
            obtain ⟨currentSame, stateSame⟩ := (EnumerationDriver.get_success resolved currentState current).mp reading
            subst current currentState
            by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry uv
            · simp only [seen, ↓reduceIte] at continued
              obtain ⟨token, cleared, written, returned⟩ := (success_bind _ _ _ _ _).mp continued
              cases token
              obtain ⟨_same, afterSame⟩ := (success_pure true true cleared after).mp returned
              subst after
              have resolvedStored : resolved.values[uv]? = some (.unenumerated (some handle) scs) := by
                simpa only [frame.values] using stored
              have second := pending_write_history held heldHandle uv (some handle) (some handle)
                scs [] resolved cleared first.isolated
                (fun slot fragment expanded => (enumerated_root resolved resolvedSafe slot fragment expanded).2)
                different resolvedStored (Or.inl rfl) written
              exact HeldFragmentHistory.trans held heldHandle before resolved cleared first second
            · have impossible : Success (pure false) resolved true after := by
                simpa only [seen, ↓reduceIte] using continued
              obtain ⟨impossible, _same⟩ := (success_pure false true resolved after).mp impossible
              cases impossible
          · have impossible : Success (pure false) before true after := by
              simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary,
                Bool.false_eq_true, ↓reduceIte] using observed
            obtain ⟨impossible, _same⟩ := (success_pure false true before after).mp impossible
            cases impossible

variable [DecidableEq (EdgeKey Symbol Constraint)]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

private theorem prepared_action_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing)
    (held heldHandle nativeFuel representativeFuel uv oldHandle : Nat) (scs : List Suspended)
    (oldValue value : Node) (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit) (checked after : Core)
    (isolated : IsolatedPending held heldHandle checked)
    (total : UnionFind.Total checked.representatives) (root : IsRoot checked.representatives uv)
    (roots : ∀ (slot : Nat) (fragment : Fragments.Fragment Symbol), checked.values[slot]? = some (.enumerated fragment) →
      IsRoot checked.representatives slot)
    (different : uv ≠ held)
    (stored : checked.values[uv]? = some (.unenumerated (some oldHandle) scs))
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel
      representativeFuel uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (observed : Success action checked () after) : HeldFragmentHistory held heldHandle checked after := by
  have selectedPrepared := prepared
  cases narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap with
  | failed fault current =>
      simp only [SourcePruningEnumerationAction.prepare,
        SourcePruningEnumerationAction.prepareWithNarrow, narrowed] at prepared
      cases prepared
  | done actualValue current =>
      simp only [SourcePruningEnumerationAction.prepare,
        SourcePruningEnumerationAction.prepareWithNarrow, narrowed] at prepared
      have valueSame : actualValue = value :=
        congrArg Prod.fst (MergedSourceComparison.Result.done.inj prepared).1
      have heapSame : current = nextHeap := (MergedSourceComparison.Result.done.inj prepared).2
      rw [valueSame] at prepared
      have nonempty : value ≠ .empty := by
        intro empty
        have actionField := congrArg Prod.snd (MergedSourceComparison.Result.done.inj prepared).1
        have actionSame : (reject : EnumerateM Symbol Constraint Unit) = action :=
          Option.some.inj (by simpa only [empty] using actionField)
        have impossible : Success (reject : EnumerateM Symbol Constraint Unit) checked () after := by
          rw [actionSame]
          exact observed
        exact reject_unsuccessful checked after () impossible
      have encoded : ∃ newHandle, encodeNode value = some newHandle := by
        cases value with
        | empty => exact (nonempty rfl).elim
        | reference name =>
            have actionField := congrArg Prod.snd (MergedSourceComparison.Result.done.inj prepared).1
            have impossible : (none : Option (EnumerateM Symbol Constraint Unit)) = some action := by
              simpa only [encodeNode] using actionField
            cases impossible
        | node entry rows depth free => exact ⟨entry.identity + 1, rfl⟩
        | union entry members depth free => exact ⟨entry.identity + 1, rfl⟩
        | mu entry body depth ordinary => exact ⟨entry.identity + 1, rfl⟩
      obtain ⟨newHandle, encoded⟩ := encoded
      have actualNarrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
          .done value nextHeap := by
        simpa only [valueSame, heapSame] using narrowed
      have actual := SourcePruningEnumerationSelectedStep.prepared_action holeKey fits admits metadata
        nativeFuel representativeFuel uv oldHandle newHandle scs oldValue value heap nextHeap
        actualNarrowed nonempty encoded
      rw [selectedPrepared] at actual
      have actionSame : action =
          (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
            else representative representativeFuel uv >>= fun selected =>
              setValue selected (.unenumerated (some newHandle) scs)) :=
        Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj actual).1).2
      rw [actionSame] at observed
      by_cases same : newHandle = oldHandle
      · rw [ite_eq_left same] at observed
        exact frame_history held heldHandle checked after isolated roots (pure_frame () () checked after observed)
      · rw [ite_eq_right same] at observed
        obtain ⟨selected, resolved, reading, writing⟩ := (success_bind _ _ _ _ _).mp observed
        have frame := representative_frame representativeFuel uv selected checked resolved total reading
        obtain ⟨found, foundLookup, selectedRoot, _endpoint⟩ :=
          (representative_success representativeFuel uv checked resolved selected).mp reading
        have selectedIsUv : selected = uv := by
          rw [selectedRoot]
          exact (UnionFind.reaches_unique
            (UnionFind.findRoot_correct representativeFuel checked.representatives uv found foundLookup).1
            root.choose_spec).1
        rw [selectedIsUv] at writing
        have resolvedStored : resolved.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
          simpa only [frame.values] using stored
        have first := frame_history held heldHandle checked resolved isolated roots frame
        have second := pending_write_history held heldHandle uv (some oldHandle) (some newHandle)
          scs scs resolved after first.isolated (frame_expanded_roots checked resolved roots frame)
          different resolvedStored (Or.inr rfl) writing
        exact HeldFragmentHistory.trans held heldHandle checked resolved after first second

/-- Every retained prefix core preserves the original held fragment history. -/
theorem prefix_held_fragment_history_at_original_budget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (workFuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (held heldHandle : Nat) (value : Node)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (isolated : IsolatedPending held heldHandle before.core)
    (decoded : lookupNode caller.checked.native.machine.heap heldHandle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    uv ≠ held ∧
      match runPrefix holeKey fits admits graph templates stop order metadata
          workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query with
      | .stopped _ _ => True
      | .parked checked candidate _ =>
          HeldFragmentHistory held heldHandle before.core checked ∧
            ∀ after, candidate = some after → HeldFragmentHistory held heldHandle before.core after.core
      | .narrowed checked _ _ _ _ candidate _ _ =>
          HeldFragmentHistory held heldHandle before.core checked ∧
            ∀ after, candidate = some after → HeldFragmentHistory held heldHandle before.core after.core
 := by
  classical
  have ready := SourcePruningEnumerationRecursive.packet_selected_ready formulas solver inventory
    stop order metadata caller memos before uv packet chosen
  have different := packet_restart_ne formulas solver inventory caller memos metadata before
    held heldHandle uv value stop order packet isolated decoded boundary chosen
  refine ⟨different, ?_⟩
  by_cases readable : ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
      ExceptT.run (getValue workFuel uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]
  · obtain ⟨oldHandle, scs, readAfter, reading⟩ := readable
    have readSuccess : Success (getValue workFuel uv) before.core
        (.unenumerated (some oldHandle) scs) readAfter := by
      rw [Success, reading]
      exact List.mem_singleton_self _
    have readFrame := (getValue_frame workFuel uv before.core readAfter _ ready.safe.1.total readSuccess).1
    have readReady := (EnumerationDriver.getValue_ready workFuel uv before.core readAfter _ ready readSuccess).1
    have readStored := (EnumerationDriver.getValue_root workFuel uv before.core readAfter _
      ready.safe ready.inside ready.root readSuccess).2.2.2
    have readHistory := HeldFragmentHistory.of_frame held heldHandle before.core readAfter ready.safe isolated readFrame
    by_cases checkedResult : ∃ (repeated : Bool) (checked : Core),
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap workFuel uv oldHandle scs readAfter) = [.ok (repeated, checked)]
    · obtain ⟨repeated, checked, checking⟩ := checkedResult
      have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap workFuel uv oldHandle scs) readAfter repeated checked := by
        rw [Success, checking]
        exact List.mem_singleton_self _
      have checkHistory := check_repeated_history caller.checked.native.machine.heap
        held heldHandle workFuel uv oldHandle scs readAfter checked repeated readHistory.isolated
        readReady different readStored checkSuccess
      have checkedHistory := HeldFragmentHistory.trans held heldHandle before.core readAfter checked
        readHistory checkHistory
      cases repeated with
      | true =>
          unfold runPrefix runPrefixWithNarrow
          simp only [reading, checking]
          refine ⟨checkedHistory, ?_⟩
          intro after adapted
          rw [SourcePruningEnumerationParkedRestart.adapt_core caller.checked.native.machine.heap
            workFuel uv oldHandle scs before after checked adapted]
          exact checkedHistory
      | false =>
          have checkFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
            caller.checked.native.machine.heap workFuel uv oldHandle scs readAfter checked
            (readFrame.total ready.safe.1.total) checkSuccess
          have wholeFrame := readFrame.trans checkFrame
          have checkedRoot : IsRoot checked.representatives uv :=
            ⟨ready.root.choose, (wholeFrame.reaches uv uv ready.root.choose).mpr ready.root.choose_spec⟩
          have checkedStored : checked.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
            simpa only [checkFrame.values] using readStored
          have noCandidate : HeldFragmentHistory held heldHandle before.core checked ∧
              ∀ after, (none : Option Cached) = some after → HeldFragmentHistory held heldHandle before.core after.core := by
            refine ⟨checkedHistory, ?_⟩
            intro after impossible
            cases impossible
          cases oldDecoded : lookupNode caller.checked.native.machine.heap oldHandle with
          | none =>
              simp only [runPrefix, runPrefixWithNarrow, reading, checking, oldDecoded]
          | some oldValue =>
              unfold runPrefix runPrefixWithNarrow
              simp only [reading, checking, oldDecoded,
                ← SourcePruningEnumerationAction.prepare_configured_eq]
              cases preparedEq : SourcePruningEnumerationAction.prepare (EnumGuard := Constraint) holeKey fits admits metadata
                  workFuel workFuel uv oldHandle scs oldValue caller.checked.native.machine.heap with
              | failed fault heap =>
                  exact noCandidate
              | done pair heap =>
                  obtain ⟨narrowedValue, possibleAction⟩ := pair
                  cases possibleAction with
                  | none =>
                      exact noCandidate
                  | some action =>
                      dsimp only
                      by_cases ran : ∃ observed : Core,
                          ExceptT.run (action checked) = [.ok ((), observed)]
                      · obtain ⟨observed, raw⟩ := ran
                        have actionSuccess : Success action checked () observed := by
                          rw [Success, raw]
                          exact List.mem_singleton_self _
                        have checkedRoots := frame_expanded_roots before.core checked
                          (fun slot fragment expanded => (enumerated_root before.core ready.safe slot fragment expanded).2)
                          wholeFrame
                        have actionHistory := prepared_action_history holeKey fits admits metadata
                          held heldHandle workFuel workFuel uv oldHandle scs oldValue narrowedValue
                          caller.checked.native.machine.heap heap action checked observed checkedHistory.isolated
                          (wholeFrame.total ready.safe.1.total) checkedRoot checkedRoots different checkedStored
                          preparedEq actionSuccess
                        have wholeHistory := HeldFragmentHistory.trans held heldHandle before.core checked observed
                          checkedHistory actionHistory
                        simp only [raw]
                        cases encoded : encodeNode narrowedValue with
                        | none =>
                            exact noCandidate
                        | some newHandle =>
                            dsimp only
                            cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap workFuel
                                uv oldHandle newHandle scs before observed with
                            | none =>
                                exact noCandidate
                            | some attached =>
                                dsimp only
                                have attachedCore := SourcePruningEnumerationNarrowAdapter.adapt_core heap
                                  workFuel uv oldHandle newHandle scs before attached observed adapted
                                have attachedHistory : HeldFragmentHistory held heldHandle before.core attached.core := by
                                  rw [attachedCore]
                                  exact wholeHistory
                                have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
                                    graph templates workFuel metadata uv (.inr newHandle) attached.core) =
                                    [.ok ((false, metadata), attached.core)] := by
                                  rw [SourcePruningRecordTypes.recordTypes_inr]
                                  rfl
                                simp only [recorded]
                                refine ⟨checkedHistory, ?_⟩
                                intro after candidate
                                cases candidate
                                exact attachedHistory
                      · generalize rawEq : ExceptT.run (action checked) = rawAction
                        cases rawAction with
                        | nil => exact noCandidate
                        | cons first rest =>
                            cases first with
                            | error fault => exact noCandidate
                            | ok pair =>
                                obtain ⟨token, observed⟩ := pair
                                cases token
                                cases rest with
                                | nil => exact (ran ⟨observed, rawEq⟩).elim
                                | cons another remaining => exact noCandidate
    · have stopped : runPrefix holeKey fits admits graph templates stop order metadata
          workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
          .stopped (ExceptT.run (getValue workFuel uv before.core))
            (some (ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
              caller.checked.native.machine.heap workFuel uv oldHandle scs readAfter))) := by
        unfold runPrefix runPrefixWithNarrow
        simp only [reading]
        split
        · exact (checkedResult ⟨true, _, by assumption⟩).elim
        · exact (checkedResult ⟨false, _, by assumption⟩).elim
        · rfl
      simp only [stopped]
  · have stopped : runPrefix holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
        .stopped (ExceptT.run (getValue workFuel uv before.core)) none := by
      unfold runPrefix runPrefixWithNarrow
      dsimp only
      split
      · exact (readable ⟨_, _, _, by assumption⟩).elim
      · rfl
    simp only [stopped]


end MicroCFTA.SourcePruningEnumerationSelectedStep
