import MicroCFTA.SourcePruningEnumerationPrefixMass
import MicroCFTA.SourcePruningEnumerationNativeWork
import MicroCFTA.SourcePruningEnumerationStorageCallbackProgress

/-!
# Work at the actual common selected prefix

Parking retains pending witness size and clears the selected flag.
Narrowing retains pending witness size and keeps all other flags.
The current packet supplies validity at the same actual prefix observation.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPrefixWork
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open EnumerationStorageProgress InternedConstructorTemplates
open SourcePruningEnumerationSelectedStep SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

private theorem replace_pending (before after : Core) (uv oldHandle newHandle : Nat)
    (oldScs newScs : List Suspended) (assignment : Nat → Term Symbol)
    (stored : before.values[uv]? = some (.unenumerated (some oldHandle) oldScs))
    (written : Success (setValue uv (.unenumerated (some newHandle) newScs)) before () after) :
    pendingSize after assignment = pendingSize before assignment := by
  have shape := (EnumerationDriver.modify_success _ before after).mp written
  have same := values_set_pendingSize before uv (.unenumerated (some oldHandle) oldScs)
    (.unenumerated (some newHandle) newScs) assignment stored
  rw [shape]
  exact Nat.add_right_cancel same

private theorem check_true_pending
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel uv handle : Nat) (scs : List Suspended) (before after : Core)
    (safe : Safe before) (inside : uv < before.counter) (root : IsRoot before.representatives uv)
    (stored : before.values[uv]? = some (.unenumerated (some handle) scs))
    (assignment : Nat → Term Symbol)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before true after) :
    ∃ value, lookupNode heap handle = some value ∧
      MergedOrdinaryHeight.recursiveBoundary value = true ∧
      pendingSize after assignment = pendingSize before assignment := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before true after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨selected, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
        have selectedSame := (EnumerationDriver.representative_root fuel uv selected before resolved
          safe inside root resolution).1
        subst selected
        have frame := representative_frame fuel uv uv before resolved safe.1.total resolution
        obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, stateSame⟩ := (EnumerationDriver.get_success resolved currentState current).mp reading
        subst current
        subst currentState
        split at continued
        · obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain ⟨_answer, afterSame⟩ := (success_pure true true written after).mp final
          have currentStored : resolved.values[uv]? = some (.unenumerated (some handle) scs) := by
            simpa only [frame.values] using stored
          refine ⟨value, rfl, boundary, ?_⟩
          rw [afterSame]
          exact (replace_pending resolved written uv handle handle scs [] assignment currentStored writing).trans
            (frame_pendingSize before resolved assignment frame)
        · obtain ⟨impossible, _state⟩ := (success_pure false true resolved after).mp continued
          cases impossible
      · have impossible : Success (pure false : EnumerateM Symbol Constraint Bool) before true after := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, ite_eq_right boundary] using observed
        obtain ⟨impossible, _state⟩ := (success_pure false true before after).mp impossible
        cases impossible

private theorem indexed_flags
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel uv : Nat) (value : UVarValue Symbol) (gained lost : List Suspended)
    (before after : Cached)
    (actual : SourcePruningEnumerationNativeIndex.write heap fuel uv value gained lost before = some after) :
    ∃ flag, SourcePruningEnumerationNativeIndex.candidate heap value = some flag ∧
      ∀ other, after.expandable other = if other = uv then flag else before.expandable other := by
  unfold SourcePruningEnumerationNativeIndex.write at actual
  cases found : SourcePruningEnumerationNativeIndex.candidate heap value with
  | none => simp only [found, Option.bind_none] at actual; cases actual
  | some flag =>
      simp only [found, Option.bind_some] at actual
      cases removed : SourcePruningEnumerationNativeIndex.count fuel before.core.representatives
          (-1) lost before.waiting with
      | none => simp only [removed, Option.bind_none] at actual; cases actual
      | some waiting =>
          simp only [removed, Option.bind_some] at actual
          cases added : SourcePruningEnumerationNativeIndex.count fuel before.core.representatives
              1 gained waiting with
          | none => simp only [added, Option.bind_none] at actual; cases actual
          | some saved =>
              simp only [added, Option.bind_some, Option.some.injEq] at actual
              subst after
              exact ⟨flag, rfl, fun _ => rfl⟩

private theorem parked_flags
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel uv handle : Nat) (scs : List Suspended) (value : Node)
    (before after : Cached) (checked : Core)
    (decoded : lookupNode heap handle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (adapted : SourcePruningEnumerationParkedRestart.adapt heap fuel uv handle scs before checked = some after) :
    ∀ other, after.expandable other = if other = uv then false else before.expandable other := by
  simp only [SourcePruningEnumerationParkedRestart.adapt, Option.map_eq_some_iff] at adapted
  obtain ⟨indexed, written, attached⟩ := adapted
  obtain ⟨flag, found, flags⟩ := indexed_flags heap fuel uv (.unenumerated (some handle) []) [] scs
    (EnumerationExpandableIndex.frame checked before) indexed written
  have same : flag = false := by
    have equality : some false = some flag := by
      simpa only [SourcePruningEnumerationNativeIndex.candidate, decoded, Option.map_some,
        boundary, List.isEmpty_nil, Bool.true_and, Bool.not_true] using found
    exact (Option.some.inj equality).symm
  intro other
  have projection := congrArg (fun cache : Cached => cache.expandable other) attached
  change indexed.expandable other = after.expandable other at projection
  rw [← projection, flags, same]
  rfl

private theorem narrowed_other_flags
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (before after : Cached) (observed : Core)
    (adapted : SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle
      scs before observed = some after) :
    ∀ other, other ≠ uv → after.expandable other = before.expandable other := by
  unfold SourcePruningEnumerationNarrowAdapter.adapt at adapted
  split at adapted
  · cases adapted
    intro other _different
    rfl
  · simp only [Option.map_eq_some_iff] at adapted
    obtain ⟨indexed, written, attached⟩ := adapted
    obtain ⟨_flag, _found, flags⟩ := indexed_flags heap fuel uv (.unenumerated (some newHandle) scs)
      scs scs (EnumerationExpandableIndex.frame observed before) indexed written
    intro other different
    have projection := congrArg (fun cache : Cached => cache.expandable other) attached
    change indexed.expandable other = after.expandable other at projection
    rw [← projection, flags, ite_eq_right different]
    rfl

private theorem filter_length_le (values : List Nat) (first second : Nat → Bool)
    (allowed : ∀ uv ∈ values, first uv = true → second uv = true) :
    (values.filter first).length ≤ (values.filter second).length := by
  revert allowed
  induction values with
  | nil => intro _; exact Nat.le_refl _
  | cons uv rest ih =>
      intro allowed
      have tail := ih (fun other member active => allowed other (List.mem_cons_of_mem uv member) active)
      cases firstFlag : first uv <;> cases secondFlag : second uv
      · simpa only [List.filter_cons, firstFlag, secondFlag, Bool.false_eq_true, ↓reduceIte] using tail
      · simpa only [List.filter_cons, firstFlag, secondFlag, Bool.false_eq_true, ↓reduceIte,
          List.length_cons] using Nat.le_succ_of_le tail
      · have impossible := allowed uv List.mem_cons_self firstFlag
        rw [secondFlag] at impossible
        cases impossible
      · simpa only [List.filter_cons, firstFlag, secondFlag, ↓reduceIte, List.length_cons] using
          Nat.succ_le_succ tail

private theorem candidates_le (before after : Cached) (uv : Nat)
    (counter : after.core.counter = before.core.counter) (selected : before.expandable uv = true)
    (flags : ∀ other, other ≠ uv → after.expandable other = before.expandable other) :
    (EnumerationIndexSelection.candidates after).length ≤
      (EnumerationIndexSelection.candidates before).length := by
  unfold EnumerationIndexSelection.candidates
  rw [counter]
  apply filter_length_le
  intro other _inside active
  by_cases same : other = uv
  · simpa only [same] using selected
  · rw [flags other same] at active
    exact active

private theorem candidates_clear_count
    (before after : EnumerationExpandableIndex.Cached Symbol EnumGuard) (uv : Nat)
    (counter : after.core.counter = before.core.counter)
    (inside : uv < before.core.counter) (selected : before.expandable uv = true)
    (flags : ∀ other, after.expandable other =
      if other = uv then false else before.expandable other) :
    (EnumerationIndexSelection.candidates after).length + 1 =
      (EnumerationIndexSelection.candidates before).length := by
  have unique : (EnumerationIndexSelection.candidates before).Nodup :=
    List.nodup_range.filter _
  have present : uv ∈ EnumerationIndexSelection.candidates before := by
    exact List.mem_filter.mpr ⟨List.mem_range.mpr inside, selected⟩
  have removed : EnumerationIndexSelection.candidates after =
      (EnumerationIndexSelection.candidates before).erase uv := by
    rw [unique.erase_eq_filter]
    unfold EnumerationIndexSelection.candidates
    rw [counter, List.filter_filter]
    apply congrArg (fun predicate => (List.range before.core.counter).filter predicate)
    funext other
    rw [flags]
    by_cases same : other = uv <;> simp [same]
  rw [removed, List.length_erase_of_mem present]
  have positive := List.length_pos_of_mem present
  omega

variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem narrowed_pending
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (nativeFuel representativeFuel readFuel checkFuel uv oldHandle newHandle : Nat)
    (scs : List Suspended) (oldValue value : Node)
    (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit) (before readAfter checked after : Core)
    (safe : Safe before)
    (reading : Success (getValue readFuel uv) before (.unenumerated (some oldHandle) scs) readAfter)
    (checking : Success (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv oldHandle scs)
      readAfter false checked)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (assignment : Nat → Language.Term Symbol)
    (executed : Success action checked () after) :
    pendingSize after assignment = pendingSize before assignment := by
  obtain ⟨readFrame, root, size, oldPath, _readPath, oldStored⟩ :=
    getValue_frame readFuel uv before readAfter _ safe.1.total reading
  have checkFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame heap checkFuel uv oldHandle scs
    readAfter checked (readFrame.total safe.1.total) checking
  have checkedFrame := readFrame.trans checkFrame
  have selectedAction := prepared_action holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle newHandle
    scs oldValue value heap nextHeap narrowed nonempty encoded
  rw [prepared] at selectedAction
  have actionSame : action =
      (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative representativeFuel uv >>= fun selected =>
          setValue selected (.unenumerated (some newHandle) scs)) :=
    Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj selectedAction).1).2
  rw [actionSame] at executed
  by_cases same : newHandle = oldHandle
  · rw [ite_eq_left same] at executed
    obtain ⟨_unit, afterSame⟩ := (success_pure () () checked after).mp executed
    rw [afterSame]
    exact frame_pendingSize before checked assignment checkedFrame
  · rw [ite_eq_right same] at executed
    obtain ⟨selected, resolved, resolution, writing⟩ := (success_bind _ _ _ _ _).mp executed
    have resolvedFrame := representative_frame representativeFuel uv selected checked resolved
      (checkedFrame.total safe.1.total) resolution
    have wholeFrame := checkedFrame.trans resolvedFrame
    obtain ⟨found, lookup, selectedSame, _resolvedSame⟩ :=
      (representative_success representativeFuel uv checked resolved selected).mp resolution
    have path := (UnionFind.findRoot_correct representativeFuel checked.representatives uv found lookup).1
    have rootSame : selected = root := selectedSame.trans
      (UnionFind.reaches_unique path ((checkedFrame.reaches uv root size).mpr oldPath)).1
    have stored : resolved.values[selected]? = some (.unenumerated (some oldHandle) scs) := by
      simpa only [wholeFrame.values, rootSame] using oldStored
    exact (replace_pending resolved after selected oldHandle newHandle scs scs assignment stored writing).trans
      (frame_pendingSize before resolved assignment wholeFrame)

private theorem narrowed_raw
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (fuel uv : Nat) (caller : Caller width) (before : Cached) (queries : Queries)
    (oldHandle : Nat) (scs : List Suspended) (readAfter checked : Core) (oldValue value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (selectedAction : EnumerateM Symbol Constraint Unit)
    (result : Result width Typing) (raw : Raw)
    (reading : ExceptT.run (getValue fuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (checking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      fuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel fuel
      uv oldHandle scs oldValue caller.checked.native.machine.heap = .done (value, some selectedAction) heap)
    (actual : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before queries = result)
    (field : (match (generalizing := false) result with | .narrowed _ _ _ _ action _ _ _ => action | _ => none) = some raw) :
    ExceptT.run (selectedAction checked) = raw := by
  have copied : (match (generalizing := false)
      runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before queries with
    | .narrowed _ _ _ _ action _ _ _ => action
    | _ => none) = some (ExceptT.run (selectedAction checked)) := by
    simp only [runPrefix, SourcePruningEnumerationSelectedStep.runPrefixWithNarrow,
      ← SourcePruningEnumerationAction.prepare_configured_eq, reading, checking, decoded, prepared]
    cases execution : ExceptT.run (selectedAction checked) with
    | nil => rfl
    | cons first rest =>
        cases rest with
        | cons _ _ =>
            cases first with
            | error _ => rfl
            | ok pair =>
                obtain ⟨token, _observed⟩ := pair
                cases token
                rfl
        | nil =>
            cases first with
            | error _ => rfl
            | ok pair =>
                obtain ⟨token, observed⟩ := pair
                cases token
                dsimp only
                cases encodeNode value with
                | none => rfl
                | some newHandle =>
                    dsimp only
                    cases SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle scs
                      before observed with
                    | none => rfl
                    | some attached =>
                        rw [SourcePruningRecordTypes.recordTypes_inr]
                        rfl
  have fields := (congrArg (fun observed : Result width Typing => match observed with
    | .narrowed _ _ _ _ action _ _ _ => action
    | _ => none) actual).trans field
  exact Option.some.inj (copied.symm.trans fields)

variable [DecidableEq Symbol] [DecidableEq Node]

private theorem finish_preserves
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (r n p h k uv : Nat) (observed : Result width Typing) :
    match observed with
    | .stopped _ _ | .parked _ _ _ => finish checkEmpty edgesOf r n p h k uv observed = observed
    | .narrowed checked prepared reached queries action candidate right _ =>
        ∃ ordinary, finish checkEmpty edgesOf r n p h k uv observed =
          .narrowed checked prepared reached queries action candidate right ordinary := by
  cases observed with
  | stopped _ _ => rfl
  | parked _ _ _ => rfl
  | narrowed checked prepared reached queries action candidate right ordinary =>
      dsimp only
      unfold finish
      split <;> simp_all only [Result.narrowed.injEq] <;> subst_vars <;>
        simp only [true_and] <;> exact ⟨_, rfl⟩

/-- The literal prefix retains pending size and consumes only its selected candidate flag. -/
theorem retained_work
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (fuel uv initialBound : Nat) (assignment : Nat → Term Symbol)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (observed : Result width Typing)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos observed)
    (actual : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before memos.query = observed) :
    match (generalizing := false) observed with
    | .parked _ (some after) _ =>
        pendingSize after.core assignment = pendingSize before.core assignment ∧
        (EnumerationIndexSelection.candidates after).length + 1 =
          (EnumerationIndexSelection.candidates before).length ∧
        SourcePruningEnumerationNativeWork.work initialBound after assignment + 1 =
          SourcePruningEnumerationNativeWork.work initialBound before assignment
    | .narrowed _ _ _ _ _ (some after) _ _ =>
        pendingSize after.core assignment = pendingSize before.core assignment ∧
        (EnumerationIndexSelection.candidates after).length ≤
          (EnumerationIndexSelection.candidates before).length ∧
        SourcePruningEnumerationNativeWork.work initialBound after assignment ≤
          SourcePruningEnumerationNativeWork.work initialBound before assignment
    | _ => True := by
  have selection : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [SourcePruningEnumerationRestart.decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  obtain ⟨inside, selected, _unblocked⟩ :=
    SourcePruningEnumerationSelection.offered before (order metadata) uv selection
  have ready := (SourcePruningEnumerationRestart.selected stop order metadata caller before uv
    packet.valid packet.safe chosen).1
  have full := valid.2.1
  cases observed with
  | stopped _ _ => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after =>
          have counter := valid.2.2.1
          obtain ⟨oldHandle, scs, readAfter, reading, checking, cached, same, core,
            _cacheValid, _safe, _pending, _counter, _ordered, _raw⟩ := full
          have equal : after = cached := Option.some.inj same
          subst cached
          have read : Success (getValue fuel uv) before.core (.unenumerated (some oldHandle) scs) readAfter := by
            rw [Success, reading]
            exact List.mem_singleton_self _
          have check : Success (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
              fuel uv oldHandle scs) readAfter true checked := by
            rw [Success, checking]
            exact List.mem_singleton_self _
          have readFrame := (getValue_frame fuel uv before.core readAfter _ packet.safe.1.total read).1
          obtain ⟨readSafe, readCounter, _protected, readStored⟩ := EnumerationDriver.getValue_root
            fuel uv before.core readAfter _ ready.safe ready.inside ready.root read
          have readRoot : IsRoot readAfter.representatives uv :=
            (readSafe.2 uv _ readStored).mp (by intro impossible; cases impossible)
          obtain ⟨value, decoded, boundary, checkSize⟩ := check_true_pending caller.checked.native.machine.heap
            fuel uv oldHandle scs readAfter checked readSafe (by rw [readCounter]; exact inside)
            readRoot readStored assignment check
          have size : pendingSize after.core assignment = pendingSize before.core assignment := by
            rw [core]
            exact checkSize.trans (frame_pendingSize before.core readAfter assignment readFrame)
          have adapted : SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
              fuel uv oldHandle scs before checked = some after := by
            have fields := congrArg (fun outcome : Result width Typing => match outcome with
              | .parked _ candidate _ => candidate
              | _ => none) actual
            simpa only [runPrefix, SourcePruningEnumerationSelectedStep.runPrefixWithNarrow,
              reading, checking] using fields
          have flags := parked_flags caller.checked.native.machine.heap fuel uv oldHandle scs value
            before after checked decoded boundary adapted
          have active := candidates_clear_count before after uv counter inside selected flags
          refine ⟨size, active, ?_⟩
          unfold SourcePruningEnumerationNativeWork.work
          rw [size]
          omega
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          have counter := valid.2.2.1
          obtain ⟨_next, finished⟩ := finish_preserves checkEmpty edgesOf 0 0 0 0 0 uv
            (.narrowed checked prepared reached queries action (some after) right ordinary)
          rw [finished] at full
          obtain ⟨oldHandle, scs, readAfter, reading, checking, oldValue, value, heap,
            selectedAction, _final, decoded, narrowed, preparedRun, _preparedSame, _reached,
            _queries, _post, _saved, shape⟩ := full
          rcases shape with ⟨_empty, _action, noCache, _right, _ordinary⟩ |
            ⟨newHandle, cached, nonempty, encoded, rawSame, same, _rest⟩
          · cases noCache
          · have equal : after = cached := Option.some.inj same
            subst cached
            have execution := narrowed_raw holeKey fits admits graph templates stop order metadata fuel uv
              caller before memos.query oldHandle scs readAfter checked oldValue value heap selectedAction
              (.narrowed checked prepared reached queries action (some after) right ordinary)
              [.ok ((), after.core)] reading checking decoded preparedRun actual rawSame
            have read : Success (getValue fuel uv) before.core (.unenumerated (some oldHandle) scs) readAfter := by
              rw [Success, reading]
              exact List.mem_singleton_self _
            have check : Success (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
                fuel uv oldHandle scs) readAfter false checked := by
              rw [Success, checking]
              exact List.mem_singleton_self _
            have success : Success selectedAction checked () after.core := by
              rw [Success, execution]
              exact List.mem_singleton_self _
            have size := narrowed_pending holeKey fits admits metadata fuel fuel fuel fuel uv oldHandle newHandle
              scs oldValue value caller.checked.native.machine.heap heap selectedAction before.core readAfter checked
              after.core packet.safe read check narrowed nonempty encoded preparedRun assignment success
            have copied : (match (generalizing := false)
                runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
                  uv caller before memos.query with
              | .narrowed _ _ _ _ _ candidate _ _ => candidate
              | _ => none) = SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle
                scs before after.core := by
              simp only [runPrefix, SourcePruningEnumerationSelectedStep.runPrefixWithNarrow,
                ← SourcePruningEnumerationAction.prepare_configured_eq, reading, checking, decoded,
                preparedRun, execution, encoded]
              cases attached : SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle
                  scs before after.core with
              | none => rfl
              | some cached =>
                  rw [SourcePruningRecordTypes.recordTypes_inr]
                  rfl
            have fields := congrArg (fun outcome : Result width Typing => match outcome with
              | .narrowed _ _ _ _ _ candidate _ _ => candidate
              | _ => none) actual
            have adapted : SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle
                scs before after.core = some after := copied.symm.trans fields
            have flags := narrowed_other_flags heap fuel uv oldHandle newHandle scs before after after.core adapted
            have active := candidates_le before after uv counter selected flags
            refine ⟨size, active, ?_⟩
            unfold SourcePruningEnumerationNativeWork.work
            rw [size]
            exact Nat.add_le_add_left active _

/-- Current selected inputs derive validity and work at one common prefix bound. -/
theorem complete_work
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (uv initialBound : Nat) (assignment : Nat → Term Symbol)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)) :
    ∃ fuel, ∀ extra,
      let observed := runPrefix holeKey fits admits graph templates stop order metadata
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv caller before memos.query
      PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (fuel + extra) uv caller before memos observed ∧
      match (generalizing := false) observed with
      | .parked _ (some after) _ =>
          pendingSize after.core assignment = pendingSize before.core assignment ∧
          (EnumerationIndexSelection.candidates after).length + 1 =
            (EnumerationIndexSelection.candidates before).length ∧
          SourcePruningEnumerationNativeWork.work initialBound after assignment + 1 =
            SourcePruningEnumerationNativeWork.work initialBound before assignment
      | .narrowed _ _ _ _ _ (some after) _ _ =>
          pendingSize after.core assignment = pendingSize before.core assignment ∧
          (EnumerationIndexSelection.candidates after).length ≤
            (EnumerationIndexSelection.candidates before).length ∧
          SourcePruningEnumerationNativeWork.work initialBound after assignment ≤
            SourcePruningEnumerationNativeWork.work initialBound before assignment
      | _ => True := by
  have selection : EnumerationPureSelection.next (order metadata) before = .expand uv := by
    cases stop with
    | none => exact Option.some.inj chosen
    | some rule =>
        simp only [SourcePruningEnumerationRestart.decision] at chosen
        split at chosen
        · cases chosen
        · exact Option.some.inj chosen
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨fuel, valid⟩ := prefix_complete holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory caller memos before (order metadata) uv roots packet.context packet.safe
    packet.pending selection realized paths counts flags
  refine ⟨fuel, ?_⟩
  intro extra
  have current := valid extra
  exact ⟨current, retained_work holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory (fuel + extra) uv initialBound assignment caller memos before packet chosen
    _ current rfl⟩

end MicroCFTA.SourcePruningEnumerationSharedPrefixWork
