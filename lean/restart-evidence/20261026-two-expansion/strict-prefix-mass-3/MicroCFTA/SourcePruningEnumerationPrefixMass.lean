import MicroCFTA.SourcePruningEnumerationPrefixCompletion
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationSuspendedMass

/-!
# Suspended mass at actual selected prefixes

A repeated recursion clears one bucket. A nonempty narrowing retains the
same bucket and changes only its node handle. The literal prefix equation
connects the returned action row to its actual cached endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationPrefixMass
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates
open SourcePruningEnumerationSelectedStep
open SourcePruningEnumerationNodes
open SourcePruningEnumerationPrefixAdmission (suspendedBound suspendedBound_values)
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

private theorem sum_map_set_zero_le {α : Type} (weight : α → Nat) (replacement : α)
    (zero : weight replacement = 0) (values : List α) (index : Nat) :
    ((values.set index replacement).map weight).sum ≤ (values.map weight).sum := by
  induction values generalizing index with
  | nil => simp
  | cons first rest ih =>
      cases index with
      | zero =>
          simp only [List.set_cons_zero, List.map_cons, List.sum_cons, zero]
          omega
      | succ index =>
          simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
          exact Nat.add_le_add_left (ih index) _

/-- Clearing a bucket cannot increase suspended mass, including at an absent slot. -/
theorem cleared_mass_le (before : Core) (target : Nat) (node : Option Nat) :
    suspendedBound {before with values := before.values.set target (.unenumerated node [])} ≤
      suspendedBound before := by
  exact sum_map_set_zero_le (fun value : UVarValue Symbol => match value with
    | .unenumerated _ scs => scs.length
    | _ => 0) (.unenumerated node []) rfl before.values target

/-- A stored pending bucket keeps its exact mass when only its node handle changes. -/
theorem same_bucket_mass (before : Core) (target : Nat) (oldNode newNode : Option Nat)
    (scs : List Suspended) (stored : before.values[target]? = some (.unenumerated oldNode scs)) :
    suspendedBound {before with values := before.values.set target (.unenumerated newNode scs)} =
      suspendedBound before := by
  simpa only [List.nil_append, List.length_nil, Nat.add_zero] using
    SourcePruningEnumerationSuspendedMass.incoming_mass before target oldNode newNode [] scs stored

private theorem check_true_mass
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel uv handle : Nat) (scs : List Suspended) (before after : Core)
    (total : UnionFind.Total before.representatives)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before true after) : suspendedBound after ≤ suspendedBound before := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before true after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
        have frame := representative_frame fuel uv root before resolved total resolution
        obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, stateSame⟩ := (EnumerationDriver.get_success resolved currentState current).mp reading
        subst current
        subst currentState
        split at continued
        · obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
          cases ignored
          obtain ⟨_answer, afterSame⟩ := (success_pure true true written after).mp final
          have writtenSame := (EnumerationDriver.modify_success _ resolved written).mp writing
          rw [afterSame, writtenSame]
          exact Nat.le_trans (cleared_mass_le resolved root (some handle))
            (Nat.le_of_eq (suspendedBound_values before resolved frame.values))
        · obtain ⟨impossible, _state⟩ := (success_pure false true resolved after).mp continued
          cases impossible
      · have impossible : Success (pure false : EnumerateM Symbol Constraint Bool) before true after := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, ite_eq_right boundary] using observed
        obtain ⟨impossible, _state⟩ := (success_pure false true before after).mp impossible
        cases impossible

/-- The actual repeated-recursion read and clear cannot increase the original mass. -/
theorem parked_mass
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (readFuel checkFuel uv oldHandle : Nat) (scs : List Suspended)
    (before readAfter checked : Core) (safe : Safe before)
    (reading : Success (getValue readFuel uv) before (.unenumerated (some oldHandle) scs) readAfter)
    (checking : Success (SourcePruningEnumerationRecursion.checkRepeated heap checkFuel uv oldHandle scs)
      readAfter true checked) : suspendedBound checked ≤ suspendedBound before := by
  have frame := (getValue_frame readFuel uv before readAfter _ safe.1.total reading).1
  exact Nat.le_trans (check_true_mass heap checkFuel uv oldHandle scs readAfter checked
    (frame.total safe.1.total) checking)
      (Nat.le_of_eq (suspendedBound_values before readAfter frame.values))

variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Actual nonempty narrowing preserves the bucket mass after the same read and false recursion check. -/
theorem narrowed_mass
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
    (executed : Success action checked () after) : suspendedBound after = suspendedBound before := by
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
    exact suspendedBound_values before checked checkedFrame.values
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
    have afterSame := (EnumerationDriver.modify_success _ resolved after).mp writing
    rw [afterSame]
    exact (same_bucket_mass resolved selected (some oldHandle) (some newHandle) scs stored).trans
      (suspendedBound_values before resolved wholeFrame.values)

variable [DecidableEq Symbol] [DecidableEq Node]

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
  have fields := (congrArg (fun observed : Result width Typing => match observed with
    | .narrowed _ _ _ _ action _ _ _ => action
    | _ => none) actual).trans field
  simp only [runPrefix, reading, checking, decoded, prepared,
    SourcePruningRecordTypes.recordTypes_inr] at fields
  repeat' first
    | exact Option.some.inj fields
    | (split at fields <;> simp_all only [SourcePruningRecordTypes.recordTypes_inr])

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

/-- The actual selected prefix derives its attached cache's mass bound from the original packet. -/
theorem retained_le
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory)
    (fuel uv : Nat) (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (observed : Result width Typing)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos observed)
    (actual : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before memos.query = observed) :
    match (generalizing := false) observed with
    | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
        suspendedBound after.core ≤ suspendedBound before.core
    | _ => True := by
  have full := valid.2.1
  cases observed with
  | stopped _ _ => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after =>
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
          simpa only [core] using parked_mass caller.checked.native.machine.heap fuel fuel uv oldHandle scs
            before.core readAfter checked packet.safe read check
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
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
            exact Nat.le_of_eq (narrowed_mass holeKey fits admits metadata fuel fuel fuel fuel uv oldHandle newHandle
              scs oldValue value caller.checked.native.machine.heap heap selectedAction before.core readAfter checked
              after.core packet.safe read check narrowed nonempty encoded preparedRun success)

end MicroCFTA.SourcePruningEnumerationPrefixMass
