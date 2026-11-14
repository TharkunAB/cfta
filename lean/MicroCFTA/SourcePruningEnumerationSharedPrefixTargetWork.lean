import MicroCFTA.SourcePruningEnumerationSharedPrefixWork

/-!
# Exact selected activity at the common prefix

Narrowing changes only the selected expandable flag.
The complementary debit records whether that flag was cleared.
The actual prefix observation supplies the same cache and native receipt.
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

private theorem candidates_target_debit
    (before after : Cached) (uv : Nat)
    (counter : after.core.counter = before.core.counter)
    (inside : uv < before.core.counter) (selected : before.expandable uv = true)
    (flags : ∀ other, other ≠ uv → after.expandable other = before.expandable other) :
    (EnumerationIndexSelection.candidates after).length +
        (if after.expandable uv then 0 else 1) =
      (EnumerationIndexSelection.candidates before).length := by
  cases active : after.expandable uv with
  | false =>
      have cleared : ∀ other, after.expandable other =
          if other = uv then false else before.expandable other := by
        intro other
        by_cases same : other = uv
        · simpa only [same, ite_true] using active
        · rw [ite_eq_right same, flags other same]
      simpa only [active, Bool.false_eq_true, ↓reduceIte] using
        candidates_clear_count before after uv counter inside selected cleared
  | true =>
      have same : after.expandable = before.expandable := by
        funext other
        by_cases equal : other = uv
        · simp only [equal, active, selected]
        · exact flags other equal
      unfold EnumerationIndexSelection.candidates
      rw [counter, same]
      simp only [↓reduceIte, Nat.add_zero]

variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

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

/-- The same prefix charges a selected flag exactly when narrowing clears it. -/
theorem retained_work_target_debit
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
        after.core.counter = before.core.counter ∧
        (∀ other, other ≠ uv → after.expandable other = before.expandable other) ∧
        pendingSize after.core assignment = pendingSize before.core assignment ∧
        (EnumerationIndexSelection.candidates after).length +
            (if after.expandable uv then 0 else 1) =
          (EnumerationIndexSelection.candidates before).length ∧
        SourcePruningEnumerationNativeWork.work initialBound after assignment +
            (if after.expandable uv then 0 else 1) =
          SourcePruningEnumerationNativeWork.work initialBound before assignment
    | _ => True := by
  have oldWork := retained_work holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory fuel uv initialBound assignment caller memos before packet chosen observed valid actual
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
  have full := valid.2.1
  cases observed with
  | stopped _ _ => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after => exact oldWork
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          have counter := valid.2.2.1
          obtain ⟨_next, finished⟩ := finish_preserves checkEmpty edgesOf 0 0 0 0 0 uv
            (.narrowed checked prepared reached queries action (some after) right ordinary)
          rw [finished] at full
          obtain ⟨oldHandle, scs, readAfter, reading, checking, oldValue, value, heap,
            selectedAction, _final, decoded, _narrowed, preparedRun, _preparedSame, _reached,
            _queries, _post, _saved, shape⟩ := full
          rcases shape with ⟨_empty, _action, noCache, _right, _ordinary⟩ |
            ⟨newHandle, cached, _nonempty, encoded, rawSame, same, _rest⟩
          · cases noCache
          · have equal : after = cached := Option.some.inj same
            subst cached
            have execution := narrowed_raw holeKey fits admits graph templates stop order metadata fuel uv
              caller before memos.query oldHandle scs readAfter checked oldValue value heap selectedAction
              (.narrowed checked prepared reached queries action (some after) right ordinary)
              [.ok ((), after.core)] reading checking decoded preparedRun actual rawSame
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
            have active := candidates_target_debit before after uv counter inside selected flags
            refine ⟨counter, flags, oldWork.1, active, ?_⟩
            unfold SourcePruningEnumerationNativeWork.work
            rw [oldWork.1]
            omega

end MicroCFTA.SourcePruningEnumerationSharedPrefixWork
