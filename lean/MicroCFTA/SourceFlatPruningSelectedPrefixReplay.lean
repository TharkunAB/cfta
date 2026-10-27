import MicroCFTA.SourceFlatPruningSelectedPrefix
import MicroCFTA.SourceFlatPruningActionReplay
import MicroCFTA.SourcePruningEnumerationRecursivePrefix

/-!
# Replay of an actual valid selected prefix

The old observation supplies each read and count that the branch uses.
The flat worker retains the same native caller and query table.
The proof does not execute the virtual ordinary continuation in PrefixValid.
-/

namespace MicroCFTA.SourceFlatPruningSelectedPrefix

open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates SourcePruningEnumerationNodes
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "OldCore" => EnumerationState.State Symbol Constraint
local notation "OldCached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata

attribute [local instance] SourcePruningEnumerationTerminalPrefix.terminalPrefixMonadList
  SourcePruningEnumerationTerminalPrefix.terminalPrefixLawfulMonadList

variable {Typing Key : Type} {width : Nat}

private theorem flat_recordTypes_inr
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv node : Nat) :
    SourceFlatPruningOracle.recordTypes graph templates fuel metadata uv (.inr node) =
      pure (false, metadata) := by
  cases templates <;> rfl

variable [DecidableEq (EdgeKey Symbol Constraint)]

variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
  (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)

/-- A retained successful candidate exposes the actual action and index observations. -/
private theorem narrowed_observation
    (fuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : Node) (caller reached : Caller width) (before after : OldCached)
    (queries savedQueries : Queries) (readAfter checked : OldCore)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit)
    (right : Option (List (Except Error ((Bool × Metadata Typing) × OldCore))))
    (ordinary : Option
      (List (Except Error ((Nat × Nat × List Suspended × Node) × OldCore)) ×
        Option (SourcePruningEnumerationNativeBranches.Result width)))
    (reading : ExceptT.run (getValue fuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (checking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap fuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel fuel
      uv oldHandle scs oldValue caller.checked.native.machine.heap = .done (value, some action) heap)
    (encoded : encodeNode value = some newHandle)
    (observed : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
      stop order metadata fuel fuel fuel fuel fuel fuel uv caller before queries =
      .narrowed checked (.done (value, some action) heap) reached savedQueries
        (some [.ok ((), after.core)]) (some after) right ordinary) :
    ExceptT.run (action checked) = [.ok ((), after.core)] ∧
      SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle scs
        before after.core = some after := by
  have missing (left : SourcePruningEnumerationSelectedStep.Result width Typing)
      (absent : match left with
        | .narrowed _ _ _ _ _ candidate _ _ => candidate = none
        | _ => False)
      (equal : left = .narrowed checked (.done (value, some action) heap) reached savedQueries
        (some [.ok ((), after.core)]) (some after) right ordinary) : False := by
    rw [equal] at absent
    cases absent
  have actual := observed
  simp only [SourcePruningEnumerationSelectedStep.runPrefix, reading, checking, decoded, prepared] at actual
  generalize rawEq : ExceptT.run (action checked) = raw at actual
  cases raw with
  | nil => exact (missing _ rfl actual).elim
  | cons first rest =>
      cases rest with
      | cons next tail =>
          cases first with
          | error error => exact (missing _ rfl actual).elim
          | ok pair =>
              obtain ⟨ignored, current⟩ := pair
              cases ignored
              exact (missing _ rfl actual).elim
      | nil =>
          cases first with
          | error error => exact (missing _ rfl actual).elim
          | ok pair =>
              obtain ⟨ignored, current⟩ := pair
              cases ignored
              dsimp only at actual
              rw [encoded] at actual
              dsimp only at actual
              cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv
                  oldHandle newHandle scs before current with
              | none =>
                  rw [adapted] at actual
                  exact (missing _ rfl actual).elim
              | some attached =>
                  rw [adapted] at actual
                  dsimp only at actual
                  rw [SourcePruningRecordTypes.recordTypes_inr] at actual
                  obtain ⟨_checked, _prepared, _caller, _queries, rowsSame, cacheSame, _right, _ordinary⟩ :=
                    SourcePruningEnumerationSelectedStep.Result.narrowed.inj actual
                  have attachedSame : attached = after := by
                    change some attached = some after at cacheSame
                    exact Option.some.inj cacheSame
                  subst attached
                  have coreSame : current = after.core := by
                    simpa only [Option.some.injEq, List.cons.injEq, Except.ok.injEq,
                      Prod.mk.injEq, true_and, and_true] using rowsSame
                  subst current
                  exact ⟨rfl, adapted⟩

variable [DecidableEq Symbol] [DecidableEq Node]

private theorem finish_preserves
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (uv : Nat) (observed : SourcePruningEnumerationSelectedStep.Result width Typing) :
    match observed with
    | .stopped _ _ | .parked _ _ _ =>
        SourcePruningEnumerationSelectedStep.finish checkEmpty edgesOf 0 0 0 0 0 uv observed = observed
    | .narrowed checked prepared reached queries action candidate right _ =>
        ∃ ordinary, SourcePruningEnumerationSelectedStep.finish checkEmpty edgesOf 0 0 0 0 0 uv observed =
          .narrowed checked prepared reached queries action candidate right ordinary := by
  cases observed with
  | stopped _ _ => rfl
  | parked _ _ _ => rfl
  | narrowed checked prepared reached queries action candidate right ordinary =>
      dsimp only
      unfold SourcePruningEnumerationSelectedStep.finish
      split <;> simp_all only [SourcePruningEnumerationSelectedStep.Result.narrowed.injEq] <;>
        subst_vars <;> simp only [true_and] <;> exact ⟨_, rfl⟩

/-- Replay the complete actual prefix from its retained old validity certificate. -/
theorem run_related_of_valid
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : OldCached) (flat : FlatCached) (memos : Memos)
    (related : EnumerationFlatCached.Related flat before)
    (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos
      (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        fuel fuel fuel fuel fuel fuel uv caller before memos.query)) :
    ResultRelated (run holeKey fits admits graph templates stop order metadata fuel fuel uv caller flat memos.query)
      (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        fuel fuel fuel fuel fuel fuel uv caller before memos.query) := by
  generalize original : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
    stop order metadata fuel fuel fuel fuel fuel fuel uv caller before memos.query = observed at valid ⊢
  have full := valid.2.1
  cases observed with
  | stopped read checked =>
      obtain ⟨_oldHandle, _scs, _readAfter, _reading, impossible⟩ := full
      exact impossible.elim
  | parked checked candidate raw =>
      obtain ⟨oldHandle, scs, readAfter, reading, checking, after, candidateSame, coreSame,
        _cacheValid, _safe, _pending, _counter, _ordered, rawSame⟩ := full
      subst candidate
      subst raw
      obtain ⟨flatRead, flatReading, reads⟩ := EnumerationFlatPartial.getValue_replays fuel uv
        flat.core before.core (.unenumerated (some oldHandle) scs) readAfter related.core (by
          rw [Success, reading]
          exact List.mem_singleton_self _)
      obtain ⟨flatChecked, flatChecking, checkedRelated⟩ :=
        SourceFlatPruningRecursion.checkRepeated_replays caller.checked.native.machine.heap fuel uv oldHandle scs
          flatRead readAfter true checked reads (by
            rw [Success, checking]
            exact List.mem_singleton_self _)
      have adapted : SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap fuel
          uv oldHandle scs before checked = some after := by
        have projected := congrArg (fun result => match result with
          | .parked _ attached _ => attached
          | _ => none) original
        simpa only [SourcePruningEnumerationSelectedStep.runPrefix, reading, checking] using projected
      obtain ⟨flatAfter, flatAdapted, caches⟩ := SourceFlatPruningIndexAdapters.parked_completed
        related checkedRelated caller.checked.native.machine.heap fuel uv oldHandle scs adapted
      have flatCore := SourceFlatPruningIndexAdapters.parked_core caller.checked.native.machine.heap
        uv oldHandle scs flat flatAfter flatChecked flatAdapted
      simp only [run, ExceptT.run, flatReading, flatChecking, flatAdapted, Option.map_some, ResultRelated, OptionalRows]
      refine ⟨checkedRelated, caches, ?_⟩
      simpa only [flatCore, coreSame] using SourceFlatPruningRestart.run_related caches stop order metadata
  | narrowed checked preparedResult reached saved action candidate right ordinary =>
      obtain ⟨finishedOrdinary, finished⟩ := finish_preserves checkEmpty edgesOf uv
        (.narrowed checked preparedResult reached saved action candidate right ordinary)
      rw [finished] at full
      have noOrdinary : ordinary = none := valid.1
      subst ordinary
      obtain ⟨oldHandle, scs, readAfter, reading, checking, oldValue, value, heap, oldAction, _final,
        decoded, narrowed, preparation, preparedSame, reachedSame, savedSame, _post, _query, shape⟩ := full
      subst preparedResult
      subst reached
      subst saved
      obtain ⟨flatRead, flatReading, reads⟩ := EnumerationFlatPartial.getValue_replays fuel uv
        flat.core before.core (.unenumerated (some oldHandle) scs) readAfter related.core (by
          rw [Success, reading]
          exact List.mem_singleton_self _)
      obtain ⟨flatChecked, flatChecking, checkedRelated⟩ :=
        SourceFlatPruningRecursion.checkRepeated_replays caller.checked.native.machine.heap fuel uv oldHandle scs
          flatRead readAfter false checked reads (by
            rw [Success, checking]
            exact List.mem_singleton_self _)
      obtain ⟨flatAction, flatPreparation, replay, flatEmpty⟩ := SourceFlatPruningAction.prepare_replays
        holeKey fits admits metadata fuel fuel uv oldHandle scs oldValue value
          caller.checked.native.machine.heap heap oldAction preparation
      rcases shape with empty | live
      · obtain ⟨empty, actionSame, candidateSame, rightSame, _finished⟩ := empty
        subst value
        subst action
        subst candidate
        subst right
        have oldReject : oldAction = EnumerationState.reject := by
          have direct : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel fuel
              uv oldHandle scs oldValue caller.checked.native.machine.heap =
              .done (.empty, some (EnumerationState.reject : EnumerateM Symbol Constraint Unit)) heap := by
            simp only [SourcePruningEnumerationAction.prepare, narrowed]
          rw [preparation] at direct
          exact Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj direct).1).2
        have flatReject := flatEmpty rfl
        subst oldAction
        subst flatAction
        simp only [run, ExceptT.run, flatReading, flatChecking, decoded, flatPreparation]
        change EnumerationFlatState.Related flatChecked checked ∧
          SourceFlatPruningAction.PreparedRelated flatChecked checked
            (.done (.empty, some EnumerationFlatState.reject) heap)
            (.done (.empty, some EnumerationState.reject) heap) ∧ _
        exact ⟨checkedRelated, ⟨rfl, rfl, .nil⟩, rfl, rfl, .nil, trivial, trivial, rfl⟩
      · obtain ⟨newHandle, after, _nonempty, encoded, actionSame, candidateSame,
          _cacheValid, _safe, _pending, _ready, _stored, _waiting, rightSame, _finished, _ordinaryCapability⟩ := live
        subst action
        subst candidate
        subst right
        obtain ⟨actionRaw, adapted⟩ := narrowed_observation holeKey fits admits graph templates stop order metadata
          fuel uv oldHandle newHandle scs oldValue value caller _ before after memos.query memos.query
            readAfter checked heap oldAction _ none reading checking decoded preparation encoded original
        obtain ⟨flatObserved, flatRaw, states⟩ := replay flatChecked checked () after.core checkedRelated (by
          rw [Success, actionRaw]
          exact List.mem_singleton_self _)
        obtain ⟨flatAfter, flatAdapted, caches⟩ := SourceFlatPruningIndexAdapters.narrowed_completed related
          states heap fuel uv oldHandle newHandle scs adapted
        have flatRight : SourceFlatPruningOracle.recordTypes graph templates fuel metadata uv
            (.inr newHandle) flatAfter.core = [.ok ((false, metadata), flatAfter.core)] := by
          rw [flat_recordTypes_inr]
          rfl
        simp only [run, ExceptT.run, flatReading, flatChecking, decoded, flatPreparation, flatRaw, encoded, flatAdapted, flatRight]
        change EnumerationFlatState.Related flatChecked checked ∧
          SourceFlatPruningAction.PreparedRelated flatChecked checked
            (.done (value, some flatAction) heap) (.done (value, some oldAction) heap) ∧ _
        refine ⟨checkedRelated, ⟨rfl, rfl, ?_⟩, rfl, rfl, ?_, caches, ?_, rfl⟩
        · change EnumerationResultRelation.Results EnumerationFlatState.Related
            (flatAction flatChecked) (oldAction checked)
          rw [flatRaw, show oldAction checked = [.ok ((), after.core)] from actionRaw]
          exact .cons (.ok () states) .nil
        · exact .cons (.ok () states) .nil
        · exact .cons (.ok (false, metadata) caches.core) .nil

end MicroCFTA.SourceFlatPruningSelectedPrefix
