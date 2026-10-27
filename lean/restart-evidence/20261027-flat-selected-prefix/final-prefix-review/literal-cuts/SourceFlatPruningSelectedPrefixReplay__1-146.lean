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
