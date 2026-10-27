import MicroCFTA.SourcePruningEnumerationIsolatedPrefixOperations
import MicroCFTA.SourcePruningEnumerationRecursivePrefixLanguage

/-!
# Isolation at the actual retained recursive prefix

The original restart decision selects a root other than the isolated boundary.
The actual runtime equation supplies the successful prepared action receipt.
The original prefix producer supplies one sufficient family for every selected root.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates EnumerationDischargeHistory
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

private theorem retained_action_success
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (fuel uv oldHandle : Nat) (scs : List Suspended) (oldValue value : Node)
    (caller reached : Caller width) (before after : Cached) (queries : SourceEndpointMemo.Memos)
    (readAfter checked : Core) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (selectedAction : EnumerateM Symbol Constraint Unit)
    (preparedField : MergedSourceComparison.Result Symbol Constraint
      (Node × Option (EnumerateM Symbol Constraint Unit)))
    (right : Option (List (Except Error ((Bool × Metadata Typing) × Core))))
    (ordinary : Option (List (Except Error ((Nat × Nat × List Suspended × Node) × Core)) ×
      Option (SourcePruningEnumerationNativeBranches.Result width)))
    (reading : ExceptT.run (getValue fuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (checking : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap fuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata fuel fuel uv oldHandle
      scs oldValue caller.checked.native.machine.heap = .done (value, some selectedAction) heap)
    (actual : runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
      uv caller before queries = .narrowed checked preparedField reached queries
        (some [.ok ((), after.core)]) (some after) right ordinary) :
    Success selectedAction checked () after.core := by
  simp only [runPrefix, reading, checking, decoded, prepared] at actual
  cases rawEq : ExceptT.run (selectedAction checked) with
  | nil => simp only [rawEq] at actual; cases actual
  | cons first rest =>
      cases first with
      | error fault => simp only [rawEq] at actual; cases actual
      | ok pair =>
          obtain ⟨token, observed⟩ := pair
          cases token
          cases rest with
          | cons _ _ => simp only [rawEq] at actual; cases actual
          | nil =>
              simp only [rawEq] at actual
              cases encoded : encodeNode value with
              | none => simp only [encoded] at actual; cases actual
              | some newHandle =>
                  simp only [encoded] at actual
                  cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap fuel uv oldHandle newHandle
                      scs before observed with
                  | none => simp only [adapted] at actual; cases actual
                  | some attached =>
                      have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel
                          metadata uv (.inr newHandle) attached.core) = [.ok ((false, metadata), attached.core)] := by
                        rw [SourcePruningRecordTypes.recordTypes_inr]
                        rfl
                      simp only [adapted, recorded] at actual
                      have ⟨_checked, _prepared, _caller, _queries, actionSame, _candidate, _right, _ordinary⟩ :=
                        Result.narrowed.inj actual
                      have coreSame : observed = after.core := by
                        simpa only [Option.some.injEq, List.cons.injEq, Except.ok.injEq, Prod.mk.injEq,
                          true_and, and_true] using actionSame
                      rw [Success, ← coreSame, rawEq]
                      exact List.mem_singleton_self _


variable [DecidableEq Symbol] [DecidableEq Node]

private theorem finish_cache_fields
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (uv : Nat) (observed : Result width Typing) :
    match observed with
    | .stopped _ _ | .parked _ _ _ => finish checkEmpty edgesOf 0 0 0 0 0 uv observed = observed
    | .narrowed checked prepared reached queries action candidate right _ =>
        ∃ ordinary, finish checkEmpty edgesOf 0 0 0 0 0 uv observed =
          .narrowed checked prepared reached queries action candidate right ordinary := by
  cases observed with
  | stopped _ _ => rfl
  | parked _ _ _ => rfl
  | narrowed checked prepared reached queries action candidate right ordinary =>
      dsimp only
      unfold finish
      split <;> simp_all only [Result.narrowed.injEq] <;> subst_vars <;>
        simp only [true_and] <;> exact ⟨_, rfl⟩


/-- Every retained cache of the valid actual prefix preserves the original isolated boundary. -/
theorem prefix_isolated
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (held heldHandle : Nat) (value : Node)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (isolated : IsolatedPending held heldHandle before.core)
    (decoded : lookupNode caller.checked.native.machine.heap heldHandle = some value)
    (boundary : MergedOrdinaryHeight.recursiveBoundary value = true)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query)) :
    match runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query with
    | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
        IsolatedPending held heldHandle after.core
    | _ => True := by
  have ready := SourcePruningEnumerationRecursive.packet_selected_ready formulas solver inventory
    stop order metadata caller memos before uv packet chosen
  have different := packet_restart_ne formulas solver inventory caller memos metadata before
    held heldHandle uv value stop order packet isolated decoded boundary chosen
  generalize actual : runPrefix holeKey fits admits graph templates stop order metadata
    fuel fuel fuel fuel fuel fuel uv caller before memos.query = observed at valid ⊢
  have full := valid.2.1
  cases observed with
  | stopped read checked => trivial
  | parked checked candidate raw =>
      obtain ⟨oldHandle, scs, readAfter, reading, checking, cached, same, core, _cacheValid,
        _safe, _pending, _counter, _ordered, _raw⟩ := full
      cases same
      have readSuccess : Success (getValue fuel uv) before.core
          (.unenumerated (some oldHandle) scs) readAfter := by
        rw [Success, reading]
        exact List.mem_singleton_self _
      have frame := (getValue_frame fuel uv before.core readAfter _ ready.safe.1.total readSuccess).1
      have readReady := (EnumerationDriver.getValue_ready fuel uv before.core readAfter _ ready readSuccess).1
      have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap fuel uv oldHandle scs) readAfter true cached.core := by
        rw [Success, core, checking]
        exact List.mem_singleton_self _
      exact (isolated.through_frame frame).through_checkRepeated caller.checked.native.machine.heap
        held heldHandle fuel uv oldHandle scs readAfter cached.core true readReady different checkSuccess
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨next, finished⟩ := finish_cache_fields checkEmpty edgesOf uv
            (.narrowed checked prepared reached queries action (some after) right ordinary)
          rw [finished] at full
          obtain ⟨oldHandle, scs, readAfter, reading, checking, oldValue, value, heap, selectedAction,
            final, oldDecoded, narrowed, selectedPrepared, _prepared, _reachedSame, queriesSame,
            _post, _saved, shape⟩ := full
          rcases shape with ⟨_empty, _action, impossible, _right, _ordinary⟩ |
            ⟨newHandle, cached, nonempty, encoded, actionSame, cachedSame, _cacheValid, _safe,
              _pending, _ready, _stored, _waiting, _right, _rest⟩
          · cases impossible
          · have same : after = cached := Option.some.inj cachedSame
            subst cached
            have actionSuccess := retained_action_success holeKey fits admits graph templates stop order metadata
              fuel uv oldHandle scs oldValue value caller reached before after memos.query readAfter checked
              heap selectedAction prepared right ordinary reading checking oldDecoded selectedPrepared
              (by simpa only [actionSame, queriesSame] using actual)
            have readSuccess : Success (getValue fuel uv) before.core
                (.unenumerated (some oldHandle) scs) readAfter := by
              rw [Success, reading]
              exact List.mem_singleton_self _
            have readFrame := (getValue_frame fuel uv before.core readAfter _ ready.safe.1.total readSuccess).1
            have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
                caller.checked.native.machine.heap fuel uv oldHandle scs) readAfter false checked := by
              rw [Success, checking]
              exact List.mem_singleton_self _
            have checkFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
              caller.checked.native.machine.heap fuel uv oldHandle scs readAfter checked
              (readFrame.total ready.safe.1.total) checkSuccess
            have wholeFrame := readFrame.trans checkFrame
            have checkedRoot : IsRoot checked.representatives uv :=
              ⟨ready.root.choose, (wholeFrame.reaches uv uv ready.root.choose).mpr ready.root.choose_spec⟩
            have readStored := (EnumerationDriver.getValue_root fuel uv before.core readAfter _
              ready.safe ready.inside ready.root readSuccess).2.2.2
            have checkedStored : checked.values[uv]? = some (.unenumerated (some oldHandle) scs) := by
              simpa only [checkFrame.values] using readStored
            exact (isolated.through_frame wholeFrame).through_prepared_nonempty
              holeKey fits admits metadata held heldHandle fuel fuel uv oldHandle newHandle scs oldValue value
              caller.checked.native.machine.heap heap selectedAction checked after.core
              (wholeFrame.total ready.safe.1.total) checkedRoot different checkedStored narrowed nonempty encoded
              selectedPrepared actionSuccess

end MicroCFTA.SourcePruningEnumerationSelectedStep

namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationDischargeHistory InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Symbol] [DecidableEq Node]

/-- The original prefix producer also preserves every initial isolated boundary in each retained cache. -/
theorem packet_prefix_complete_isolated
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before) :
    ∃ bound,
      (∀ extra selected,
        SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
        SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
          stop order metadata formulas solver inventory (bound + extra) selected caller before memos
          (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
            selected caller before memos.query)) ∧
      ∀ extra selected,
        SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
        ∀ held handle value,
          IsolatedPending held handle before.core →
          lookupNode caller.checked.native.machine.heap handle = some value →
          MergedOrdinaryHeight.recursiveBoundary value = true →
          match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
              (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
              selected caller before memos.query with
          | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
              IsolatedPending held handle after.core
          | _ => True := by
  obtain ⟨bound, completed⟩ := packet_prefix_complete holeKey fits admits graph templates checkEmpty edgesOf
    stop order metadata formulas solver inventory caller memos before packet
  refine ⟨bound, completed, ?_⟩
  intro extra selected chosen held handle value isolated decoded boundary
  exact SourcePruningEnumerationSelectedStep.prefix_isolated holeKey fits admits graph templates checkEmpty edgesOf
    stop order metadata formulas solver inventory (bound + extra) selected caller before memos held handle value
    packet isolated decoded boundary chosen (completed extra selected chosen)

end MicroCFTA.SourcePruningEnumerationRecursive
