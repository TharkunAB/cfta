import MicroCFTA.SourcePruningEnumerationRecursivePrefixLanguage
import MicroCFTA.SourcePruningEnumerationSelectedPrefixCanonical

/-!
# Canonical histories at actual selected-prefix caches

The actual run supplies the selected action receipt.
The original packet producer supplies the same sufficient prefix family.
Canonical remains separate from the restrictions removed by parking.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationSemantics EnumerationValidity
open InternedConstructorTemplates
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


/-- Every retained cache of the valid actual prefix has canonical stored tries. -/
theorem prefix_canonical
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (canonical : Canonical before.core)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query)) :
    match runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query with
    | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ => Canonical after.core
    | _ => True := by
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
      have readCanonical := (getValue_canonical fuel uv before.core readAfter _ canonical readSuccess).1
      have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap fuel uv oldHandle scs) readAfter true cached.core := by
        rw [Success, core, checking]
        exact List.mem_singleton_self _
      exact SourcePruningEnumerationSelectedPrefixCanonical.checkRepeated_canonical
        caller.checked.native.machine.heap fuel uv oldHandle scs readAfter cached.core true
        readCanonical checkSuccess
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨next, finished⟩ := finish_cache_fields checkEmpty edgesOf uv
            (.narrowed checked prepared reached queries action (some after) right ordinary)
          rw [finished] at full
          obtain ⟨oldHandle, scs, readAfter, reading, checking, oldValue, value, heap, selectedAction,
            final, decoded, narrowed, selectedPrepared, _prepared, _reachedSame, queriesSame,
            _post, _saved, shape⟩ := full
          rcases shape with ⟨_empty, _action, impossible, _right, _ordinary⟩ |
            ⟨newHandle, cached, nonempty, encoded, actionSame, cachedSame, _cacheValid, _safe,
              _pending, _ready, _stored, _waiting, _right, _rest⟩
          · cases impossible
          · have same : after = cached := Option.some.inj cachedSame
            subst cached
            have actionSuccess := retained_action_success holeKey fits admits graph templates stop order metadata
              fuel uv oldHandle scs oldValue value caller reached before after memos.query readAfter checked
              heap selectedAction prepared right ordinary reading checking decoded selectedPrepared
              (by simpa only [actionSame, queriesSame] using actual)
            have readSuccess : Success (getValue fuel uv) before.core
                (.unenumerated (some oldHandle) scs) readAfter := by
              rw [Success, reading]
              exact List.mem_singleton_self _
            have readFacts := getValue_canonical fuel uv before.core readAfter _ canonical readSuccess
            have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
                caller.checked.native.machine.heap fuel uv oldHandle scs) readAfter false checked := by
              rw [Success, checking]
              exact List.mem_singleton_self _
            have checkedCanonical := SourcePruningEnumerationSelectedPrefixCanonical.checkRepeated_canonical
              caller.checked.native.machine.heap fuel uv oldHandle scs readAfter checked false
              readFacts.1 checkSuccess
            exact SourcePruningEnumerationSelectedPrefixCanonical.prepared_nonempty_canonical
              holeKey fits admits metadata fuel fuel uv oldHandle newHandle scs oldValue value
              caller.checked.native.machine.heap heap selectedAction checked after.core checkedCanonical
              readFacts.2 narrowed nonempty encoded selectedPrepared actionSuccess

end MicroCFTA.SourcePruningEnumerationSelectedStep

namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationValidity InternedConstructorTemplates
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

/-- Keep the complete semantic prefix packet and append Canonical at its actual retained caches. -/
theorem packet_prefix_complete_semantics_canonical
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (canonical : Canonical before.core) :
    ∃ bound,
      (∀ extra selected,
        SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
        SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
          stop order metadata formulas solver inventory (bound + extra) selected caller before memos
          (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
            selected caller before memos.query)) ∧
      (∀ extra selected,
        SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
        SourcePruningEnumerationSelectedStep.PrefixMeaning formulas solver (bound + extra) selected caller before
          (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
            selected caller before memos.query)) ∧
      ∀ extra selected,
        SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
        match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
            (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
            selected caller before memos.query with
        | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ => Canonical after.core
        | _ => True := by
  obtain ⟨bound, valid, meaning⟩ := packet_prefix_complete_semantics holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory caller memos before packet
  refine ⟨bound, valid, meaning, ?_⟩
  intro extra selected chosen
  exact SourcePruningEnumerationSelectedStep.prefix_canonical holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory (bound + extra) selected
    caller before memos canonical (valid extra selected chosen)

end MicroCFTA.SourcePruningEnumerationRecursive
