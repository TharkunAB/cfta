import MicroCFTA.SourcePruningEnumerationPrefixCompletion
import MicroCFTA.SourcePruningEnumerationRecursionOrder

/-!
# Per-slot recursion histories at actual selected-prefix caches

Reading and representative compression retain every history slot.
Recursion checks and prepared actions can change stored values.
The actual retained cache still has the original ancestry function.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
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
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

private theorem checkRepeated_recursion_ancestry {EnumGuard NativeGuard : Type}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard) (repeated : Bool)
    (total : UnionFind.Total before.representatives)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before repeated after) : after.recursionAncestry = before.recursionAncestry := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before repeated after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after repeated impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
        have resolvedFrame := representative_frame fuel uv root before resolved total resolution
        obtain ⟨current, reading, read, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, readingSame⟩ := (EnumerationDriver.get_success resolved reading current).mp read
        subst current
        subst reading
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry root
        · rw [ite_eq_left seen] at continued
          obtain ⟨token, written, writing, finished⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          have writtenSame := (EnumerationDriver.modify_success _ resolved written).mp writing
          obtain ⟨_same, afterSame⟩ := (success_pure true repeated written after).mp finished
          rw [afterSame, writtenSame]
          exact resolvedFrame.recursionAncestry
        · rw [ite_eq_right seen] at continued
          obtain ⟨_same, afterSame⟩ := (success_pure false repeated resolved after).mp continued
          rw [afterSame]
          exact resolvedFrame.recursionAncestry
      · have pureObserved : Success (pure false) before repeated after := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, ite_eq_right boundary] using observed
        obtain ⟨_same, afterSame⟩ := (success_pure false repeated before after).mp pureObserved
        rw [afterSame]

variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem prepared_nonempty_recursion_ancestry
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (nativeFuel representativeFuel uv oldHandle newHandle : Nat)
    (scs : List Suspended) (oldValue value : Node)
    (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit) (checked after : Core)
    (total : UnionFind.Total checked.representatives)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (observed : Success action checked () after) :
    after.recursionAncestry = checked.recursionAncestry := by
  have actual := prepared_action holeKey fits admits metadata
    nativeFuel representativeFuel uv oldHandle newHandle scs oldValue value heap nextHeap
    narrowed nonempty encoded
  rw [prepared] at actual
  have actionSame : action =
      (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative representativeFuel uv >>= fun selected =>
          setValue selected (.unenumerated (some newHandle) scs)) :=
    Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj actual).1).2
  rw [actionSame] at observed
  by_cases same : newHandle = oldHandle
  · rw [ite_eq_left same] at observed
    obtain ⟨_same, afterSame⟩ := (success_pure () () checked after).mp observed
    rw [afterSame]
  · rw [ite_eq_right same] at observed
    obtain ⟨selected, resolved, reading, writing⟩ := (success_bind _ _ _ _ _).mp observed
    have resolvedFrame := representative_frame representativeFuel uv selected checked resolved total reading
    have afterSame := (EnumerationDriver.modify_success _ resolved after).mp writing
    rw [afterSame]
    exact resolvedFrame.recursionAncestry

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


/-- Every retained cache of the valid actual prefix has the original per-slot recursion histories. -/
theorem prefix_recursion_ancestry
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (total : UnionFind.Total before.core.representatives)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query)) :
    match runPrefix holeKey fits admits graph templates stop order metadata fuel fuel fuel fuel fuel fuel
        uv caller before memos.query with
    | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
        after.core.recursionAncestry = before.core.recursionAncestry
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
      have readFrame := (getValue_frame fuel uv before.core readAfter _ total readSuccess).1
      have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap fuel uv oldHandle scs) readAfter true cached.core := by
        rw [Success, core, checking]
        exact List.mem_singleton_self _
      have checkedHistories := checkRepeated_recursion_ancestry caller.checked.native.machine.heap
        fuel uv oldHandle scs readAfter cached.core true (readFrame.total total) checkSuccess
      exact checkedHistories.trans readFrame.recursionAncestry
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
            have readFrame := (getValue_frame fuel uv before.core readAfter _ total readSuccess).1
            have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
                caller.checked.native.machine.heap fuel uv oldHandle scs) readAfter false checked := by
              rw [Success, checking]
              exact List.mem_singleton_self _
            have checkedFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
              caller.checked.native.machine.heap fuel uv oldHandle scs readAfter checked
              (readFrame.total total) checkSuccess
            have afterHistories := prepared_nonempty_recursion_ancestry holeKey fits admits metadata
              fuel fuel uv oldHandle newHandle scs oldValue value caller.checked.native.machine.heap heap
              selectedAction checked after.core (checkedFrame.total (readFrame.total total)) narrowed
              nonempty encoded selectedPrepared actionSuccess
            exact afterHistories.trans (checkedFrame.recursionAncestry.trans readFrame.recursionAncestry)

end MicroCFTA.SourcePruningEnumerationSelectedStep
