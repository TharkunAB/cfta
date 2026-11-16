import MicroCFTA.SourcePruningEnumerationSelectedStepCompletion
import MicroCFTA.SourcePruningEnumerationRawAliasPrimitives

namespace MicroCFTA.SourcePruningEnumerationSelectedPrefixRawAliases
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationSelectedStep (runPrefix runPrefixWithNarrow)
open SourcePruningEnumerationRawAliasPrimitives
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
set_option autoImplicit false
variable {Typing Key : Type} {width : Nat}
attribute [local instance] SourcePruningEnumerationRecursion.recursionMonadList

/- Note [Selected prefix raw aliases]
Successful reads compress paths and retain each existing raw alias.
The recursion check and narrowing action use those reads and value writes.
A value write does not change the representative forest.
Both cache adapters retain the exact observed core.
Right recording is pure for every template list.
The proof follows the actual prefix observations at all six supplied fuels.
It does not need totality or a resource invariant.
-/

private theorem getValue_forward (fuel uv : Nat) (before after : Core) (value : UVarValue Symbol)
    (actual : Success (getValue fuel uv) before value after) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right := by
  obtain ⟨found, lookup, _stored, rfl⟩ := (getValue_success fuel uv before after value).mp actual
  exact findRoot_sameClass_forward fuel uv before.representatives found lookup

private theorem setValue_forest (uv : Nat) (value : UVarValue Symbol) (before after : Core)
    (actual : Success (setValue uv value) before () after) :
    after.representatives = before.representatives := by
  have shape := (EnumerationDriver.modify_success _ before after).mp actual
  simpa only using congrArg (fun state : Core => state.representatives) shape

private theorem checkRepeated_forward
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel uv handle : Nat)
    (scs : List Suspended) (before after : Core) (repeated : Bool)
    (actual : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before repeated after) :
    ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before repeated after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using actual
      exact (success_failure .unresolvedReference before after repeated impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at actual
        obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp actual
        have first := representative_sameClass_forward fuel uv root before resolved resolution
        obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, stateSame⟩ := (EnumerationDriver.get_success resolved currentState current).mp reading
        subst current currentState
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry root
        · simp only [seen, ↓reduceIte] at continued
          obtain ⟨token, cleared, written, returned⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          obtain ⟨_same, afterSame⟩ := (success_pure true repeated cleared after).mp returned
          subst after
          have forest := setValue_forest root (.unenumerated (some handle) []) resolved cleared written
          intro left right same
          rw [forest]
          exact first left right same
        · have returned : Success (pure false) resolved repeated after := by
            simpa only [seen, ↓reduceIte] using continued
          obtain ⟨_same, afterSame⟩ := (success_pure false repeated resolved after).mp returned
          subst after
          exact first
      · have returned : Success (pure false) before repeated after := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary,
            Bool.false_eq_true, ↓reduceIte] using actual
        obtain ⟨_same, afterSame⟩ := (success_pure false repeated before after).mp returned
        subst after
        exact fun _ _ same => same

variable [DecidableEq (EdgeKey Symbol Constraint)]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

private theorem prepared_action_forward
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (nativeFuel representativeFuel uv oldHandle : Nat)
    (scs : List Suspended) (oldValue value : Node)
    (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit) (checked after : Core)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel
      representativeFuel uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (actual : Success action checked () after) :
    ∀ left right, UnionFind.SameClass checked.representatives left right →
      UnionFind.SameClass after.representatives left right := by
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
          exact actual
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
      have actionShape := SourcePruningEnumerationSelectedStep.prepared_action holeKey fits admits metadata
        nativeFuel representativeFuel uv oldHandle newHandle scs oldValue value heap nextHeap
        actualNarrowed nonempty encoded
      rw [selectedPrepared] at actionShape
      have actionSame : action =
          (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
            else representative representativeFuel uv >>= fun selected =>
              setValue selected (.unenumerated (some newHandle) scs)) :=
        Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj actionShape).1).2
      rw [actionSame] at actual
      by_cases same : newHandle = oldHandle
      · rw [ite_eq_left same] at actual
        obtain ⟨_same, afterSame⟩ := (success_pure () () checked after).mp actual
        subst after
        exact fun _ _ original => original
      · rw [ite_eq_right same] at actual
        obtain ⟨selected, resolved, reading, writing⟩ := (success_bind _ _ _ _ _).mp actual
        have first := representative_sameClass_forward representativeFuel uv selected checked resolved reading
        have forest := setValue_forest selected (.unenumerated (some newHandle) scs) resolved after writing
        intro left right original
        rw [forest]
        exact first left right original

theorem runPrefix_sameClass_forward
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries) :
    match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries with
    | .stopped _ _ => True
    | .parked checked candidate _ =>
        (∀ left right, UnionFind.SameClass before.core.representatives left right →
          UnionFind.SameClass checked.representatives left right) ∧
        ∀ after, candidate = some after → ∀ left right,
          UnionFind.SameClass before.core.representatives left right →
            UnionFind.SameClass after.core.representatives left right
    | .narrowed checked _ _ _ _ candidate _ _ =>
        (∀ left right, UnionFind.SameClass before.core.representatives left right →
          UnionFind.SameClass checked.representatives left right) ∧
        ∀ after, candidate = some after → ∀ left right,
          UnionFind.SameClass before.core.representatives left right →
            UnionFind.SameClass after.core.representatives left right := by
  classical
  by_cases readable : ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
      ExceptT.run (getValue readFuel uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]
  · obtain ⟨oldHandle, scs, readAfter, reading⟩ := readable
    have readSuccess : Success (getValue readFuel uv) before.core
        (.unenumerated (some oldHandle) scs) readAfter := by
      rw [Success, reading]
      exact List.mem_singleton_self _
    have readForward := getValue_forward readFuel uv before.core readAfter
      (.unenumerated (some oldHandle) scs) readSuccess
    by_cases checkedResult : ∃ (repeated : Bool) (checked : Core),
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter) = [.ok (repeated, checked)]
    · obtain ⟨repeated, checked, checking⟩ := checkedResult
      have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
          caller.checked.native.machine.heap checkFuel uv oldHandle scs) readAfter repeated checked := by
        rw [Success, checking]
        exact List.mem_singleton_self _
      have checkForward := checkRepeated_forward caller.checked.native.machine.heap
        checkFuel uv oldHandle scs readAfter checked repeated checkSuccess
      have checkedForward : ∀ left right, UnionFind.SameClass before.core.representatives left right →
          UnionFind.SameClass checked.representatives left right :=
        fun left right same => checkForward left right (readForward left right same)
      cases repeated with
      | true =>
          unfold runPrefix runPrefixWithNarrow
          simp only [reading, checking]
          refine ⟨checkedForward, ?_⟩
          intro after adapted
          rw [SourcePruningEnumerationParkedRestart.adapt_core caller.checked.native.machine.heap
            indexFuel uv oldHandle scs before after checked adapted]
          exact checkedForward
      | false =>
          have noCandidate :
              (∀ left right, UnionFind.SameClass before.core.representatives left right →
                UnionFind.SameClass checked.representatives left right) ∧
              ∀ after, (none : Option Cached) = some after → ∀ left right,
                UnionFind.SameClass before.core.representatives left right →
                  UnionFind.SameClass after.core.representatives left right := by
            refine ⟨checkedForward, ?_⟩
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
                  nativeFuel representativeFuel uv oldHandle scs oldValue caller.checked.native.machine.heap with
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
                        have actionForward := prepared_action_forward holeKey fits admits metadata
                          nativeFuel representativeFuel uv oldHandle scs oldValue narrowedValue
                          caller.checked.native.machine.heap heap action checked observed preparedEq actionSuccess
                        have wholeForward : ∀ left right, UnionFind.SameClass before.core.representatives left right →
                            UnionFind.SameClass observed.representatives left right :=
                          fun left right same => actionForward left right (checkedForward left right same)
                        simp only [raw]
                        cases encoded : encodeNode narrowedValue with
                        | none =>
                            exact noCandidate
                        | some newHandle =>
                            dsimp only
                            cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap indexFuel
                                uv oldHandle newHandle scs before observed with
                            | none =>
                                exact noCandidate
                            | some attached =>
                                dsimp only
                                have attachedCore := SourcePruningEnumerationNarrowAdapter.adapt_core heap
                                  indexFuel uv oldHandle newHandle scs before attached observed adapted
                                have attachedForward : ∀ left right,
                                    UnionFind.SameClass before.core.representatives left right →
                                      UnionFind.SameClass attached.core.representatives left right := by
                                  rw [attachedCore]
                                  exact wholeForward
                                have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
                                    graph templates callbackFuel metadata uv (.inr newHandle) attached.core) =
                                    [.ok ((false, metadata), attached.core)] := by
                                  rw [SourcePruningRecordTypes.recordTypes_inr]
                                  rfl
                                simp only [recorded]
                                refine ⟨checkedForward, ?_⟩
                                intro after candidate
                                cases candidate
                                exact attachedForward
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
          readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries =
          .stopped (ExceptT.run (getValue readFuel uv before.core))
            (some (ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
              caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter))) := by
        unfold runPrefix runPrefixWithNarrow
        simp only [reading]
        split
        · exact (checkedResult ⟨true, _, by assumption⟩).elim
        · exact (checkedResult ⟨false, _, by assumption⟩).elim
        · rfl
      simp only [stopped]
  · have stopped : runPrefix holeKey fits admits graph templates stop order metadata
        readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries =
        .stopped (ExceptT.run (getValue readFuel uv before.core)) none := by
      unfold runPrefix runPrefixWithNarrow
      dsimp only
      split
      · exact (readable ⟨_, _, _, by assumption⟩).elim
      · rfl
    simp only [stopped]

end MicroCFTA.SourcePruningEnumerationSelectedPrefixRawAliases
