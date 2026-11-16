import MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets
import MicroCFTA.SourcePruningEnumerationSharedEagerNoneDispatch
import MicroCFTA.SourcePruningEnumerationSharedEagerNoneCachedWriters
import MicroCFTA.SourcePruningEnumerationSharedTerminalProper
import MicroCFTA.SourcePruningEnumerationSharedChildProper

set_option autoImplicit false
namespace MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Native" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" α => List (Except EnumerationState.Error (α × Core))
variable {width : Nat}
local notation "Fault" => SourceEqualityNativeDemand.Outcome width Node ⊕
  SourcePruningEnumerationSharedEnabledEmpty.Outcome width
local notation "CoreResult" => Except Fault (Option (Raw Unit)) × Caller width × Queries × Core
attribute [local instance] SourcePruningEnumerationTerminalPrefix.terminalPrefixMonadList
  SourcePruningEnumerationTerminalPrefix.terminalPrefixLawfulMonadList

private def RawNone {α : Type} (raw : Raw α) : Prop :=
  ∀ state ∈ rawCores raw, NoneBucketsEmpty state

private def ResultNone (observed : CoreResult) : Prop :=
  NoneBucketsEmpty observed.2.2.2 ∧ match observed.1 with
    | .ok (some raw) => RawNone raw
    | _ => True

private theorem raw_single {α : Type} (value : α) (state : Core)
    (initial : NoneBucketsEmpty state) : RawNone [.ok (value, state)] := by
  intro current member
  simp only [rawCores, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_singleton] at member
  subst current
  exact initial

private theorem raw_from_success {α : Type} (action : EnumerateM Symbol Constraint α) (before : Core)
    (each : ∀ value after, Success action before value after → NoneBucketsEmpty after) :
    RawNone (ExceptT.run (action before)) := by
  intro current member
  obtain ⟨row, rawMember, selected⟩ := List.mem_flatMap.mp member
  cases row with
  | error fault => cases selected
  | ok payload =>
      obtain ⟨value, after⟩ := payload
      have same : current = after := List.mem_singleton.mp selected
      subst current
      exact each value after rawMember

private theorem some_set_none (before : Core) (target handle : Nat) (bucket : List Suspended)
    (initial : NoneBucketsEmpty before) :
    NoneBucketsEmpty {before with values := before.values.set target (.unenumerated (some handle) bucket)} := by
  intro uv scs stored
  rcases List.mem_or_eq_of_mem_set (List.mem_of_getElem? stored) with retained | replaced
  · obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp retained
    exact initial index scs found
  · cases replaced

private theorem shape_single {α : Type} (raw : Raw α) (value : α) (after : Core)
    (member : Except.ok (value, after) ∈ raw)
    (shape : raw = [] ∨ ∃ row, raw = [row]) : raw = [.ok (value, after)] := by
  rcases shape with empty | ⟨row, singleton⟩
  · rw [empty] at member
    cases member
  · rw [singleton] at member ⊢
    rw [← List.mem_singleton.mp member]

private theorem optional_shape (source target : Nat) (node : Option Nat)
    (left right : List Suspended) (before : Core) :
    ExceptT.run (SourcePruningEnumerationDispatch.finishOptional source target node left right before) = [] ∨
      ∃ row, ExceptT.run (SourcePruningEnumerationDispatch.finishOptional source target node left right before) = [row] := by
  unfold SourcePruningEnumerationDispatch.finishOptional
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

private theorem assimilate_shape (source target handle : Nat) (left right : List Suspended)
    (value : Node) (before : Core) :
    ExceptT.run (SourcePruningEnumerationAssimilation.finish source target handle left right value before) = [] ∨
      ∃ row, ExceptT.run (SourcePruningEnumerationAssimilation.finish source target handle left right value before) = [row] := by
  cases value <;> first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩

private theorem dispatch_shape
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (n p h : Nat) (caller : Caller width) (before : Core)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol Constraint Unit)
    (reached : Caller width) (saved : Queries)
    (selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty n p h
      caller before source target queries = (.ok (some action), reached, saved)) :
    ExceptT.run (action before) = [] ∨ ∃ row, ExceptT.run (action before) = [row] := by
  by_cases same : source = target
  · simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_left same, Id.run, pure,
      Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
    obtain ⟨rfl, rfl, rfl⟩ := selected
    exact Or.inr ⟨_, rfl⟩
  · cases sourceStored : before.values[source]? with
    | none => simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored] at selected
    | some sourceValue =>
      cases sourceValue with
      | eliminated =>
        simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, Id.run, pure,
          Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
        obtain ⟨rfl, rfl, rfl⟩ := selected
        exact Or.inr ⟨_, rfl⟩
      | enumerated fragment =>
        cases targetStored : before.values[target]? with
        | none => simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored] at selected
        | some targetValue =>
          simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
            Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
          obtain ⟨rfl, rfl, rfl⟩ := selected
          exact Or.inr ⟨_, rfl⟩
      | unenumerated sourceNode sourceScs =>
        cases targetStored : before.values[target]? with
        | none => simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored] at selected
        | some targetValue =>
          cases targetValue with
          | eliminated =>
            simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
              Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
            obtain ⟨rfl, rfl, rfl⟩ := selected
            exact Or.inr ⟨_, rfl⟩
          | enumerated fragment =>
            simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
              Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
            obtain ⟨rfl, rfl, rfl⟩ := selected
            exact Or.inr ⟨_, rfl⟩
          | unenumerated targetNode targetScs =>
            cases sourceNodeSame : sourceNode with
            | none =>
              subst sourceNode
              simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
              obtain ⟨rfl, rfl, rfl⟩ := selected
              exact optional_shape _ _ _ _ _ _
            | some sourceHandle =>
              subst sourceNode
              cases targetNodeSame : targetNode with
              | none =>
                subst targetNode
                simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                  Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
                obtain ⟨rfl, rfl, rfl⟩ := selected
                exact optional_shape _ _ _ _ _ _
              | some targetHandle =>
                subst targetNode
                cases leftDecoded : SourcePruningEnumerationNodes.lookupNode caller.checked.native.machine.heap sourceHandle with
                | none => simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored, leftDecoded] at selected
                | some left =>
                  cases rightDecoded : SourcePruningEnumerationNodes.lookupNode caller.checked.native.machine.heap targetHandle with
                  | none => simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded] at selected
                  | some right =>
                    cases native : SourceEqualityNativeDemand.execute n
                        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) caller.checked with
                    | yielded control checkedAfter =>
                      simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded, native] at selected
                    | failed nativeFailure checkedAfter =>
                      simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded, native] at selected
                    | constraintError message checkedAfter =>
                      simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded, native] at selected
                    | blocked reason control checkedAfter =>
                      simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded, native] at selected
                    | done query queried =>
                      rcases phase : (if checkEmpty then
                        SourcePruningEnumerationSharedEnabledEmpty.check p h query queried caller.fourth queries
                        else (.skipped queried caller.fourth, queries)) with ⟨worker, workerQueries⟩
                      cases phaseDone : worker.completed with
                      | none =>
                        simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored,
                          leftDecoded, rightDecoded, native, SourcePruningEnumerationSharedDispatch.afterQuery,
                          phase, phaseDone, Except.mapError] at selected
                      | some answer =>
                        cases encoded : SourcePruningEnumerationNodes.encodeNode (if answer then (.empty : Node) else query) with
                        | none =>
                          simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored, leftDecoded,
                            rightDecoded, native, SourcePruningEnumerationSharedDispatch.afterQuery, phase, phaseDone, encoded, Except.mapError] at selected
                        | some handle =>
                          simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                            leftDecoded, rightDecoded, native, SourcePruningEnumerationSharedDispatch.afterQuery, phase, phaseDone,
                            encoded, Option.map_some, Except.mapError, Id.run, pure,
                            Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
                          obtain ⟨rfl, rfl, rfl⟩ := selected
                          exact assimilate_shape _ _ _ _ _ _ _

private theorem dispatch_all
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (n p h : Nat) (caller : Caller width) (before : Core)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol Constraint Unit)
    (reached : Caller width) (saved : Queries) (initial : NoneBucketsEmpty before)
    (selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty n p h
      caller before source target queries = (.ok (some action), reached, saved)) :
    RawNone (ExceptT.run (action before)) := by
  apply raw_from_success
  intro token after completed
  cases token
  exact SourcePruningEnumerationSharedEagerNoneDispatch.dispatch_none_buckets
    checkEmpty n p h caller before source target queries action reached saved after initial selected
    (shape_single _ () after completed (dispatch_shape checkEmpty n p h caller before source target queries action reached saved selected))

private theorem prefix_none (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (before after : Core)
    (recorded : List Nat) (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (initial : NoneBucketsEmpty before)
    (actual : Success (SourcePruningEnumerationTerminalPrefix.run fuel first rest waiting)
      before (recorded, winner, moved) after) : NoneBucketsEmpty after := by
  unfold SourcePruningEnumerationTerminalPrefix.run at actual
  obtain ⟨actualRecorded, scanned, scanning, continued⟩ := (success_bind _ _ _ _ _).mp actual
  have scannedGood := mapM_invariant (fun sc => representative fuel sc.var) NoneBucketsEmpty (first :: rest)
    (fun sc _ previous result next valid step => by
      obtain ⟨found, _, _, rfl⟩ := (representative_success fuel sc.var previous next result).mp step
      exact valid) before scanned actualRecorded initial scanning
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  have unitedGood := forM_invariant (fun sc => unionVariables fuel first.var sc.var) NoneBucketsEmpty rest
    (fun sc _ previous next valid step => by
      obtain ⟨forest, _, rfl⟩ := (unionVariables_success fuel first.var sc.var previous next).mp step
      exact valid) scanned united scannedGood unions
  obtain ⟨actualWinner, resolved, resolution, final⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨found, _, _, rfl⟩ := (representative_success fuel first.var united resolved actualWinner).mp resolution
  obtain ⟨_same, rfl⟩ := (success_pure _ _ _ _).mp final
  exact unitedGood

private theorem incoming_finish_none (target handle : Nat) (incomingScs oldScs : List Suspended)
    (replacement : Node) (before : Core) (initial : NoneBucketsEmpty before) :
    RawNone (ExceptT.run (SourcePruningEnumerationIncomingNode.finish target handle incomingScs oldScs replacement before)) := by
  let written : Core := {before with
    values := before.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
    recursionAncestry := fun other => if other = target then
      (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
      else before.recursionAncestry other}
  have good : NoneBucketsEmpty written := some_set_none before target handle (incomingScs ++ oldScs) initial
  have rawRun : ExceptT.run (SourcePruningEnumerationIncomingNode.finish target handle incomingScs oldScs replacement before) =
      match replacement with | .empty => [] | _ => [.ok ((), written)] := by
    cases replacement <;> rfl
  rw [rawRun]
  split
  · intro state impossible
    cases impossible
  · exact raw_single () written good

private theorem incoming_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h : Nat) (caller : Caller width) (before : Core)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (initial : NoneBucketsEmpty before) :
    ResultNone (SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h caller before target incoming incomingScs queries) := by
  generalize observedEq : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h caller before target incoming incomingScs queries = observed
  obtain ⟨result, reached, saved, read⟩ := observed
  unfold ResultNone
  dsimp only
  unfold SourcePruningEnumerationSharedIncomingNode.run at observedEq
  split at observedEq
  next =>
    simp only [Prod.mk.injEq] at observedEq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := observedEq
    refine ⟨initial, ?_⟩
    intro state impossible
    simp only [rawCores, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.not_mem_nil] at impossible
  next =>
    repeat' first
      | solve
        | have readSame := congrArg (fun observed : CoreResult => observed.2.2.2) observedEq
          have resultSame := congrArg Prod.fst observedEq
          dsimp only at readSame resultSame
          constructor
          · rw [← readSame]
            change NoneBucketsEmpty before
            exact initial
          · rw [← resultSame]
            first
            | trivial
            | exact incoming_finish_none _ _ _ _ _ _ (by change NoneBucketsEmpty before; exact initial)
            | intro state impossible
              simp only [rawCores, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.not_mem_nil] at impossible
      | split at observedEq
      | (dsimp only at observedEq; split at observedEq)

open SourcePruningEnumerationSharedCachedTerminal (rawFold fold cachedAdapter incomingCacheAdapter)

private theorem raw_fold_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (n p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Core) (target : Nat) (queries : Queries)
    (initial : NoneBucketsEmpty before) :
    ResultNone (rawFold checkEmpty n p h sources caller before target queries) := by
  induction sources generalizing caller before queries with
  | nil => exact ⟨initial, raw_single () before initial⟩
  | cons source rest ih =>
      rw [rawFold]
      generalize selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty n p h
        caller before source target queries = observed
      obtain ⟨result, reached, saved⟩ := observed
      cases result with
      | error fault => exact ⟨initial, True.intro⟩
      | ok possible =>
          cases possible with
          | none => exact ⟨initial, True.intro⟩
          | some action =>
              have all := dispatch_all checkEmpty n p h caller before source target queries action reached saved initial selected
              dsimp only
              split
              next middle actual =>
                apply ih reached middle saved
                exact all middle (by rw [actual]; exact List.mem_singleton_self _)
              next other => exact ⟨initial, all⟩

private theorem recovered_none
    {heap : Native} {before after : Cached} {source target : Nat} {returned : Core}
    (valid : NoneBucketsEmpty returned)
    (recovered : (returned.values[target]?).bind (fun value =>
      (SourcePruningEnumerationNativeIndex.candidate heap value).map (fun flag =>
        (⟨returned, (fun slot => if slot = source then false else
          if slot = target then flag else before.expandable slot), before.waiting⟩ : Cached))) = some after) :
    NoneBucketsEmpty after.core := by
  obtain ⟨value, _stored, classified⟩ := Option.bind_eq_some_iff.mp recovered
  obtain ⟨flag, _classified, same⟩ := Option.map_eq_some_iff.mp classified
  subst after
  exact valid
private theorem cached_adapt_none
    {heap : InternedConstructorTemplates.State Symbol Constraint} {before after : Cached}
    {source target : Nat} {raw : Raw Unit} (valid : NoneBucketsEmpty before.core)
    (rows : ∀ returned, raw = [.ok ((), returned)] → NoneBucketsEmpty returned)
    (adapted : SourcePruningEnumerationCachedAdapter.adapt heap before source target raw = some after) : NoneBucketsEmpty after.core := by
  cases raw with
  | nil =>
      simp only [SourcePruningEnumerationCachedAdapter.adapt, Option.some.injEq] at adapted
      subst after
      exact valid
  | cons row rest =>
      cases row with
      | error fault => simp only [SourcePruningEnumerationCachedAdapter.adapt] at adapted; cases adapted
      | ok payload =>
          rcases payload with ⟨ignored, returned⟩
          cases ignored
          cases rest with
          | cons next later => simp only [SourcePruningEnumerationCachedAdapter.adapt] at adapted; cases adapted
          | nil =>
              have returnedValid := rows returned rfl
              by_cases same : source = target
              · simp only [SourcePruningEnumerationCachedAdapter.adapt, same, ↓reduceIte, Option.some.injEq] at adapted
                subst after
                exact valid
              · cases stored : before.core.values[source]? with
                | none =>
                    simp only [SourcePruningEnumerationCachedAdapter.adapt, same, ↓reduceIte, stored] at adapted
                    exact recovered_none returnedValid adapted
                | some value =>
                    cases value with
                    | eliminated =>
                        simp only [SourcePruningEnumerationCachedAdapter.adapt, same, ↓reduceIte, stored, Option.some.injEq] at adapted
                        subst after
                        exact valid
                    | enumerated fragment =>
                        simp only [SourcePruningEnumerationCachedAdapter.adapt, same, ↓reduceIte, stored] at adapted
                        exact recovered_none returnedValid adapted
                    | unenumerated node scs =>
                        simp only [SourcePruningEnumerationCachedAdapter.adapt, same, ↓reduceIte, stored] at adapted
                        exact recovered_none returnedValid adapted

private theorem cached_adapter_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width) (before : Cached)
    (source target : Nat) (queries : Queries) (valid : NoneBucketsEmpty before.core) :
    (∀ returned, (cachedAdapter checkEmpty nativeFuel p h caller before source target queries).1 =
      .ok (some [.ok ((), returned)]) → NoneBucketsEmpty returned) ∧
    (∀ after, (cachedAdapter checkEmpty nativeFuel p h caller before source target queries).2.2.2 = some after →
      NoneBucketsEmpty after.core) := by
  rcases dispatched : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
    caller before.core source target queries with ⟨outcome, reachedCaller, saved⟩
  cases outcome with
  | error fault =>
      simp only [cachedAdapter, dispatched]
      constructor <;> intro after impossible <;> cases impossible
  | ok possible =>
      cases possible with
      | none =>
          simp only [cachedAdapter, dispatched]
          constructor <;> intro after impossible <;> cases impossible
      | some action =>
          simp only [cachedAdapter, dispatched]
          have rows : ∀ returned, ExceptT.run (action before.core) = [.ok ((), returned)] →
              NoneBucketsEmpty returned := by
            intro returned completed
            exact SourcePruningEnumerationSharedEagerNoneDispatch.dispatch_none_buckets checkEmpty nativeFuel p h
              caller before.core source target queries action reachedCaller saved returned
              valid dispatched completed
          constructor
          · intro returned same
            exact rows returned (Option.some.inj (Except.ok.inj same))
          · intro after adapted
            exact cached_adapt_none valid rows adapted


private theorem fold_candidate_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries)
    (valid : NoneBucketsEmpty before.core) (after : Cached)
    (candidate : (fold checkEmpty nativeFuel p h sources caller before target queries).2 = some after) :
    NoneBucketsEmpty after.core := by
  induction sources generalizing caller before queries with
  | nil =>
      simp only [fold, Option.some.injEq] at candidate
      subst after
      exact valid
  | cons source rest ih =>
      have headProper := cached_adapter_none
        checkEmpty nativeFuel p h caller before source target queries valid
      rcases headObserved : cachedAdapter checkEmpty nativeFuel p h
        caller before source target queries with ⟨outcome, reachedCaller, saved, headCache⟩
      rw [headObserved] at headProper
      dsimp only at headProper
      cases outcome with
      | error fault => simp only [fold, headObserved] at candidate; cases candidate
      | ok possible =>
          cases possible with
          | none => simp only [fold, headObserved] at candidate; cases candidate
          | some raw =>
              cases raw with
              | nil =>
                  simp only [fold, headObserved] at candidate
                  exact headProper.2 after candidate
              | cons row tail =>
                  cases row with
                  | error fault =>
                      simp only [fold, headObserved] at candidate
                      exact headProper.2 after candidate
                  | ok payload =>
                      rcases payload with ⟨ignored, core⟩
                      cases ignored
                      cases tail with
                      | cons next later =>
                          simp only [fold, headObserved] at candidate
                          exact headProper.2 after candidate
                      | nil =>
                          have coreProper := headProper.1 core rfl
                          cases headCache with
                          | none => simp only [fold, headObserved] at candidate; cases candidate
                          | some recovered =>
                              simp only [fold, headObserved] at candidate
                              exact ih reachedCaller (EnumerationExpandableIndex.frame core recovered)
                                saved coreProper candidate


private theorem incoming_adapt_none
    {heap : Native} {indexFuel target : Nat} {incomingScs : List Suspended}
    {before after : Cached} {read : Core} {raw : Raw Unit}
    (readValid : NoneBucketsEmpty read)
    (rows : ∀ returned, raw = [.ok ((), returned)] → NoneBucketsEmpty returned)
    (adapted : SourcePruningEnumerationIncomingCacheAdapter.adapt heap indexFuel target incomingScs before read raw = some after) :
    NoneBucketsEmpty after.core := by
  cases raw with
  | nil =>
      simp only [SourcePruningEnumerationIncomingCacheAdapter.adapt] at adapted
      split at adapted
      · rename_i oldNode oldScs stored
        simp only [Option.map_eq_some_iff] at adapted
        obtain ⟨written, _written, same⟩ := adapted
        subst after
        exact some_set_none read target 0 (incomingScs ++ oldScs) readValid
      · cases adapted
  | cons row rest =>
      cases row with
      | error fault => simp only [SourcePruningEnumerationIncomingCacheAdapter.adapt] at adapted; cases adapted
      | ok payload =>
          obtain ⟨⟨⟩, returned⟩ := payload
          cases rest with
          | nil =>
              have coreSame := SourcePruningEnumerationIncomingCacheAdapter.adapt_singleton_core
                heap indexFuel target incomingScs before after read returned adapted
              rw [coreSame]
              exact rows returned rfl
          | cons next later => simp only [SourcePruningEnumerationIncomingCacheAdapter.adapt] at adapted; cases adapted

private theorem incoming_cache_candidate_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (caller : Caller width) (before : Cached)
    (target : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries)
    (initial : NoneBucketsEmpty before.core) (after : Cached)
    (candidate : (incomingCacheAdapter checkEmpty r n p h k caller before target incoming incomingScs queries).2 = some after) :
    NoneBucketsEmpty after.core := by
  have fields := incoming_none checkEmpty r n p h caller before.core target incoming incomingScs queries initial
  unfold incomingCacheAdapter at candidate
  generalize original : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
    caller before.core target incoming incomingScs queries = observed at fields candidate
  obtain ⟨result, reached, saved, read⟩ := observed
  dsimp only at candidate
  cases result with
  | error fault => cases candidate
  | ok payload =>
      cases payload with
      | none => cases candidate
      | some raw =>
          apply incoming_adapt_none fields.1 ?_ candidate
          intro returned rawSame
          exact fields.2 returned (by rw [rawSame]; exact List.mem_singleton_self _)

private theorem states_single (state : Core) (initial : NoneBucketsEmpty state) :
    ∀ current ∈ [state], NoneBucketsEmpty current := by
  intro current member
  have same := List.mem_singleton.mp member
  subst current
  exact initial

private theorem states_cons {α : Type} (state : Core) (raw : Raw α)
    (initial : NoneBucketsEmpty state) (all : RawNone raw) :
    ∀ current ∈ state :: rawCores raw, NoneBucketsEmpty current := by
  intro current member
  rcases List.mem_cons.mp member with same | rest
  · subst current
    exact initial
  · exact all current rest

private theorem raw_hole_none (raw : Raw Unit) (winner : Nat) (all : RawNone raw) :
    RawNone (raw.map fun row => match row with
      | .error error => .error error
      | .ok result => .ok ((Fragments.Fragment.hole winner : Fragment), result.2)) := by
  have same : rawCores (raw.map fun row => match row with
      | .error error => .error error
      | .ok result => .ok ((Fragments.Fragment.hole winner : Fragment), result.2)) = rawCores raw := by
    simp only [rawCores, List.flatMap_map]
    congr 1
    funext row
    cases row <;> rfl
  intro state member
  rw [same] at member
  exact all state member

private theorem terminal_raw_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting) (caller : Caller width) (before : Core)
    (incoming : Node) (scs : List Suspended) (queries : Queries) (initial : NoneBucketsEmpty before) :
    ∀ state ∈ childCores (SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty r n p h
      first rest waiting caller before incoming scs queries), NoneBucketsEmpty state := by
  have prefixAll : RawNone (ExceptT.run (SourcePruningEnumerationTerminalPrefix.run r first rest waiting before)) := by
    apply raw_from_success
    intro result after actual
    obtain ⟨recorded, winner, moved⟩ := result
    exact prefix_none r first rest waiting before after recorded winner moved initial actual
  unfold SourcePruningEnumerationSharedCachedTerminal.raw
  split
  next => exact states_single before initial
  next =>
    split
    next recorded winner moved joined prefixObserved =>
      have joinedGood : NoneBucketsEmpty joined := prefixAll joined (by rw [prefixObserved]; exact List.mem_singleton_self _)
      have foldGood := raw_fold_none checkEmpty n p h recorded caller joined winner queries joinedGood
      generalize foldObserved : rawFold checkEmpty n p h recorded caller joined winner queries = observed at foldGood ⊢
      obtain ⟨result, reached, saved, outer⟩ := observed
      cases result with
      | error fault => exact states_single outer foldGood.1
      | ok possible =>
          cases possible with
          | none => exact states_single outer foldGood.1
          | some raw =>
              cases raw with
              | nil => exact states_single outer foldGood.1
              | cons row tail =>
                  cases row with
                  | error fault => exact states_cons outer _ foldGood.1 foldGood.2
                  | ok payload =>
                      obtain ⟨token, folded⟩ := payload
                      cases token
                      cases tail with
                      | cons second remaining => exact states_cons outer _ foldGood.1 foldGood.2
                      | nil =>
                          dsimp only [Unit.unit]
                          have foldedGood := foldGood.2 folded (List.mem_singleton_self _)
                          have incomingGood := incoming_none checkEmpty r n p h reached folded winner incoming scs saved foldedGood
                          generalize incomingObserved : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
                            reached folded winner incoming scs saved = observed at incomingGood ⊢
                          obtain ⟨result, finalCaller, finalQueries, read⟩ := observed
                          cases result with
                          | error fault => exact states_single read incomingGood.1
                          | ok possible =>
                              cases possible with
                              | none => exact states_single read incomingGood.1
                              | some raw => exact states_cons read _ incomingGood.1 (raw_hole_none raw winner incomingGood.2)
    next => exact states_cons before _ initial prefixAll
private theorem terminal_candidate_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (first : Suspended) (rest : List Suspended)
    (caller : Caller width) (before : Cached) (incoming : Node) (incomingScs : List Suspended)
    (queries : Queries) (proper : NoneBucketsEmpty before.core)
    (after : Cached)
    (candidate : (SourcePruningEnumerationSharedCachedTerminal.run checkEmpty r n p h k first rest caller before incoming incomingScs queries).2 = some after) :
    NoneBucketsEmpty after.core := by
  unfold SourcePruningEnumerationSharedCachedTerminal.run at candidate
  split at candidate
  next empty =>
    have same : before = after := Option.some.inj candidate
    subst after
    exact proper
  next nonempty =>
    split at candidate
    next recorded winner moved joined prefixObserved =>
      have prefixSuccess : Success (SourcePruningEnumerationTerminalPrefix.run r first rest before.waiting)
          before.core (recorded, winner, moved) joined := by
        rw [Success, prefixObserved]
        exact List.mem_singleton_self _
      have joinedProper := prefix_none r first rest before.waiting
        before.core joined recorded winner moved proper prefixSuccess
      rcases foldObserved : fold checkEmpty n p h recorded
          caller ⟨joined, before.expandable, moved⟩ winner queries with
        ⟨⟨foldResult, foldCaller, foldQueries, foldOuter⟩, foldCache⟩
      rw [foldObserved] at candidate
      have foldExact := (SourcePruningEnumerationSharedCachedTerminal.fold_erase checkEmpty n p h recorded
        caller ⟨joined, before.expandable, moved⟩ winner queries).symm.trans (congrArg Prod.fst foldObserved)
      have foldFields := raw_fold_none checkEmpty n p h recorded caller joined winner queries joinedProper
      rw [foldExact] at foldFields
      have foldProper : NoneBucketsEmpty foldOuter := foldFields.1
      cases foldResult with
      | error fault => cases candidate
      | ok possible =>
        cases possible with
        | none => cases candidate
        | some raw =>
          cases raw with
          | nil =>
            apply fold_candidate_none checkEmpty n p h recorded
              caller ⟨joined, before.expandable, moved⟩ winner queries joinedProper after
            rw [foldObserved]
            exact candidate
          | cons row tail =>
            cases row with
            | error fault => cases candidate
            | ok payload =>
              rcases payload with ⟨⟨⟩, folded⟩
              cases tail with
              | cons next later => cases candidate
              | nil =>
                have foldedSame := SourcePruningEnumerationSharedCachedTerminal.rawFold_singleton_core checkEmpty n p h recorded
                  caller joined winner queries folded foldCaller foldQueries foldOuter foldExact
                have foldedProper : NoneBucketsEmpty folded := by simpa only [foldedSame] using foldProper
                cases foldCache with
                | none =>
                  dsimp only at candidate
                  rcases incomingObserved : SourcePruningEnumerationSharedIncomingNode.run checkEmpty r n p h
                      foldCaller folded winner incoming incomingScs foldQueries with
                    ⟨incomingResult, reached, saved, read⟩
                  rw [incomingObserved] at candidate
                  cases incomingResult with
                  | error fault => cases candidate
                  | ok possible => cases possible <;> cases candidate
                | some recovered =>
                  dsimp only at candidate
                  rcases incomingObserved : incomingCacheAdapter checkEmpty r n p h k
                      foldCaller (EnumerationExpandableIndex.frame folded recovered)
                      winner incoming incomingScs foldQueries with
                    ⟨⟨incomingResult, reached, saved, read⟩, incomingCache⟩
                  rw [incomingObserved] at candidate
                  cases incomingResult with
                  | error fault => cases candidate
                  | ok possible =>
                    cases possible with
                    | none => cases candidate
                    | some incomingRaw =>
                      apply incoming_cache_candidate_none checkEmpty r n p h k
                        foldCaller (EnumerationExpandableIndex.frame folded recovered) winner incoming incomingScs
                        foldQueries foldedProper after
                      rw [incomingObserved]
                      exact candidate
    next other => cases candidate



private theorem shallow_none
    (scs : List Suspended) (value : Value Symbol Constraint)
    (before after : EnumerationState.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint (Fragment)) (fragment : Fragment)
    (proper : NoneBucketsEmpty before)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs value = some action)
    (success : Success action before fragment after) : NoneBucketsEmpty after := by
  cases value with
  | empty =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, Option.some.injEq] at prepared
      rw [← prepared] at success
      exact (reject_unsuccessful before after fragment success).elim
  | reference name =>
      simp only [SourcePruningEnumerationShallowChild.prepareChild, reduceCtorEq] at prepared
  | node entry edges depth free =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true, ↓reduceIte, SourcePruningEnumerationNodes.encodeNode,
          Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, continued⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨ignored, written, writing, final⟩ := (success_bind _ _ _ _ _).mp continued
        cases ignored
        have writtenGood := some_write_none_buckets before.counter (entry.identity + 1) scs
          (allocated (some (entry.identity + 1)) before) written
          (allocated_none_buckets (some (entry.identity + 1)) before proper) writing
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment written after).mp final
        subst after
        exact writtenGood
  | union entry _ _ _ | mu entry _ _ _ =>
      by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
      · simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, ↓reduceIte, reduceCtorEq] at prepared
      · simp only [SourcePruningEnumerationShallowChild.prepareChild, terminal, Bool.false_eq_true, ↓reduceIte, SourcePruningEnumerationNodes.encodeNode,
          Option.some.injEq] at prepared
        rw [← prepared] at success
        obtain ⟨uv, allocatedAfter, allocation, final⟩ := (success_bind _ _ _ _ _).mp success
        have shape : uv = before.counter ∧ allocatedAfter = allocated (some (entry.identity + 1)) before := by
          simpa [Success, allocate_exact, ExceptT.run] using allocation
        obtain ⟨rfl, rfl⟩ := shape
        obtain ⟨_fragmentSame, afterSame⟩ :=
          (success_pure (.hole before.counter) fragment (allocated (some (entry.identity + 1)) before) after).mp final
        subst after
        exact allocated_none_buckets (some (entry.identity + 1)) before proper

private theorem shallow_rows_none
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel : Nat)
    (scs : List Suspended) (value : Value Symbol Constraint)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (rows : List (Fragment × EnumerationExpandableIndex.Cached Symbol Constraint))
    (proper : NoneBucketsEmpty before.core)
    (cached : SourcePruningEnumerationCachedPrepare.prepareChild heap fuel scs value before = some rows) :
    ∀ fragment after, (fragment, after) ∈ rows → NoneBucketsEmpty after.core := by
  have raw := SourcePruningEnumerationCachedPrepare.erase_some heap fuel scs value before rows cached
  cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs value with
  | none =>
      simp only [prepared, Option.map_none, reduceCtorEq] at raw
  | some action =>
      simp only [prepared, Option.map_some, Option.some.injEq] at raw
      intro fragment after member
      apply shallow_none scs value before.core after.core
        action fragment proper prepared
      rw [Success, raw]
      exact List.mem_map.mpr ⟨(fragment, after), member, rfl⟩


private theorem shallow_cache_none
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel : Nat)
    (scs : List Suspended) (value : Value Symbol Constraint)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (proper : NoneBucketsEmpty before.core)
    (observed : (match SourcePruningEnumerationCachedPrepare.prepareChild heap fuel scs value before with
      | some [] => some before
      | some [(_, result)] => some result
      | _ => none) = some after) : NoneBucketsEmpty after.core := by
  cases prepared : SourcePruningEnumerationCachedPrepare.prepareChild heap fuel scs value before with
  | none =>
      simp only [prepared, reduceCtorEq] at observed
  | some rows =>
      cases rows with
      | nil =>
          have same : before = after := by simpa only [prepared, Option.some.injEq] using observed
          subst after
          exact proper
      | cons row rest =>
          rcases row with ⟨fragment, reached⟩
          cases rest with
          | nil =>
              have same : reached = after := by simpa only [prepared, Option.some.injEq] using observed
              rw [← same]
              exact shallow_rows_none heap fuel scs value before [(fragment, reached)]
                proper prepared fragment reached (by simp)
          | cons row rest =>
              simp only [prepared, reduceCtorEq] at observed


private theorem child_observe_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Core) (waiting : EnumerationWaitingIndex.Waiting) (queries : Queries)
    (initial : NoneBucketsEmpty before) :
    ∀ state ∈ childCores (ChildDispatch.observe checkEmpty r n p h scs incoming caller before waiting queries),
      NoneBucketsEmpty state := by
  by_cases empty : incoming = .empty
  · simp only [ChildDispatch.observe, ite_eq_left empty]
    exact states_single before initial
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
        cases here with
        | nil =>
            simp only [ChildDispatch.observe, ite_eq_right empty, partitioned]
            cases prepared : SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) scs incoming with
            | none => exact states_single before initial
            | some action =>
                apply states_cons before _ initial
                apply raw_from_success
                intro fragment after actual
                exact shallow_none scs incoming before after action fragment initial prepared actual
        | cons first rest =>
            simp only [ChildDispatch.observe, ite_eq_right empty, partitioned]
            exact terminal_raw_none checkEmpty r n p h first rest waiting caller before incoming descendants queries initial
theorem child_none_buckets
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (initial : NoneBucketsEmpty before.core) :
    (∀ state ∈ childCores (ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries).1,
      NoneBucketsEmpty state) ∧
    ∀ after, (ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries).2 = some after →
      NoneBucketsEmpty after.core
 := by
  constructor
  · rw [ChildDispatch.erase]
    exact child_observe_none checkEmpty r n p h scs incoming caller before.core before.waiting queries initial
  · intro after candidate
    by_cases empty : incoming = .empty
    · simp only [ChildDispatch.run, ite_eq_left empty, Option.some.injEq] at candidate
      subst after
      exact initial
    · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
      | mk here descendants =>
          cases here with
          | nil =>
              apply shallow_cache_none caller.checked.native.machine.heap k scs incoming before after initial
              simp only [ChildDispatch.run, ite_eq_right empty, partitioned] at candidate
              cases cached : SourcePruningEnumerationCachedPrepare.prepareChild
                  caller.checked.native.machine.heap k scs incoming before with
              | none => simpa only [cached] using candidate
              | some rows =>
                  cases rows with
                  | nil => simpa only [cached] using candidate
                  | cons row rest =>
                      obtain ⟨fragment, reached⟩ := row
                      cases rest with
                      | nil => simpa only [cached] using candidate
                      | cons next later => simpa only [cached] using candidate
          | cons first rest =>
              apply terminal_candidate_none checkEmpty r n p h k first rest caller before incoming descendants queries initial after
              simpa only [ChildDispatch.run, ite_eq_right empty, partitioned] using candidate

end MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets
