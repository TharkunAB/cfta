import MicroCFTA.SourcePruningEnumerationPathSelectedRaw
import MicroCFTA.SourcePruningEnumerationPathAssimilation
import MicroCFTA.SourcePruningEnumerationPathFold

/-!
# Paths in every raw dispatcher and fold row

Each actual writer uses the original stored buckets.
The fold preserves paths before it selects a singleton continuation.
-/
namespace MicroCFTA.SourcePruningEnumerationPathFoldRaw
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationPathTransport SourcePruningEnumerationPathSelectedRaw
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat} {P : EqualityTrie.Path → Prop}
local notation "Core" => EnumerationState.State Symbol EnumGuard

private theorem optional_raw_paths
    (before : Core) (source target : Nat) (sourceNode targetNode node : Option Nat)
    (sourceScs targetScs : List Suspended) (paths : StatePaths P before)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs)) :
    RawPaths P (ExceptT.run
      (SourcePruningEnumerationDispatch.finishOptional source target node sourceScs targetScs before)) := by
  intro result after member
  change Except.ok (result, after) ∈ (if node = some 0 then [] else
    [.ok ((), assimilated before target source (.unenumerated node (sourceScs ++ targetScs)))]) at member
  by_cases empty : node = some 0
  · rw [ite_eq_left empty] at member
    cases member
  · rw [ite_eq_right empty] at member
    have same := List.mem_singleton.mp member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
    exact SourcePruningEnumerationDispatch.assimilated_paths before source target sourceNode targetNode node
      sourceScs targetScs paths sourceStored targetStored

private theorem assimilation_raw_paths
    (before : Core) (source target handle : Nat) (sourceNode targetNode : Option Nat)
    (sourceScs targetScs : List Suspended) (replacement : Node) (paths : StatePaths P before)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs)) :
    RawPaths P (ExceptT.run
      (SourcePruningEnumerationAssimilation.finish source target handle sourceScs targetScs replacement before)) := by
  have rawRun : ExceptT.run
      (SourcePruningEnumerationAssimilation.finish source target handle sourceScs targetScs replacement before) =
      match replacement with
      | .empty => []
      | _ => [.ok ((), assimilated before target source
          (.unenumerated (some handle) (sourceScs ++ targetScs)))] := by
    cases replacement <;> rfl
  intro result after member
  rw [rawRun] at member
  split at member
  · simp at member
  · have same := List.mem_singleton.mp member
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
    exact SourcePruningEnumerationDispatch.assimilated_paths before source target sourceNode targetNode (some handle)
      sourceScs targetScs paths sourceStored targetStored

private theorem noop_raw_paths (before : Core) (paths : StatePaths P before) :
    RawPaths P [Except.ok ((), before)] := by
  intro result after member
  have same := List.mem_singleton.mp member
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  exact paths

private theorem failure_raw_paths (before : Core) (error : EnumerationState.Error) :
    RawPaths P (ExceptT.run (EnumerationState.failure (α := Unit) error before)) := by
  intro result after member
  change Except.ok (result, after) ∈ [Except.error error] at member
  simp at member

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem dispatch_selected_raw_paths
    (checkEmpty : Bool) (nativeFuel p h : Nat) (beforeCaller : Caller width) (before : Core)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries) (paths : StatePaths P before)
    (selected : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries)) :
    RawPaths P (ExceptT.run (action before)) := by
  by_cases same : source = target
  · simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_left same, Id.run, pure,
      Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
    rcases selected with ⟨rfl, rfl, rfl⟩
    exact noop_raw_paths before paths
  · cases sourceStored : before.values[source]? with
    | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored] at selected
    | some sourceValue =>
      cases sourceValue with
      | eliminated =>
        simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, Id.run, pure,
          Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
        rcases selected with ⟨rfl, rfl, rfl⟩
        exact noop_raw_paths before paths
      | enumerated sourceFragment =>
        cases targetStored : before.values[target]? with
        | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored] at selected
        | some targetValue =>
          simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
            Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
          rcases selected with ⟨rfl, rfl, rfl⟩
          exact failure_raw_paths before EnumerationState.Error.invalidIntersection
      | unenumerated sourceNode sourceScs =>
        cases targetStored : before.values[target]? with
        | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored] at selected
        | some targetValue =>
          cases targetValue with
          | eliminated =>
            simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
              Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
            rcases selected with ⟨rfl, rfl, rfl⟩
            exact failure_raw_paths before EnumerationState.Error.invalidIntersection
          | enumerated targetFragment =>
            simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
              Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
            rcases selected with ⟨rfl, rfl, rfl⟩
            exact failure_raw_paths before EnumerationState.Error.invalidIntersection
          | unenumerated targetNode targetScs =>
            cases sourceNodeSame : sourceNode with
            | none =>
              subst sourceNode
              simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
              rcases selected with ⟨rfl, rfl, rfl⟩
              exact optional_raw_paths before source target none targetNode targetNode sourceScs targetScs
                paths sourceStored targetStored
            | some sourceHandle =>
              subst sourceNode
              cases targetNodeSame : targetNode with
              | none =>
                subst targetNode
                simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                  Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
                rcases selected with ⟨rfl, rfl, rfl⟩
                exact optional_raw_paths before source target (some sourceHandle) none (some sourceHandle)
                  sourceScs targetScs paths sourceStored targetStored
              | some targetHandle =>
                subst targetNode
                cases leftDecoded : SourcePruningEnumerationNodes.lookupNode beforeCaller.checked.native.machine.heap sourceHandle with
                | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded] at selected
                | some left =>
                  cases rightDecoded : SourcePruningEnumerationNodes.lookupNode beforeCaller.checked.native.machine.heap targetHandle with
                  | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded] at selected
                  | some right =>
                    cases native : SourceEqualityNativeDemand.execute nativeFuel
                        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked with
                    | yielded control checkedAfter =>
                      simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded, native] at selected
                    | failed nativeFailure checkedAfter =>
                      simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded, native] at selected
                    | constraintError message checkedAfter =>
                      simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded, native] at selected
                    | blocked reason control checkedAfter =>
                      simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded, native] at selected
                    | done query queried =>
                      rcases phase : (if checkEmpty then
                        SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                        else (.done false queried beforeCaller.fourth, queries)) with ⟨worker, workerQueries⟩
                      cases workerSame : worker with
                      | failed fault checkedAfter saved =>
                        subst worker
                        simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded,
                          rightDecoded, native, SourcePruningEnumerationDispatch.afterQuery, phase, Except.mapError] at selected
                      | done answer checkedAfter saved =>
                        subst worker
                        cases encoded : SourcePruningEnumerationNodes.encodeNode (if answer then (.empty : Node) else query) with
                        | none =>
                          simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored, leftDecoded,
                            rightDecoded, native, SourcePruningEnumerationDispatch.afterQuery, phase, encoded, Except.mapError] at selected
                        | some handle =>
                          simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                            leftDecoded, rightDecoded, native, SourcePruningEnumerationDispatch.afterQuery, phase,
                            encoded, Option.map_some, Except.mapError, Id.run, pure,
                            Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
                          rcases selected with ⟨rfl, rfl, rfl⟩
                          exact assimilation_raw_paths before source target handle (some sourceHandle) (some targetHandle)
                            sourceScs targetScs (if answer then (.empty : Node) else query) paths sourceStored targetStored

/-- Every successful raw row of an actual dispatcher action retains the original paths. -/
theorem dispatch_raw_paths
    (checkEmpty : Bool) (n p h : Nat) (caller : Caller width) (before : Core)
    (source target : Nat) (queries : Queries) (paths : StatePaths P before) :
    match (SourcePruningEnumerationDispatch.dispatch checkEmpty n p h caller before source target queries).1 with
    | .ok (some action) => RawPaths P (ExceptT.run (action before))
    | _ => True := by
  generalize observedEq : SourcePruningEnumerationDispatch.dispatch checkEmpty n p h
    caller before source target queries = observed
  obtain ⟨result, reached, saved⟩ := observed
  dsimp only
  cases result with
  | error fault => trivial
  | ok maybeAction =>
      cases maybeAction with
      | none => trivial
      | some action =>
          exact dispatch_selected_raw_paths checkEmpty n p h caller before source target queries action
            reached saved paths observedEq

/-- The actual fold retains paths at every successful raw row, including stopped raw lists. -/
theorem fold_raw_paths
    (checkEmpty : Bool) (n p h : Nat) (sources : List Nat) (caller : Caller width) (before : Core)
    (target : Nat) (queries : Queries) (paths : StatePaths P before) :
    match (SourcePruningEnumerationFold.run checkEmpty n p h sources caller before target queries).1 with
    | .ok (some raw) => RawPaths P raw
    | _ => True := by
  induction sources generalizing caller before queries with
  | nil =>
      intro result after member
      simp only [List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at member
      rcases member with ⟨_, rfl⟩
      exact paths
  | cons source rest ih =>
      have step := dispatch_raw_paths checkEmpty n p h caller before source target queries paths
      cases dispatched : SourcePruningEnumerationDispatch.dispatch checkEmpty n p h
          caller before source target queries with
      | mk result endpoint =>
          rcases endpoint with ⟨reached, saved⟩
          rw [dispatched] at step
          simp only [SourcePruningEnumerationFold.run, dispatched]
          cases result with
          | error fault => trivial
          | ok action =>
              cases action with
              | none => trivial
              | some action =>
                  dsimp only at step ⊢
                  cases rawEq : ExceptT.run (action before) with
                  | nil => simpa only [rawEq] using step
                  | cons row rows =>
                      cases row with
                      | error fault => simpa only [rawEq] using step
                      | ok pair =>
                          rcases pair with ⟨resultUnit, after⟩
                          cases resultUnit
                          cases rows with
                          | cons second rest => simpa only [rawEq] using step
                          | nil =>
                              have afterPaths : StatePaths P after :=
                                step () after (by simp only [rawEq, List.mem_singleton])
                              exact ih reached after saved afterPaths

end MicroCFTA.SourcePruningEnumerationPathFoldRaw
