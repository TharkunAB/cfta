import MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets
import MicroCFTA.SourcePruningEnumerationSharedDispatchProper

namespace MicroCFTA.SourcePruningEnumerationSharedEagerNoneDispatch
open EnumerationState EnumerationCorrectness
open SourcePruningEnumerationSharedEagerNoneBuckets
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "EnumGuard" => Constraint
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
set_option autoImplicit false
variable {width : Nat}

private theorem assimilated_none
    (before : Core) (source target : Nat)
    (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List Suspended)
    (initial : NoneBucketsEmpty before)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs))
    (noneOrigin : merged = none → sourceNode = none ∧ targetNode = none) :
    NoneBucketsEmpty
      (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) := by
  intro uv scs stored
  have member : UVarValue.unenumerated none scs ∈
      (before.values.set target (.unenumerated merged (sourceScs ++ targetScs))).set
        source .eliminated := List.mem_of_getElem? stored
  rcases List.mem_or_eq_of_mem_set member with retained | eliminated
  · rcases List.mem_or_eq_of_mem_set retained with old | replacement
    · obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp old
      exact initial index scs found
    · cases merged with
      | some handle => cases replacement
      | none =>
          obtain ⟨sourceNone, targetNone⟩ := noneOrigin rfl
          rw [sourceNone] at sourceStored
          rw [targetNone] at targetStored
          have sourceEmpty := initial source sourceScs sourceStored
          have targetEmpty := initial target targetScs targetStored
          have same := (UVarValue.unenumerated.inj replacement).2
          exact same.trans (by rw [sourceEmpty, targetEmpty]; rfl)
  · cases eliminated

theorem dispatch_none_buckets
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : Core)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : Core)
    (proper : NoneBucketsEmpty before)
    (selected : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    NoneBucketsEmpty after := by
  by_cases same : source = target
  · simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_left same, Id.run, pure,
      Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
    rcases selected with ⟨rfl, rfl, rfl⟩
    change [Except.ok ((), before)] = [Except.ok ((), after)] at completed
    simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
    subst after
    exact proper
  · cases sourceStored : before.values[source]? with
    | none => simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored] at selected
    | some sourceValue =>
      cases sourceValue with
      | eliminated =>
        simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, Id.run, pure,
          Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
        rcases selected with ⟨rfl, rfl, rfl⟩
        change [Except.ok ((), before)] = [Except.ok ((), after)] at completed
        simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
        subst after
        exact proper
      | enumerated sourceFragment =>
        cases targetStored : before.values[target]? with
        | none => simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored] at selected
        | some targetValue =>
          simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
            Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
          rcases selected with ⟨rfl, rfl, rfl⟩
          cases completed
      | unenumerated sourceNode sourceScs =>
        cases targetStored : before.values[target]? with
        | none => simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored] at selected
        | some targetValue =>
          cases targetValue with
          | eliminated =>
            simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
              Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
            rcases selected with ⟨rfl, rfl, rfl⟩
            cases completed
          | enumerated targetFragment =>
            simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
              Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
            rcases selected with ⟨rfl, rfl, rfl⟩
            cases completed
          | unenumerated targetNode targetScs =>
            cases sourceNodeSame : sourceNode with
            | none =>
              subst sourceNode
              simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
              rcases selected with ⟨rfl, rfl, rfl⟩
              by_cases empty : targetNode = some 0
              · simp [SourcePruningEnumerationDispatch.finishOptional, empty, ExceptT.run] at completed
              · change (if targetNode = some 0 then [] else
                  [Except.ok ((), assimilated before target source (.unenumerated targetNode (sourceScs ++ targetScs)))]) = _ at completed
                rw [ite_eq_right empty] at completed
                simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                subst after
                exact assimilated_none before source target none targetNode targetNode sourceScs targetScs
                  proper sourceStored targetStored (fun absent => ⟨rfl, absent⟩)
            | some sourceHandle =>
              subst sourceNode
              cases targetNodeSame : targetNode with
              | none =>
                subst targetNode
                simp only [SourcePruningEnumerationSharedDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                  Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
                rcases selected with ⟨rfl, rfl, rfl⟩
                by_cases empty : (some sourceHandle : Option Nat) = some 0
                · simp [SourcePruningEnumerationDispatch.finishOptional, empty, ExceptT.run] at completed
                · change (if (some sourceHandle : Option Nat) = some 0 then [] else
                    [Except.ok ((), assimilated before target source (.unenumerated (some sourceHandle) (sourceScs ++ targetScs)))]) = _ at completed
                  rw [ite_eq_right empty] at completed
                  simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                  subst after
                  exact assimilated_none before source target (some sourceHandle) none (some sourceHandle)
                    sourceScs targetScs proper sourceStored targetStored (by intro impossible; cases impossible)
              | some targetHandle =>
                subst targetNode
                cases leftDecoded : SourcePruningEnumerationNodes.lookupNode beforeCaller.checked.native.machine.heap sourceHandle with
                | none => simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored, leftDecoded] at selected
                | some left =>
                  cases rightDecoded : SourcePruningEnumerationNodes.lookupNode beforeCaller.checked.native.machine.heap targetHandle with
                  | none => simp [SourcePruningEnumerationSharedDispatch.dispatch, same, sourceStored, targetStored, leftDecoded, rightDecoded] at selected
                  | some right =>
                    cases native : SourceEqualityNativeDemand.execute nativeFuel
                        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked with
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
                        SourcePruningEnumerationSharedEnabledEmpty.check p h query queried beforeCaller.fourth queries
                        else (.skipped queried beforeCaller.fourth, queries)) with ⟨worker, workerQueries⟩
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
                          rcases selected with ⟨rfl, rfl, rfl⟩
                          revert completed
                          cases (if answer then (.empty : Node) else query) with
                          | empty => intro completed; cases completed
                          | reference name =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact assimilated_none before source target (some sourceHandle) (some targetHandle) (some handle)
                              sourceScs targetScs proper sourceStored targetStored (by intro impossible; cases impossible)
                          | node entry edges depth free =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact assimilated_none before source target (some sourceHandle) (some targetHandle) (some handle)
                              sourceScs targetScs proper sourceStored targetStored (by intro impossible; cases impossible)
                          | union entry members depth free =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact assimilated_none before source target (some sourceHandle) (some targetHandle) (some handle)
                              sourceScs targetScs proper sourceStored targetStored (by intro impossible; cases impossible)
                          | mu entry body depthShape ordinaryShape =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact assimilated_none before source target (some sourceHandle) (some targetHandle) (some handle)
                              sourceScs targetScs proper sourceStored targetStored (by intro impossible; cases impossible)


end MicroCFTA.SourcePruningEnumerationSharedEagerNoneDispatch

#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerNoneDispatch.dispatch_none_buckets
