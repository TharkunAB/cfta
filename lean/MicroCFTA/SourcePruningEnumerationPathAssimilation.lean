import MicroCFTA.SourcePruningEnumerationPathTransport
import MicroCFTA.SourcePruningEnumerationDispatch

/-!
# Stored path preservation through actual native assimilation

The actual writes append the two stored pending buckets.
The path predicate does not depend on their optional native handles.
-/
namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat} {P : EqualityTrie.Path → Prop}

/-- The actual target write and source elimination preserve both original path buckets. -/
theorem assimilated_paths
    (before : EnumerationState.State Symbol EnumGuard) (source target : Nat)
    (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List Suspended)
    (paths : StatePaths P before)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs)) :
    StatePaths P (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) := by
  have sourcePaths : BucketPaths P sourceScs :=
    paths (.unenumerated sourceNode sourceScs) (List.mem_of_getElem? sourceStored)
  have targetPaths : BucketPaths P targetScs :=
    paths (.unenumerated targetNode targetScs) (List.mem_of_getElem? targetStored)
  have payload := sourcePaths.append targetPaths
  intro value member
  change value ∈ (before.values.set target
    (.unenumerated merged (sourceScs ++ targetScs))).set source .eliminated at member
  rcases List.mem_or_eq_of_mem_set member with retained | eliminated
  · rcases List.mem_or_eq_of_mem_set retained with old | replacement
    · exact paths value old
    · simpa only [replacement, references] using payload
  · simp [eliminated, references, BucketPaths]

/-- Every actual successful dispatcher singleton preserves its original path predicate. -/
theorem dispatch_paths
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (paths : StatePaths P before)
    (selected : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    StatePaths P after := by
  by_cases same : source = target
  · simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_left same, Id.run, pure,
      Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
    rcases selected with ⟨rfl, rfl, rfl⟩
    change [Except.ok ((), before)] = [Except.ok ((), after)] at completed
    simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
    subst after
    exact paths
  · cases sourceStored : before.values[source]? with
    | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored] at selected
    | some sourceValue =>
      cases sourceValue with
      | eliminated =>
        simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, Id.run, pure,
          Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
        rcases selected with ⟨rfl, rfl, rfl⟩
        change [Except.ok ((), before)] = [Except.ok ((), after)] at completed
        simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
        subst after
        exact paths
      | enumerated sourceFragment =>
        cases targetStored : before.values[target]? with
        | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored] at selected
        | some targetValue =>
          simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
            Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
          rcases selected with ⟨rfl, rfl, rfl⟩
          cases completed
      | unenumerated sourceNode sourceScs =>
        cases targetStored : before.values[target]? with
        | none => simp [SourcePruningEnumerationDispatch.dispatch, same, sourceStored, targetStored] at selected
        | some targetValue =>
          cases targetValue with
          | eliminated =>
            simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
              Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
            rcases selected with ⟨rfl, rfl, rfl⟩
            cases completed
          | enumerated targetFragment =>
            simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
              Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
            rcases selected with ⟨rfl, rfl, rfl⟩
            cases completed
          | unenumerated targetNode targetScs =>
            cases sourceNodeSame : sourceNode with
            | none =>
              subst sourceNode
              simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
              rcases selected with ⟨rfl, rfl, rfl⟩
              by_cases empty : targetNode = some 0
              · simp [SourcePruningEnumerationDispatch.finishOptional, empty, ExceptT.run] at completed
              · change (if targetNode = some 0 then [] else
                  [Except.ok ((), assimilated before target source (.unenumerated targetNode (sourceScs ++ targetScs)))]) = _ at completed
                rw [ite_eq_right empty] at completed
                simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                subst after
                exact assimilated_paths before source target none targetNode targetNode sourceScs targetScs
                  paths sourceStored targetStored
            | some sourceHandle =>
              subst sourceNode
              cases targetNodeSame : targetNode with
              | none =>
                subst targetNode
                simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_right same, sourceStored, targetStored,
                  Id.run, pure, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
                rcases selected with ⟨rfl, rfl, rfl⟩
                by_cases empty : (some sourceHandle : Option Nat) = some 0
                · simp [SourcePruningEnumerationDispatch.finishOptional, empty, ExceptT.run] at completed
                · change (if (some sourceHandle : Option Nat) = some 0 then [] else
                    [Except.ok ((), assimilated before target source (.unenumerated (some sourceHandle) (sourceScs ++ targetScs)))]) = _ at completed
                  rw [ite_eq_right empty] at completed
                  simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                  subst after
                  exact assimilated_paths before source target (some sourceHandle) none (some sourceHandle)
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
                          revert completed
                          cases (if answer then (.empty : Node) else query) with
                          | empty => intro completed; cases completed
                          | reference name =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact assimilated_paths before source target (some sourceHandle) (some targetHandle) (some handle)
                              sourceScs targetScs paths sourceStored targetStored
                          | node entry edges depth free =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact assimilated_paths before source target (some sourceHandle) (some targetHandle) (some handle)
                              sourceScs targetScs paths sourceStored targetStored
                          | union entry members depth free =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact assimilated_paths before source target (some sourceHandle) (some targetHandle) (some handle)
                              sourceScs targetScs paths sourceStored targetStored
                          | mu entry body depthShape ordinaryShape =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact assimilated_paths before source target (some sourceHandle) (some targetHandle) (some handle)
                              sourceScs targetScs paths sourceStored targetStored


end MicroCFTA.SourcePruningEnumerationDispatch
