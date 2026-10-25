import MicroCFTA.SourcePruningEnumerationDispatch

namespace MicroCFTA.SourcePruningEnumerationDispatchShape
open EnumerationState EnumerationCorrectness
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- An actual singleton retains the input or assimilates its two stored pending payloads. -/
theorem singleton
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (selected : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before source target queries = (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    after = before ∨ source ≠ target ∧
      ∃ (sourceNode targetNode merged : Option Nat) (sourceScs targetScs : List Suspended),
        before.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
        before.values[target]? = some (.unenumerated targetNode targetScs) ∧
        after = assimilated before target source (.unenumerated merged (sourceScs ++ targetScs)) := by
  by_cases same : source = target
  · simp only [SourcePruningEnumerationDispatch.dispatch, ite_eq_left same, Id.run, pure,
      Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at selected
    rcases selected with ⟨rfl, rfl, rfl⟩
    change [Except.ok ((), before)] = [Except.ok ((), after)] at completed
    simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
    subst after
    exact .inl rfl
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
        exact .inl rfl
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
                exact .inr ⟨same, none, targetNode, targetNode, sourceScs, targetScs, rfl, rfl, rfl⟩
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
                  exact .inr ⟨same, some sourceHandle, none, some sourceHandle, sourceScs, targetScs, rfl, rfl, rfl⟩
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
                            exact .inr ⟨same, some sourceHandle, some targetHandle, some handle, sourceScs, targetScs, rfl, rfl, rfl⟩
                          | node entry edges depth free =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact .inr ⟨same, some sourceHandle, some targetHandle, some handle, sourceScs, targetScs, rfl, rfl, rfl⟩
                          | union entry members depth free =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact .inr ⟨same, some sourceHandle, some targetHandle, some handle, sourceScs, targetScs, rfl, rfl, rfl⟩
                          | mu entry body depthShape ordinaryShape =>
                            intro completed
                            change [Except.ok ((), assimilated before target source (.unenumerated (some handle) (sourceScs ++ targetScs)))] = _ at completed
                            simp only [List.cons.injEq, and_true, Except.ok.injEq, Prod.mk.injEq, true_and] at completed
                            subst after
                            exact .inr ⟨same, some sourceHandle, some targetHandle, some handle, sourceScs, targetScs, rfl, rfl, rfl⟩

end MicroCFTA.SourcePruningEnumerationDispatchShape
