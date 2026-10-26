import MicroCFTA.SourcePruningEnumerationIncomingObservedResources
import MicroCFTA.SourcePruningEnumerationDispatch

/-!
# Exact successful dispatcher observations

Successful bounds identify the captured action and every returned field.
The proof compares the actual native and optional-check observations.
It needs no caller invariant or range premise.
-/
namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

private theorem ok_tuple_unique {E : Type _} {A : Type _} {B : Type _} {C : Type _}
    {observation : Except E A × B × C} {first second : A} {after later : B} {saved current : C}
    (one : observation = (.ok first, after, saved))
    (two : observation = (.ok second, later, current)) :
    first = second ∧ after = later ∧ saved = current := by
  simpa only [Prod.mk.injEq, Except.ok.injEq] using one.symm.trans two

/-- Different successful bounds retain the exact action, caller and query memo. -/
theorem ok_unique
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (flag : Bool) {n p h N P H : Nat}
    {beforeCaller : Caller width} {before : EnumerationState.State Symbol EnumGuard}
    {source target : Nat} {queries : Queries}
    {result other : Option (EnumerateM Symbol EnumGuard Unit)}
    {afterCaller later : Caller width} {saved current : Queries}
    (one : dispatch flag n p h beforeCaller before source target queries =
      (.ok result, afterCaller, saved))
    (two : dispatch flag N P H beforeCaller before source target queries =
      (.ok other, later, current)) :
    result = other ∧ afterCaller = later ∧ saved = current := by
  by_cases same : source = target
  · simp only [dispatch, ite_eq_left same, Id.run, pure] at one two
    exact ok_tuple_unique one two
  · cases sourceStored : before.values[source]? with
    | none =>
        simp only [dispatch, ite_eq_right same, sourceStored, Id.run, pure] at one two
        exact ok_tuple_unique one two
    | some sourceValue =>
        cases sourceValue with
        | eliminated =>
            simp only [dispatch, ite_eq_right same, sourceStored, Id.run, pure] at one two
            exact ok_tuple_unique one two
        | enumerated fragment =>
            cases targetStored : before.values[target]? <;>
              simp only [dispatch, ite_eq_right same, sourceStored, targetStored, Id.run, pure] at one two <;>
              exact ok_tuple_unique one two
        | unenumerated sourceNode sourceScs =>
            cases targetStored : before.values[target]? with
            | none =>
                simp only [dispatch, ite_eq_right same, sourceStored, targetStored, Id.run, pure] at one two
                exact ok_tuple_unique one two
            | some targetValue =>
                cases targetValue with
                | eliminated =>
                    simp only [dispatch, ite_eq_right same, sourceStored, targetStored, Id.run, pure] at one two
                    exact ok_tuple_unique one two
                | enumerated fragment =>
                    simp only [dispatch, ite_eq_right same, sourceStored, targetStored, Id.run, pure] at one two
                    exact ok_tuple_unique one two
                | unenumerated targetNode targetScs =>
                    cases sourceNode with
                    | none =>
                        simp only [dispatch, ite_eq_right same, sourceStored, targetStored, Id.run, pure] at one two
                        exact ok_tuple_unique one two
                    | some leftHandle =>
                        cases targetNode with
                        | none =>
                            simp only [dispatch, ite_eq_right same, sourceStored, targetStored, Id.run, pure] at one two
                            exact ok_tuple_unique one two
                        | some rightHandle =>
                            cases leftDecoded : lookupNode beforeCaller.checked.native.machine.heap leftHandle with
                            | none =>
                                simp only [dispatch, ite_eq_right same, sourceStored, targetStored, leftDecoded,
                                  Id.run, pure] at one two
                                exact ok_tuple_unique one two
                            | some left =>
                                cases rightDecoded : lookupNode beforeCaller.checked.native.machine.heap rightHandle with
                                | none =>
                                    simp only [dispatch, ite_eq_right same, sourceStored, targetStored,
                                      leftDecoded, rightDecoded, Id.run, pure] at one two
                                    exact ok_tuple_unique one two
                                | some right =>
                                    cases firstNative : SourceEqualityNativeDemand.execute n
                                        (.code (SourceRecursiveIntersectionCode.requestNode
                                          IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked with
                                    | yielded | failed | constraintError | blocked =>
                                        simp only [dispatch, ite_eq_right same, sourceStored, targetStored,
                                          leftDecoded, rightDecoded, firstNative, Id.run, pure] at one
                                        cases one
                                    | done query queried =>
                                        cases secondNative : SourceEqualityNativeDemand.execute N
                                            (.code (SourceRecursiveIntersectionCode.requestNode
                                              IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked with
                                        | yielded | failed | constraintError | blocked =>
                                            simp only [dispatch, ite_eq_right same, sourceStored, targetStored,
                                              leftDecoded, rightDecoded, secondNative, Id.run, pure] at two
                                            cases two
                                        | done otherQuery otherQueried =>
                                            obtain ⟨sameQuery, sameQueried⟩ := SourceCurrentAllocatedNativeColdClosedExact.completed_unique
                                              n N _ beforeCaller.checked queried otherQueried query otherQuery
                                              firstNative secondNative
                                            subst otherQuery
                                            subst otherQueried
                                            cases firstPhase : (if flag then
                                                SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                                                else (.done false queried beforeCaller.fourth, queries)) with
                                            | mk firstOutcome firstQueries =>
                                                cases firstOutcome with
                                                | failed fault checked savedMemo =>
                                                    simp only [dispatch, ite_eq_right same, sourceStored, targetStored,
                                                      leftDecoded, rightDecoded, firstNative, afterQuery, firstPhase,
                                                      Except.mapError, Id.run, pure] at one
                                                    cases one
                                                | done answer checked savedMemo =>
                                                    cases secondPhase : (if flag then
                                                        SourcePruningEnumerationEnabledEmpty.check P H query queried beforeCaller.fourth queries
                                                        else (.done false queried beforeCaller.fourth, queries)) with
                                                    | mk secondOutcome secondQueries =>
                                                        cases secondOutcome with
                                                        | failed fault laterChecked currentMemo =>
                                                            simp only [dispatch, ite_eq_right same, sourceStored, targetStored,
                                                              leftDecoded, rightDecoded, secondNative, afterQuery, secondPhase,
                                                              Except.mapError, Id.run, pure] at two
                                                            cases two
                                                        | done otherAnswer laterChecked currentMemo =>
                                                            obtain ⟨rfl, rfl, rfl, rfl⟩ :=
                                                              SourcePruningEnumerationEnabledEmpty.optional_done_unique flag
                                                                firstPhase secondPhase
                                                            simp only [dispatch, ite_eq_right same, sourceStored, targetStored,
                                                              leftDecoded, rightDecoded, firstNative, afterQuery, firstPhase,
                                                              Except.mapError, Id.run, pure] at one
                                                            simp only [dispatch, ite_eq_right same, sourceStored, targetStored,
                                                              leftDecoded, rightDecoded, secondNative, afterQuery, secondPhase,
                                                              Except.mapError, Id.run, pure] at two
                                                            exact ok_tuple_unique one two

end MicroCFTA.SourcePruningEnumerationDispatch
