import MicroCFTA.SourcePruningEnumerationDispatch
import MicroCFTA.SourcePruningEnumerationEnabledEmptyStability

/-!
# Successful dispatcher observations at larger bounds

A completed native query retains its exact checked state.
A completed enabled check retains its exact answer and memos.
The dispatcher therefore retains its action and every returned field.
-/
namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A successful query finalizer retains its exact optional action, caller and query memo. -/
theorem afterQuery_ok_stable
    {checkEmpty : Bool} {p h P H source target : Nat}
    {sourceScs targetScs : List Suspended} {query : Node} {queried : Checked width}
    {beforeCaller afterCaller : Caller width} {queries savedQueries : Queries}
    {action : Option (EnumerateM Symbol EnumGuard Unit)}
    (observed : afterQuery checkEmpty p h source target sourceScs targetScs
      query queried beforeCaller queries = (.ok action, afterCaller, savedQueries))
    (enoughP : p ≤ P) (enoughH : h ≤ H) :
    afterQuery checkEmpty P H source target sourceScs targetScs
      query queried beforeCaller queries = (.ok action, afterCaller, savedQueries) := by
  cases checkEmpty with
  | false =>
      simpa only [afterQuery, Bool.false_eq_true, ↓reduceIte] using observed
  | true =>
      cases phase : SourcePruningEnumerationEnabledEmpty.check p h query queried
          beforeCaller.fourth queries with
      | mk outcome returned =>
          cases outcome with
          | failed _fault _checked _memo =>
              simp only [afterQuery, ↓reduceIte, phase] at observed
              cases observed
          | done answer checked saved =>
              have later := SourcePruningEnumerationEnabledEmpty.check_done_stable
                p h P H query queried checked beforeCaller.fourth saved queries returned answer
                phase enoughP enoughH
              simpa only [afterQuery, ↓reduceIte, phase, later] using observed

/-- A successful dispatcher retains its exact optional action and endpoints at larger bounds. -/
theorem dispatch_ok_stable
    {checkEmpty : Bool} {n p h N P H : Nat}
    {beforeCaller afterCaller : Caller width} {before : EnumerationState.State Symbol EnumGuard}
    {source target : Nat} {queries savedQueries : Queries}
    {action : Option (EnumerateM Symbol EnumGuard Unit)}
    (observed : dispatch checkEmpty n p h beforeCaller before source target queries =
      (.ok action, afterCaller, savedQueries))
    (enoughNative : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    dispatch checkEmpty N P H beforeCaller before source target queries =
      (.ok action, afterCaller, savedQueries) := by
  by_cases same : source = target
  · simpa only [dispatch, ite_eq_left same, Id.run, pure] using observed
  · cases sourceStored : before.values[source]? with
    | none =>
        simpa only [dispatch, ite_eq_right same, sourceStored, Id.run, pure] using observed
    | some sourceValue =>
        cases sourceValue with
        | eliminated =>
            simpa only [dispatch, ite_eq_right same, sourceStored, Id.run, pure] using observed
        | enumerated _fragment =>
            cases targetStored : before.values[target]? <;>
              simpa only [dispatch, ite_eq_right same, sourceStored, targetStored, Id.run, pure]
                using observed
        | unenumerated sourceNode sourceScs =>
            cases targetStored : before.values[target]? with
            | none =>
                simpa only [dispatch, ite_eq_right same, sourceStored, targetStored, Id.run, pure]
                  using observed
            | some targetValue =>
                cases targetValue with
                | eliminated =>
                    simpa only [dispatch, ite_eq_right same, sourceStored, targetStored, Id.run, pure]
                      using observed
                | enumerated _fragment =>
                    simpa only [dispatch, ite_eq_right same, sourceStored, targetStored, Id.run, pure]
                      using observed
                | unenumerated targetNode targetScs =>
                    cases sourceNode with
                    | none =>
                        simpa only [dispatch, ite_eq_right same, sourceStored, targetStored, Id.run, pure]
                          using observed
                    | some leftHandle =>
                        cases targetNode with
                        | none =>
                            simpa only [dispatch, ite_eq_right same, sourceStored, targetStored, Id.run, pure]
                              using observed
                        | some rightHandle =>
                            cases leftDecoded : lookupNode beforeCaller.checked.native.machine.heap leftHandle with
                            | none =>
                                simpa only [dispatch, ite_eq_right same, sourceStored, targetStored,
                                  leftDecoded, Id.run, pure] using observed
                            | some left =>
                                cases rightDecoded : lookupNode beforeCaller.checked.native.machine.heap rightHandle with
                                | none =>
                                    simpa only [dispatch, ite_eq_right same, sourceStored, targetStored,
                                      leftDecoded, rightDecoded, Id.run, pure] using observed
                                | some right =>
                                    cases native : SourceEqualityNativeDemand.execute n
                                        (.code (SourceRecursiveIntersectionCode.requestNode
                                          IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked with
                                    | yielded | failed | constraintError | blocked =>
                                        simp only [dispatch, ite_eq_right same, sourceStored, targetStored,
                                          leftDecoded, rightDecoded, native, Id.run, pure] at observed
                                        cases observed
                                    | done query queried =>
                                        have nativeLater := SourceEqualityNativeDemand.done_stable n (N - n)
                                          (.code (SourceRecursiveIntersectionCode.requestNode
                                            IntersectionEmptyDomain.emptyDomain left right))
                                          beforeCaller.checked queried query native
                                        rw [Nat.add_sub_of_le enoughNative] at nativeLater
                                        rcases phase : afterQuery (EnumGuard := EnumGuard) checkEmpty p h
                                            source target sourceScs targetScs query queried beforeCaller queries with
                                          ⟨phaseResult, _phaseCaller, _phaseQueries⟩
                                        cases phaseResult with
                                        | error _fault =>
                                            simp only [dispatch, ite_eq_right same, sourceStored, targetStored,
                                              leftDecoded, rightDecoded, native, phase, Except.mapError,
                                              Id.run, pure] at observed
                                            cases observed
                                        | ok _possible =>
                                            have phaseLater := afterQuery_ok_stable phase enoughP enoughH
                                            simpa only [dispatch, ite_eq_right same, sourceStored, targetStored,
                                              leftDecoded, rightDecoded, native, nativeLater, phase, phaseLater,
                                              Except.mapError, Id.run, pure] using observed

end MicroCFTA.SourcePruningEnumerationDispatch
