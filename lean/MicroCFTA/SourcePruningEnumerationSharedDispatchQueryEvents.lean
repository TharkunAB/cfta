import MicroCFTA.SourcePruningEnumerationSharedDispatch

/-!
# Native query events in the actual shared dispatcher

Each event retains the complete input caller, query memos and native outcome.
The result projection retains every original branch and returned action.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEvents
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourcePruningEnumerationDispatch (finishOptional)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "NativeOutcome" => SourceEqualityNativeDemand.Outcome
local notation "Observed" => SourcePruningEnumerationSharedEnabledEmpty.Outcome

/-- One query event retains the exact input and its actual native observation. -/
abbrev Event (width : Nat) := Caller width × Queries × Node × Node × NativeOutcome width Node

/-- The dispatcher retains its original action, faults and complete native endpoint. -/
abbrev DispatchResult (EnumGuard : Type) (width : Nat) :=
  (Except (NativeOutcome width Node ⊕ Observed width) (Option (EnumerateM Symbol EnumGuard Unit))) × Caller width × Queries

variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Observe the single query site without changing any dispatcher branch. -/
noncomputable def observe
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard) (source target : Nat) (queries : Queries) :
    DispatchResult EnumGuard width × List (Event width) := Id.run do
  let noop : EnumerateM Symbol EnumGuard Unit := fun state => [.ok ((), state)]
  if source = target then return ((.ok (some noop), caller, queries), [])
  let some sourceValue := before.values[source]? | return ((.ok none, caller, queries), [])
  match sourceValue with
  | .eliminated => return ((.ok (some noop), caller, queries), [])
  | _ => pure PUnit.unit
  let some targetValue := before.values[target]? | return ((.ok none, caller, queries), [])
  let .unenumerated sourceNode sourceScs := sourceValue |
    return ((.ok (some (failure .invalidIntersection)), caller, queries), [])
  let .unenumerated targetNode targetScs := targetValue |
    return ((.ok (some (failure .invalidIntersection)), caller, queries), [])
  let some sourceHandle := sourceNode |
    return ((.ok (some (finishOptional source target targetNode sourceScs targetScs)), caller, queries), [])
  let some targetHandle := targetNode |
    return ((.ok (some (finishOptional source target (some sourceHandle) sourceScs targetScs)), caller, queries), [])
  let some left := lookupNode caller.checked.native.machine.heap sourceHandle | return ((.ok none, caller, queries), [])
  let some right := lookupNode caller.checked.native.machine.heap targetHandle | return ((.ok none, caller, queries), [])
  let actual : NativeOutcome width Node := SourceEqualityNativeDemand.execute nativeFuel
    (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) caller.checked
  let event : Event width := (caller, queries, left, right, actual)
  match actual with
  | .done query queried =>
      let prepared := SourcePruningEnumerationSharedDispatch.afterQuery checkEmpty p h
        source target sourceScs targetScs query queried caller queries
      return ((prepared.1.mapError Sum.inr, prepared.2.1, prepared.2.2), [event])
  | other => return ((.error (.inl other), SourceCurrentAllocatedPartialState.advance
      caller other.state caller.fourth caller.merge, queries), [event])

/-- Exact query events preserve the full dispatcher result and identify its literal query branch. -/
theorem observe_exact
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width)
    (before : EnumerationState.State Symbol EnumGuard) (source target : Nat) (queries : Queries) :
    let observed := observe checkEmpty nativeFuel p h caller before source target queries
    observed.1 = SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h caller before source target queries ∧
    observed.2.length ≤ 1 ∧
    (observed.2.length = 1 ↔ ∃ sourceHandle targetHandle sourceScs targetScs left right,
      source ≠ target ∧ before.values[source]? = some (.unenumerated (some sourceHandle) sourceScs) ∧
      before.values[target]? = some (.unenumerated (some targetHandle) targetScs) ∧
      lookupNode caller.checked.native.machine.heap sourceHandle = some left ∧
      lookupNode caller.checked.native.machine.heap targetHandle = some right) ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      start = caller ∧ saved = queries ∧ actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked := by
  dsimp only
  by_cases same : source = target
  · simp [observe, SourcePruningEnumerationSharedDispatch.dispatch, same]
  · cases sourceRead : before.values[source]? with
    | none => simp [observe, SourcePruningEnumerationSharedDispatch.dispatch, same, sourceRead]
    | some sourceValue =>
        cases sourceValue with
        | eliminated => simp [observe, SourcePruningEnumerationSharedDispatch.dispatch, same, sourceRead]
        | enumerated fragment =>
            cases targetRead : before.values[target]? <;>
              simp [observe, SourcePruningEnumerationSharedDispatch.dispatch, same, sourceRead, targetRead]
        | unenumerated sourceNode sourceScs =>
            cases targetRead : before.values[target]? with
            | none => simp [observe, SourcePruningEnumerationSharedDispatch.dispatch, same, sourceRead, targetRead]
            | some targetValue =>
                cases targetValue with
                | eliminated => simp [observe, SourcePruningEnumerationSharedDispatch.dispatch, same, sourceRead, targetRead]
                | enumerated fragment => simp [observe, SourcePruningEnumerationSharedDispatch.dispatch, same, sourceRead, targetRead]
                | unenumerated targetNode targetScs =>
                    cases sourceNode with
                    | none => simp [observe, SourcePruningEnumerationSharedDispatch.dispatch, same, sourceRead, targetRead]
                    | some sourceHandle =>
                        cases targetNode with
                        | none => simp [observe, SourcePruningEnumerationSharedDispatch.dispatch, same, sourceRead, targetRead]
                        | some targetHandle =>
                            cases leftRead : lookupNode caller.checked.native.machine.heap sourceHandle with
                            | none => simp [observe, SourcePruningEnumerationSharedDispatch.dispatch, same, sourceRead, targetRead, leftRead]
                            | some left =>
                                cases rightRead : lookupNode caller.checked.native.machine.heap targetHandle with
                                | none => simp [observe, SourcePruningEnumerationSharedDispatch.dispatch, same, sourceRead, targetRead, leftRead, rightRead]
                                | some right =>
                                    cases actual : SourceEqualityNativeDemand.execute nativeFuel
                                        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
                                        caller.checked <;>
                                      simp [observe, SourcePruningEnumerationSharedDispatch.dispatch, same, sourceRead, targetRead,
                                        leftRead, rightRead, actual, Prod.mk.injEq] <;>
                                      rintro start saved eventLeft eventRight observed rfl rfl rfl rfl rfl <;>
                                      exact ⟨rfl, rfl, actual.symm⟩

end MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEvents
