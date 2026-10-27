import MicroCFTA.EnumerationFlatCore
import MicroCFTA.SourcePruningEnumerationDispatch

/-!
# Native dispatch across the union-find representation change

The same raw slots select the same native request. Every returned caller and
query state remains literal. Rejected actions and explicit errors stay distinct.
-/
namespace MicroCFTA.EnumerationFlatNativeDispatch
open SourcePruningEnumerationNodes
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- Update both raw slots and the target ancestry in the source order. -/
def assimilated (state : EnumerationFlatState.State Symbol EnumGuard) (target source : Nat)
    (merged : EnumerationState.UVarValue Symbol) : EnumerationFlatState.State Symbol EnumGuard :=
  {state with
    values := (state.values.set target merged).set source .eliminated
    recursionAncestry := fun other => if other = target then
      (state.recursionAncestry source ++ state.recursionAncestry target).eraseDups
      else state.recursionAncestry other}

/-- The raw update preserves the complete relation without a new forest read. -/
theorem assimilated_related (related : EnumerationFlatState.Related flat earlier)
    (target source : Nat) (merged : EnumerationState.UVarValue Symbol) :
    EnumerationFlatState.Related (assimilated flat target source merged)
      (EnumerationCorrectness.assimilated earlier target source merged) := by
  refine ⟨related.valid, related.representatives, related.counter, ?_, related.obligations,
    ?_, related.expansionAncestry⟩
  · change (flat.values.set target merged).set source .eliminated = _
    rw [related.values]
    rfl
  · change (fun other => if other = target then _ else flat.recursionAncestry other) = _
    rw [related.recursionAncestry]
    rfl

/-- Reject the empty optional handle before either raw write. -/
def finishOptional (source target : Nat) (node : Option Nat)
    (sourceScs targetScs : List EnumerationState.Suspended) :
    EnumerationFlatState.Action Symbol EnumGuard Unit :=
  fun state => if node = some 0 then [] else
    [.ok ((), assimilated state target source (.unenumerated node (sourceScs ++ targetScs)))]

/-- Reject the empty native value before the two raw writes and ancestry transfer. -/
def finish (source target handle : Nat)
    (sourceScs targetScs : List EnumerationState.Suspended) (result : Node) :
    EnumerationFlatState.Action Symbol EnumGuard Unit :=
  match result with
  | .empty => fun _ => []
  | _ => fun state =>
      [.ok ((), assimilated state target source (.unenumerated (some handle) (sourceScs ++ targetScs)))]

/-- Optional finishing keeps every ordered result and its complete core. -/
theorem finishOptional_related (related : EnumerationFlatState.Related flat earlier)
    (source target : Nat) (node : Option Nat)
    (sourceScs targetScs : List EnumerationState.Suspended) :
    EnumerationResultRelation.Results EnumerationFlatState.Related
      (finishOptional source target node sourceScs targetScs flat)
      (SourcePruningEnumerationDispatch.finishOptional source target node sourceScs targetScs earlier) := by
  by_cases empty : node = some 0
  · simp only [finishOptional, SourcePruningEnumerationDispatch.finishOptional, empty, ↓reduceIte]
    exact .nil
  · simp only [finishOptional, SourcePruningEnumerationDispatch.finishOptional, empty, ↓reduceIte]
    exact .cons (.ok () (assimilated_related related target source _)) .nil

/-- Native finishing consumes the same value without executing another query. -/
theorem finish_related (related : EnumerationFlatState.Related flat earlier)
    (source target handle : Nat) (sourceScs targetScs : List EnumerationState.Suspended)
    (result : Node) :
    EnumerationResultRelation.Results EnumerationFlatState.Related
      (finish source target handle sourceScs targetScs result flat)
      (SourcePruningEnumerationAssimilation.finish source target handle sourceScs targetScs result earlier) := by
  cases result <;> first
    | exact .nil
    | exact .cons (.ok () (assimilated_related related target source _)) .nil

/-- Keep exact outer effects and relate every captured action at related input cores. -/
def PreparedRelated {Fault : Type 1}
    (flat : Except Fault (Option (EnumerationFlatState.Action Symbol EnumGuard Unit)) × Caller width × Queries)
    (earlier : Except Fault (Option (EnumerationState.EnumerateM Symbol EnumGuard Unit)) × Caller width × Queries) : Prop :=
  flat.2 = earlier.2 ∧
    match flat.1, earlier.1 with
    | .error first, .error second => first = second
    | .ok none, .ok none => True
    | .ok (some first), .ok (some second) =>
        ∀ left right, EnumerationFlatState.Related left right →
          EnumerationResultRelation.Results EnumerationFlatState.Related (first left) (second right)
    | _, _ => False

/-- Keep the reached caller and query pair outside a missing encoded action. -/
noncomputable def afterQuery
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (p h : Nat) (source target : Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (query : Node) (queried : Checked width) (beforeCaller : Caller width) (queries : Queries) :
    (Except (SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (EnumerationFlatState.Action Symbol EnumGuard Unit))) × Caller width × Queries :=
  let phase : SourceCurrentAllocatedConjunctionWorker.Outcome width × Queries :=
    if checkEmpty then
      SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
    else (.done false queried beforeCaller.fourth, queries)
  match phase.1 with
  | .done answer checkedAfter saved =>
      let replacement : Node := if answer then .empty else query
      (.ok ((encodeNode replacement).map (fun handle =>
          finish source target handle sourceScs targetScs replacement)),
        SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge, phase.2)
  | .failed _ checkedAfter saved =>
      (.error phase.1,
        SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge, phase.2)

/-- Select the source branches before the actual checked query and enabled check. -/
noncomputable def dispatch
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationFlatState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) :
    (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (EnumerationFlatState.Action Symbol EnumGuard Unit))) × Caller width × Queries := Id.run do
  let noop : EnumerationFlatState.Action Symbol EnumGuard Unit := fun state => [.ok ((), state)]
  if source = target then return (.ok (some noop), beforeCaller, queries)
  let some sourceValue := before.values[source]? | return (.ok none, beforeCaller, queries)
  match sourceValue with
  | .eliminated => return (.ok (some noop), beforeCaller, queries)
  | _ => pure PUnit.unit
  let some targetValue := before.values[target]? | return (.ok none, beforeCaller, queries)
  let .unenumerated sourceNode sourceScs := sourceValue |
    return (.ok (some (EnumerationFlatState.failure .invalidIntersection)), beforeCaller, queries)
  let .unenumerated targetNode targetScs := targetValue |
    return (.ok (some (EnumerationFlatState.failure .invalidIntersection)), beforeCaller, queries)
  let some sourceHandle := sourceNode |
    return (.ok (some (finishOptional source target targetNode sourceScs targetScs)), beforeCaller, queries)
  let some targetHandle := targetNode |
    return (.ok (some (finishOptional source target (some sourceHandle) sourceScs targetScs)), beforeCaller, queries)
  let some left := lookupNode beforeCaller.checked.native.machine.heap sourceHandle |
    return (.ok none, beforeCaller, queries)
  let some right := lookupNode beforeCaller.checked.native.machine.heap targetHandle |
    return (.ok none, beforeCaller, queries)
  let actual : SourceEqualityNativeDemand.Outcome width Node :=
    SourceEqualityNativeDemand.execute nativeFuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) beforeCaller.checked
  match actual with
  | .done query queried =>
    let prepared :
      (Except (SourceCurrentAllocatedConjunctionWorker.Outcome width)
        (Option (EnumerationFlatState.Action Symbol EnumGuard Unit))) × Caller width × Queries :=
      afterQuery checkEmpty p h source target sourceScs targetScs query queried beforeCaller queries
    return (prepared.1.mapError Sum.inr, prepared.2.1, prepared.2.2)
  | other => return (.error (.inl other),
      SourceCurrentAllocatedPartialState.advance beforeCaller other.state beforeCaller.fourth beforeCaller.merge, queries)

/-- The same emptiness phase retains its complete caller and query effects. -/
theorem afterQuery_related
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (p h source target : Nat)
    (sourceScs targetScs : List EnumerationState.Suspended)
    (query : Node) (queried : Checked width) (beforeCaller : Caller width) (queries : Queries) :
    PreparedRelated (afterQuery (EnumGuard := EnumGuard) checkEmpty p h source target
      sourceScs targetScs query queried beforeCaller queries)
      (SourcePruningEnumerationDispatch.afterQuery checkEmpty p h source target
        sourceScs targetScs query queried beforeCaller queries) := by
  unfold afterQuery SourcePruningEnumerationDispatch.afterQuery
  generalize (if checkEmpty then
    SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
    else (.done false queried beforeCaller.fourth, queries)) = phase
  obtain ⟨outcome, savedQueries⟩ := phase
  cases outcome with
  | done answer checked saved =>
      dsimp only
      refine ⟨rfl, ?_⟩
      cases encoded : encodeNode (if answer then .empty else query) with
      | none => trivial
      | some handle =>
          intro flat earlier related
          exact finish_related related source target handle sourceScs targetScs _
  | failed fault checked saved => exact ⟨rfl, rfl⟩

/-- Renaming a fault retains the same outer effects and every action observation. -/
theorem mapError_related {Fault Next : Type 1}
    (flat : Except Fault (Option (EnumerationFlatState.Action Symbol EnumGuard Unit)) × Caller width × Queries)
    (earlier : Except Fault (Option (EnumerationState.EnumerateM Symbol EnumGuard Unit)) × Caller width × Queries)
    (related : PreparedRelated flat earlier) (rename : Fault → Next) :
    PreparedRelated (flat.1.mapError rename, flat.2)
      (earlier.1.mapError rename, earlier.2) := by
  obtain ⟨effects, results⟩ := related
  refine ⟨effects, ?_⟩
  cases first : flat.1 with
  | error fault =>
      cases second : earlier.1 <;> simp_all only [Except.mapError]
  | ok firstValue =>
      cases second : earlier.1 with
      | error fault => simp_all only [Except.mapError]
      | ok secondValue =>
          cases firstValue <;> cases secondValue <;> simp_all only [Except.mapError]

/-- Every bounded native dispatcher retains all outer effects and ordered action rows. -/
theorem dispatch_related
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (related : EnumerationFlatState.Related flat earlier)
    (checkEmpty : Bool) (nativeFuel p h : Nat) (beforeCaller : Caller width)
    (source target : Nat) (queries : Queries) :
    PreparedRelated (dispatch checkEmpty nativeFuel p h beforeCaller flat source target queries)
      (SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller earlier source target queries) := by
  unfold dispatch SourcePruningEnumerationDispatch.dispatch
  simp only [related.values]
  by_cases same : source = target
  · simp only [same, ↓reduceIte]
    exact ⟨rfl, fun _ _ states => .cons (.ok () states) .nil⟩
  · simp only [same, ↓reduceIte]
    cases sourceRead : earlier.values[source]? with
    | none => exact ⟨rfl, trivial⟩
    | some sourceValue =>
      cases sourceValue with
      | eliminated => exact ⟨rfl, fun _ _ states => .cons (.ok () states) .nil⟩
      | enumerated fragment =>
        cases targetRead : earlier.values[target]? with
        | none => exact ⟨rfl, trivial⟩
        | some targetValue =>
          exact ⟨rfl, fun _ _ _ => .cons (.error EnumerationState.Error.invalidIntersection) .nil⟩
      | unenumerated sourceNode sourceScs =>
        cases targetRead : earlier.values[target]? with
        | none => exact ⟨rfl, trivial⟩
        | some targetValue =>
          cases targetValue with
          | eliminated => exact ⟨rfl, fun _ _ _ => .cons (.error EnumerationState.Error.invalidIntersection) .nil⟩
          | enumerated fragment => exact ⟨rfl, fun _ _ _ => .cons (.error EnumerationState.Error.invalidIntersection) .nil⟩
          | unenumerated targetNode targetScs =>
            cases sourceNode with
            | none => exact ⟨rfl, fun _ _ states => finishOptional_related states source target _ _ _⟩
            | some sourceHandle =>
              cases targetNode with
              | none => exact ⟨rfl, fun _ _ states => finishOptional_related states source target _ _ _⟩
              | some targetHandle =>
                cases leftRead : lookupNode beforeCaller.checked.native.machine.heap sourceHandle with
                | none => simp only [leftRead]; exact ⟨rfl, trivial⟩
                | some left =>
                  simp only [leftRead]
                  cases rightRead : lookupNode beforeCaller.checked.native.machine.heap targetHandle with
                  | none => exact ⟨rfl, trivial⟩
                  | some right =>
                    cases actual : (SourceEqualityNativeDemand.execute nativeFuel
                      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
                      beforeCaller.checked) with
                    | yielded control state => exact ⟨rfl, rfl⟩
                    | failed fault state => exact ⟨rfl, rfl⟩
                    | constraintError message state => exact ⟨rfl, rfl⟩
                    | blocked reason control state => exact ⟨rfl, rfl⟩
                    | done query queried =>
                      exact mapError_related _ _ (afterQuery_related checkEmpty p h source target
                        sourceScs targetScs query queried beforeCaller queries) Sum.inr

end MicroCFTA.EnumerationFlatNativeDispatch
