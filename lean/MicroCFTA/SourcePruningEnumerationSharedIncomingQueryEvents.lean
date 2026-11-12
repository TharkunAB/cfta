import MicroCFTA.SourcePruningEnumerationSharedIncomingNode
import MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEvents

/-!
# Actual incoming intersection query events

The observer retains every original native, Core and memo endpoint.
It records only the explicit intersection execute site.
The optional enabled worker remains unchanged. Its internal calls are not counted.
The returned Core action executes once on its actual read state.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEvents
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationIncomingNode (finish)
open SourcePruningEnumerationSharedDispatchQueryEvents (Event)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "NativeOutcome" => SourceEqualityNativeDemand.Outcome
local notation "Observed" => SourcePruningEnumerationSharedEnabledEmpty.Outcome

/-- The full incoming result includes the actual compressed read state. -/
abbrev IncomingResult (EnumGuard : Type) (width : Nat) :=
  (Except (NativeOutcome width Node ⊕ Observed width)
    (Option (List (Except Error (Unit × EnumerationState.State Symbol EnumGuard))))) ×
    Caller width × Queries × EnumerationState.State Symbol EnumGuard

variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

local instance incomingEventsMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Record the actual single query site and retain the full incoming operation. -/
noncomputable def observe
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (uv : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    IncomingResult EnumGuard width × List (Event width) :=
  match UnionFind.findRoot representativeFuel before.representatives uv with
  | none => ((.ok (some [.error .representativeFuel]), beforeCaller, queries, before), [])
  | some found =>
      let readState : EnumerationState.State Symbol EnumGuard := {before with representatives := found.forest}
      match before.values[found.representative]? with
      | none => ((.ok (some [.error .invalidSlot]), beforeCaller, queries, readState), [])
      | some (.unenumerated oldNode oldScs) =>
          match oldNode with
          | none =>
              match encodeNode incoming with
              | none => ((.ok none, beforeCaller, queries, readState), [])
              | some handle =>
                  ((.ok (some (ExceptT.run (finish found.representative handle incomingScs oldScs incoming readState))),
                    beforeCaller, queries, readState), [])
          | some oldHandle =>
              match lookupNode beforeCaller.checked.native.machine.heap oldHandle with
              | none => ((.ok none, beforeCaller, queries, readState), [])
              | some old =>
                  let actual : NativeOutcome width Node := SourceEqualityNativeDemand.execute nativeFuel
                    (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                    beforeCaller.checked
                  let event : Event width := (beforeCaller, queries, incoming, old, actual)
                  match actual with
                  | .done query queried =>
                      let phase : Observed width × Queries :=
                        if checkEmpty then
                          SourcePruningEnumerationSharedEnabledEmpty.check p h query queried beforeCaller.fourth queries
                        else (.skipped queried beforeCaller.fourth, queries)
                      let afterCaller : Caller width := SourceCurrentAllocatedPartialState.advance
                        beforeCaller phase.1.state phase.1.memo beforeCaller.merge
                      match phase.1.completed with
                      | some answer =>
                          let replacement : Node := if answer then .empty else query
                          match encodeNode replacement with
                          | none => ((.ok none, afterCaller, phase.2, readState), [event])
                          | some handle =>
                              ((.ok (some (ExceptT.run (finish found.representative handle incomingScs oldScs replacement readState))),
                                afterCaller, phase.2, readState), [event])
                      | none => ((.error (.inr phase.1), afterCaller, phase.2, readState), [event])
                  | other =>
                      ((.error (.inl other), SourceCurrentAllocatedPartialState.advance
                        beforeCaller other.state beforeCaller.fourth beforeCaller.merge, queries, readState), [event])
      | some _ => ((.ok (some [.error .invalidIntersection]), beforeCaller, queries, readState), [])

/-- Exact events preserve the full result and identify the actual incoming query branch. -/
theorem observe_exact
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (uv : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    let observed := observe checkEmpty representativeFuel nativeFuel p h beforeCaller before uv incoming incomingScs queries
    observed.1 = SourcePruningEnumerationSharedIncomingNode.run
      checkEmpty representativeFuel nativeFuel p h beforeCaller before uv incoming incomingScs queries ∧
    observed.2.length ≤ 1 ∧
    (observed.2.length = 1 ↔ ∃ found oldHandle oldScs old,
      UnionFind.findRoot representativeFuel before.representatives uv = some found ∧
      before.values[found.representative]? = some (.unenumerated (some oldHandle) oldScs) ∧
      lookupNode beforeCaller.checked.native.machine.heap oldHandle = some old) ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      start = beforeCaller ∧ saved = queries ∧ left = incoming ∧
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked := by
  dsimp only
  cases rootRead : UnionFind.findRoot representativeFuel before.representatives uv with
  | none => simp [observe, SourcePruningEnumerationSharedIncomingNode.run, rootRead]
  | some found =>
      cases slotRead : before.values[found.representative]? with
      | none => simp [observe, SourcePruningEnumerationSharedIncomingNode.run, rootRead, slotRead]
      | some value =>
          cases value with
          | eliminated => simp [observe, SourcePruningEnumerationSharedIncomingNode.run, rootRead, slotRead]
          | enumerated fragment => simp [observe, SourcePruningEnumerationSharedIncomingNode.run, rootRead, slotRead]
          | unenumerated oldNode oldScs =>
              cases oldNode with
              | none =>
                  cases encoded : encodeNode incoming <;>
                    simp [observe, SourcePruningEnumerationSharedIncomingNode.run, rootRead, slotRead, encoded]
              | some oldHandle =>
                  cases oldRead : lookupNode beforeCaller.checked.native.machine.heap oldHandle with
                  | none => simp [observe, SourcePruningEnumerationSharedIncomingNode.run, rootRead, slotRead, oldRead]
                  | some old =>
                      cases actual : SourceEqualityNativeDemand.execute nativeFuel
                          (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                          beforeCaller.checked <;>
                        simp [observe, SourcePruningEnumerationSharedIncomingNode.run, rootRead, slotRead,
                          oldRead, actual, Prod.mk.injEq] <;>
                        try (rintro start saved left right outcome rfl rfl rfl rfl rfl
                             exact ⟨rfl, rfl, rfl, actual.symm⟩)
                      case done query queried =>
                        generalize phaseRead : (if checkEmpty then
                          SourcePruningEnumerationSharedEnabledEmpty.check p h query queried beforeCaller.fourth queries
                          else (.skipped queried beforeCaller.fourth, queries) : Observed width × Queries) = phase
                        cases completed : phase.1.completed with
                        | none =>
                            simp [Prod.mk.injEq]
                            rintro start saved left right outcome rfl rfl rfl rfl rfl
                            exact ⟨rfl, rfl, rfl, actual.symm⟩
                        | some answer =>
                            cases encoded : encodeNode (if answer then .empty else query) <;>
                              simp [encoded, Prod.mk.injEq] <;>
                              rintro start saved left right outcome rfl rfl rfl rfl rfl <;>
                              exact ⟨rfl, rfl, rfl, actual.symm⟩

end MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEvents
