import MicroCFTA.EnumerationFlatNativeFold
import MicroCFTA.SourcePruningEnumerationIncomingNode

/-!
# Native incoming merge with direct-parent representative reads

The read core stays separate from the written rows. The actual native request
and enabled check run once. Earlier representative bounds remain explicit.
-/
namespace MicroCFTA.EnumerationFlatNativeIncoming
open InternedConstructorTemplates
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}
attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

/-- Write the incoming slot and inherit ancestry before Empty rejection. -/
def finish (target handle : Nat) (incomingScs oldScs : List EnumerationState.Suspended)
    (replacement : Node) : EnumerationFlatState.Action Symbol EnumGuard Unit := do
  EnumerationFlatState.setValue target (.unenumerated (some handle) (incomingScs ++ oldScs))
  EnumerationFlatState.inheritAncestry target
  match replacement with
  | .empty => EnumerationFlatState.reject
  | _ => pure ()

/-- Keep every written result or rejection at related actual read cores. -/
theorem finish_related (related : EnumerationFlatState.Related flat earlier)
    (target handle : Nat) (incomingScs oldScs : List EnumerationState.Suspended)
    (replacement : Node) :
    EnumerationResultRelation.Results EnumerationFlatState.Related
      (finish target handle incomingScs oldScs replacement flat)
      (SourcePruningEnumerationIncomingNode.finish target handle incomingScs oldScs replacement earlier) := by
  unfold finish SourcePruningEnumerationIncomingNode.finish
  apply EnumerationResultRelation.stateT_bind _ _ _ _
    (EnumerationFlatState.setValue_related related target _)
  intro _ left right states
  apply EnumerationResultRelation.stateT_bind _ _ _ _
    (EnumerationFlatState.inheritAncestry_related states target)
  intro _ left right states
  cases replacement <;> first
    | exact .nil
    | exact EnumerationFlatState.pure_related states ()

/-- Execute the native incoming merge and return its actual read core. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationFlatState.State Symbol EnumGuard)
    (uv : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationFlatState.State Symbol EnumGuard))))) ×
      Caller width × Queries × EnumerationFlatState.State Symbol EnumGuard :=
  let target := FlatUnionFind.root before.representatives uv
  match before.values[target]? with
  | none => (.ok (some [.error .invalidSlot]), beforeCaller, queries, before)
  | some (.unenumerated oldNode oldScs) =>
      match oldNode with
      | none =>
          match encodeNode incoming with
          | none => (.ok none, beforeCaller, queries, before)
          | some handle =>
              (.ok (some (ExceptT.run (finish target handle incomingScs oldScs incoming before))),
                beforeCaller, queries, before)
      | some oldHandle =>
          match lookupNode beforeCaller.checked.native.machine.heap oldHandle with
          | none => (.ok none, beforeCaller, queries, before)
          | some old =>
              let actual : SourceEqualityNativeDemand.Outcome width Node :=
                SourceEqualityNativeDemand.execute nativeFuel
                  (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                  beforeCaller.checked
              match actual with
              | .done query queried =>
                  let phase : SourceCurrentAllocatedConjunctionWorker.Outcome width × Queries :=
                    if checkEmpty then
                      SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                    else (.done false queried beforeCaller.fourth, queries)
                  let afterCaller : Caller width :=
                    SourceCurrentAllocatedPartialState.advance beforeCaller phase.1.state phase.1.memo beforeCaller.merge
                  match phase.1 with
                  | .done answer checkedAfter saved =>
                      let replacement : Node := if answer then .empty else query
                      match encodeNode replacement with
                      | none => (.ok none, afterCaller, phase.2, before)
                      | some handle =>
                          (.ok (some (ExceptT.run (finish target handle incomingScs oldScs replacement before))),
                            SourceCurrentAllocatedPartialState.advance beforeCaller checkedAfter saved beforeCaller.merge,
                            phase.2, before)
                  | .failed fault checkedAfter saved =>
                      (.error (.inr (.failed fault checkedAfter saved)), afterCaller, phase.2, before)
              | other =>
                  (.error (.inl other), SourceCurrentAllocatedPartialState.advance
                    beforeCaller other.state beforeCaller.fourth beforeCaller.merge, queries, before)
  | some _ => (.ok (some [.error .invalidIntersection]), beforeCaller, queries, before)

/-- A completed earlier root read preserves every native bound and exact native effects. -/
theorem run_related
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (related : EnumerationFlatState.Related flat earlier)
    (completed : UnionFind.findRoot representativeFuel earlier.representatives uv = some found)
    (checkEmpty : Bool) (nativeFuel p h : Nat) (beforeCaller : Caller width)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    EnumerationFlatNativeFold.ResultRelated
      (run checkEmpty nativeFuel p h beforeCaller flat uv incoming incomingScs queries)
      (SourcePruningEnumerationIncomingNode.run checkEmpty representativeFuel nativeFuel p h
        beforeCaller earlier uv incoming incomingScs queries) := by
  obtain ⟨rootSame, _sizeSame, retained⟩ :=
    FlatUnionFind.findRoot_represents related.representatives completed
  have readRelated : EnumerationFlatState.Related flat
      {earlier with representatives := found.forest} :=
    EnumerationFlatState.related_forests related related.valid retained
  simp only [run, SourcePruningEnumerationIncomingNode.run, completed, ← rootSame, related.values]
  cases stored : earlier.values[found.representative]? with
  | none => exact ⟨rfl, rfl, readRelated, .cons (.error EnumerationState.Error.invalidSlot) .nil⟩
  | some value =>
    cases value with
    | eliminated => exact ⟨rfl, rfl, readRelated, .cons (.error EnumerationState.Error.invalidIntersection) .nil⟩
    | enumerated fragment => exact ⟨rfl, rfl, readRelated, .cons (.error EnumerationState.Error.invalidIntersection) .nil⟩
    | unenumerated oldNode oldScs =>
      cases oldNode with
      | none =>
        cases encoded : encodeNode incoming with
        | none => exact ⟨rfl, rfl, readRelated, trivial⟩
        | some handle => exact ⟨rfl, rfl, readRelated, finish_related readRelated _ _ _ _ _⟩
      | some oldHandle =>
        dsimp only
        cases decoded : lookupNode beforeCaller.checked.native.machine.heap oldHandle with
        | none => exact ⟨rfl, rfl, readRelated, trivial⟩
        | some old =>
          generalize SourceEqualityNativeDemand.execute nativeFuel
            (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
            beforeCaller.checked = actual
          cases actual with
          | failed fault checked => exact ⟨rfl, rfl, readRelated, rfl⟩
          | yielded control checked => exact ⟨rfl, rfl, readRelated, rfl⟩
          | constraintError fault checked => exact ⟨rfl, rfl, readRelated, rfl⟩
          | blocked names checked => exact ⟨rfl, rfl, readRelated, rfl⟩
          | done query queried =>
            generalize (if checkEmpty then
              SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
              else (.done false queried beforeCaller.fourth, queries)) = phase
            obtain ⟨outcome, savedQueries⟩ := phase
            cases outcome with
            | failed fault checked saved => exact ⟨rfl, rfl, readRelated, rfl⟩
            | done answer checked saved =>
              dsimp only
              cases encoded : encodeNode (if answer then .empty else query) with
              | none => exact ⟨rfl, rfl, readRelated, trivial⟩
              | some handle => exact ⟨rfl, rfl, readRelated, finish_related readRelated _ _ _ _ _⟩

/-- Every related input supplies one stable sufficient earlier representative bound. -/
theorem run_stable
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (related : EnumerationFlatState.Related flat earlier) (uv : Nat) :
    ∃ representativeFuel, ∀ extra checkEmpty nativeFuel p h (beforeCaller : Caller width)
      incoming incomingScs queries,
      EnumerationFlatNativeFold.ResultRelated
        (run checkEmpty nativeFuel p h beforeCaller flat uv incoming incomingScs queries)
        (SourcePruningEnumerationIncomingNode.run checkEmpty (representativeFuel + extra) nativeFuel p h
          beforeCaller earlier uv incoming incomingScs queries) := by
  obtain ⟨fuel, found, stable, _rootSame, _sizeSame, _retained⟩ :=
    FlatUnionFind.find_stable related.representatives uv
  exact ⟨fuel, fun extra checkEmpty nativeFuel p h beforeCaller incoming incomingScs queries =>
    run_related related (stable extra) checkEmpty nativeFuel p h beforeCaller incoming incomingScs queries⟩

end MicroCFTA.EnumerationFlatNativeIncoming
