import MicroCFTA.SourcePruningEnumerationFoldResources
import MicroCFTA.SourcePruningEnumerationDispatchProjectionHeap

/-!
# Projection heaps at actual ordered fold returns

Each completed singleton derives the next current admission.
Early returns retain the projection heap at their actual native caller.
-/
namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState EnumerationCorrectness EnumerationCompleteness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed step advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
local notation "ProjectionHeap" => SourceEqualityAnnotationHeap.Heap projectable
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original fold resources and projectability hold at every actual outer successful return. -/
theorem observed_resources_projection_heap (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationState.State Symbol EnumGuard) (sources : List Nat)
    (checkEmpty : Bool) (n p h target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (targetPending : PendingAt before target)
    (selected : ∀ source ∈ sources, PendingOrEliminated before source)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed sources.length)
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (originalProjection : ProjectionHeap beforeCaller.checked.native.machine.heap)
    {result : Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))}
    {afterCaller : Caller (bits + 2)} {saved : Queries} {after : EnumerationState.State Symbol EnumGuard}
    (observed : run checkEmpty n p h sources beforeCaller before target memos.query =
      (.ok result, afterCaller, saved, after)) :
    Fits (advance seed sources.length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed sources.length).1) afterCaller.checked.native.machine.heap ∧
      ProjectionHeap afterCaller.checked.native.machine.heap := by
  have resources := observed_resources seed formulas solver inventory beforeCaller before sources
    checkEmpty n p h target memos initial realized targetPending selected fits reserved known observed
  refine ⟨resources.1, resources.2, ?_⟩
  clear resources
  induction sources generalizing seed inventory beforeCaller before memos with
  | nil =>
      simp only [run] at observed
      have same := congrArg (fun output => output.2.1) observed
      dsimp only at same
      rw [← same]
      exact originalProjection
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty n p h
        beforeCaller before source target memos.query with ⟨outcome, reachedCaller, queries⟩
      cases outcome with
      | error fault =>
          simp only [run, dispatchObserved] at observed
          cases observed
      | ok possible =>
          have current := (SourcePruningEnumerationDispatch.observed_resources_projection_heap
            seed.1 seed.2 formulas solver inventory beforeCaller before checkEmpty n p h source target
            memos initial realized fits reserved.head known originalProjection dispatchObserved).2.2
          cases possible with
          | none =>
              simp only [run, dispatchObserved] at observed
              have same := congrArg (fun output => output.2.1) observed
              dsimp only at same
              rw [← same]
              exact current
          | some action =>
              cases raw : ExceptT.run (action before) with
              | nil =>
                  simp only [run, dispatchObserved, raw] at observed
                  have same := congrArg (fun output => output.2.1) observed
                  dsimp only at same
                  rw [← same]
                  exact current
              | cons first tail =>
                  cases first with
                  | error fault =>
                      simp only [run, dispatchObserved, raw] at observed
                      have same := congrArg (fun output => output.2.1) observed
                      dsimp only at same
                      rw [← same]
                      exact current
                  | ok pair =>
                      rcases pair with ⟨valueUnit, middle⟩
                      cases valueUnit
                      cases tail with
                      | cons second remaining =>
                          simp only [run, dispatchObserved, raw] at observed
                          have same := congrArg (fun output => output.2.1) observed
                          dsimp only at same
                          rw [← same]
                          exact current
                      | nil =>
                          obtain ⟨next, final, post, querySame, middleRealized, middleTarget,
                            middleSelected, middleFits, middleKnown⟩ :=
                            observed_singleton seed formulas solver inventory beforeCaller before source target rest checkEmpty memos
                              initial realized targetPending selected fits reserved.head known dispatchObserved raw
                          simp only [run, dispatchObserved, raw] at observed
                          rw [← querySame] at observed
                          exact ih (step seed) next reachedCaller middle final post.context middleRealized middleTarget
                            middleSelected middleFits reserved.tail middleKnown current observed

end MicroCFTA.SourcePruningEnumerationFold
