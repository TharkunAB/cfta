import MicroCFTA.SourcePruningEnumerationFoldAdmission

/-!
# Original resources at the actual ordered fold return

Every successful singleton supplies the next current packet.
The original reservation covers that entry. Early stops retain their native
effects and fit the remaining conservative schedule without executing it.
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
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original reservations bound the exact returned caller of every outer successful fold. -/
theorem observed_resources (seed : Seed)
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
    {result : Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))}
    {afterCaller : Caller (bits + 2)} {saved : Queries} {after : EnumerationState.State Symbol EnumGuard}
    (observed : run checkEmpty n p h sources beforeCaller before target memos.query =
      (.ok result, afterCaller, saved, after)) :
    Fits (advance seed sources.length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed sources.length).1) afterCaller.checked.native.machine.heap := by
  induction sources generalizing seed inventory beforeCaller before memos with
  | nil =>
      simp only [run] at observed
      have same := congrArg (fun output => output.2.1) observed
      dsimp only at same
      rw [← same]
      exact ⟨fits, known⟩
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty n p h
        beforeCaller before source target memos.query with ⟨outcome, reachedCaller, queries⟩
      cases outcome with
      | error fault =>
          simp only [run, dispatchObserved] at observed
          cases observed
      | ok possible =>
          have bounded := SourcePruningEnumerationDispatch.observed_resources seed.1 seed.2 formulas solver inventory
            beforeCaller before checkEmpty n p h source target memos initial realized fits reserved.head known dispatchObserved
          have padded : Fits (advance seed (source :: rest).length).2 reachedCaller.checked ∧
              Heap (fun guard => guard ∈ (advance seed (source :: rest).length).1)
                reachedCaller.checked.native.machine.heap := by
            refine ⟨bounded.1.mono (SourcePruningEnumerationIncomingReservation.advance_profile_ge (step seed) rest.length), ?_⟩
            intro key edge found
            exact SourcePruningEnumerationIncomingReservation.advance_alphabet_ge (step seed) rest.length
              (bounded.2 key edge found)
          cases possible with
          | none =>
              simp only [run, dispatchObserved] at observed
              have same := congrArg (fun output => output.2.1) observed
              dsimp only at same
              rw [← same]
              exact padded
          | some action =>
              cases raw : ExceptT.run (action before) with
              | nil =>
                  simp only [run, dispatchObserved, raw] at observed
                  have same := congrArg (fun output => output.2.1) observed
                  dsimp only at same
                  rw [← same]
                  exact padded
              | cons first tail =>
                  cases first with
                  | error fault =>
                      simp only [run, dispatchObserved, raw] at observed
                      have same := congrArg (fun output => output.2.1) observed
                      dsimp only at same
                      rw [← same]
                      exact padded
                  | ok pair =>
                      rcases pair with ⟨valueUnit, middle⟩
                      cases valueUnit
                      cases tail with
                      | cons second remaining =>
                          simp only [run, dispatchObserved, raw] at observed
                          have same := congrArg (fun output => output.2.1) observed
                          dsimp only at same
                          rw [← same]
                          exact padded
                      | nil =>
                          obtain ⟨next, final, post, querySame, middleRealized, middleTarget,
                            middleSelected, middleFits, middleKnown⟩ :=
                            observed_singleton seed formulas solver inventory beforeCaller before source target rest checkEmpty memos
                              initial realized targetPending selected fits reserved.head known dispatchObserved raw
                          simp only [run, dispatchObserved, raw] at observed
                          rw [← querySame] at observed
                          exact ih (step seed) next reachedCaller middle final post.context middleRealized middleTarget
                            middleSelected middleFits reserved.tail middleKnown observed

end MicroCFTA.SourcePruningEnumerationFold
