import MicroCFTA.SourceCurrentAllocatedNativeStoredDispatch
import MicroCFTA.SourcePruningEnumerationFoldAdmission

/-!
# Native structural certificates at every actual fold return

The recursive entry comes from an actual singleton-success action observation.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeStoredFold
open EnumerationState EnumerationCorrectness EnumerationCompleteness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed step Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual fold outcome retains native certificates under the current original reservation. -/
theorem fold_native_stored (seed : Seed)
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
    (stored : Stored beforeCaller.checked.native) :
    Stored (SourcePruningEnumerationFold.run checkEmpty n p h sources
      beforeCaller before target memos.query).2.1.checked.native := by
  induction sources generalizing seed inventory beforeCaller before memos with
  | nil =>
      change Stored beforeCaller.checked.native
      exact stored
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty n p h
        beforeCaller before source target memos.query with ⟨outcome, reachedCaller, queries⟩
      have reachedStored := SourceCurrentAllocatedNativeStoredDispatch.dispatch_native_stored seed.2 checkEmpty n p h
        beforeCaller before source target memos.query initial.ready realized fits reserved.head stored
      rw [dispatchObserved] at reachedStored
      change Stored reachedCaller.checked.native at reachedStored
      cases outcome with
      | error fault =>
          simpa only [SourcePruningEnumerationFold.run, dispatchObserved] using reachedStored
      | ok possible =>
          cases possible with
          | none =>
              simpa only [SourcePruningEnumerationFold.run, dispatchObserved] using reachedStored
          | some action =>
              cases raw : ExceptT.run (action before) with
              | nil =>
                  simpa only [SourcePruningEnumerationFold.run, dispatchObserved, raw] using reachedStored
              | cons first tail =>
                  cases first with
                  | error fault =>
                      simpa only [SourcePruningEnumerationFold.run, dispatchObserved, raw] using reachedStored
                  | ok pair =>
                      rcases pair with ⟨valueUnit, middle⟩
                      cases valueUnit
                      cases tail with
                      | cons second remaining =>
                          simpa only [SourcePruningEnumerationFold.run, dispatchObserved, raw] using reachedStored
                      | nil =>
                          obtain ⟨next, final, post, querySame, middleRealized, middleTarget,
                            middleSelected, middleFits, middleKnown⟩ :=
                            SourcePruningEnumerationFold.observed_singleton seed formulas solver inventory
                              beforeCaller before source target rest checkEmpty memos initial realized targetPending
                              selected fits reserved.head known dispatchObserved raw
                          simp only [SourcePruningEnumerationFold.run, dispatchObserved, raw]
                          rw [← querySame]
                          exact ih (step seed) next reachedCaller middle final post.context middleRealized middleTarget
                            middleSelected middleFits reserved.tail middleKnown reachedStored

end MicroCFTA.SourceCurrentAllocatedNativeStoredFold
