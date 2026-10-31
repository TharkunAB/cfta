import MicroCFTA.SourceCurrentAllocatedNativeDispatchKnown
import MicroCFTA.SourceCurrentAllocatedNativeStoredDispatch
import MicroCFTA.SourcePruningEnumerationCachedFold
import MicroCFTA.SourcePruningEnumerationFoldAdmission

/-!
# Whole ordinary-cache transport through the actual cached fold

The source-list induction derives each next admission.
The raw fallback returns no cache. Its raw Core rows are outside this theorem.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceCurrentAllocatedNativeCachedFoldKnown
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed step Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
open EnumerationCompleteness (PendingAt PendingOrEliminated)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- Every actual returned fold cache keeps the same whole ordinary height bound. -/
theorem fold_known (bits bound : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached) (sources : List Nat)
    (checkEmpty : Bool) (n p h target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (targetPending : PendingAt before.core target)
    (selected : ∀ source ∈ sources, PendingOrEliminated before.core source)
    (fits : Fits seed.2 beforeCaller.checked) (reserved : Reserved bits seed sources.length)
    (annotated : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (stored : Stored beforeCaller.checked.native)
    (known : KnownOrdinary bound beforeCaller.checked.native.machine.heap before) :
    let actual := SourcePruningEnumerationCachedFold.run checkEmpty n p h sources
      beforeCaller before target memos.query
    match actual.2 with
    | none => True
    | some after => KnownOrdinary bound actual.1.2.1.checked.native.machine.heap after := by
  classical
  dsimp only
  induction sources generalizing seed inventory beforeCaller before memos with
  | nil =>
      change KnownOrdinary bound beforeCaller.checked.native.machine.heap before
      exact known
  | cons source rest ih =>
      have reservation : Reserved bits seed (rest.length + 1) := by
        simpa only [List.length_cons] using reserved
      have room := reservation.head
      have slots : source = target ∨ before.core.values[source]? = some .eliminated ∨
          ∃ (sourceNode targetNode : Option Nat) (sourceScs targetScs : List EnumerationState.Suspended),
            before.core.values[source]? = some (.unenumerated sourceNode sourceScs) ∧
            before.core.values[target]? = some (.unenumerated targetNode targetScs) := by
        rcases selected source (by simp) with ⟨sourceNode, sourceScs, sourceRead⟩ | eliminated
        · obtain ⟨targetNode, targetScs, targetRead⟩ := targetPending
          exact .inr (.inr ⟨sourceNode, targetNode, sourceScs, targetScs, sourceRead, targetRead⟩)
        · exact .inr (.inl eliminated)
      have dispatchKnown := SourceCurrentAllocatedNativeDispatchKnown.dispatch_known bits bound seed.2
        formulas solver inventory beforeCaller before checkEmpty n p h source target memos initial realized
        slots known fits room stored
      cases dispatchResult : SourcePruningEnumerationDispatch.dispatch checkEmpty n p h
          beforeCaller before.core source target memos.query with
      | mk outcome saved =>
          rcases saved with ⟨reachedCaller, savedQueries⟩
          cases outcome with
          | error _fault =>
              simp only [SourcePruningEnumerationCachedFold.run,
                SourcePruningEnumerationCachedAdapter.run, dispatchResult]
          | ok possible =>
              cases possible with
              | none =>
                  simp only [SourcePruningEnumerationCachedFold.run,
                    SourcePruningEnumerationCachedAdapter.run, dispatchResult]
              | some action =>
                  simp only [dispatchResult] at dispatchKnown
                  cases rawResult : ExceptT.run (action before.core) with
                  | nil =>
                      simp only [SourcePruningEnumerationCachedFold.run,
                        SourcePruningEnumerationCachedAdapter.run, dispatchResult, rawResult,
                        SourcePruningEnumerationCachedAdapter.adapt]
                      exact dispatchKnown.1
                  | cons first tail =>
                      cases first with
                      | error _rowError =>
                          simp only [SourcePruningEnumerationCachedFold.run,
                            SourcePruningEnumerationCachedAdapter.run, dispatchResult, rawResult,
                            SourcePruningEnumerationCachedAdapter.adapt]
                      | ok value =>
                          rcases value with ⟨valueUnit, core⟩
                          cases valueUnit
                          cases tail with
                          | cons _second _remaining =>
                              simp only [SourcePruningEnumerationCachedFold.run,
                                SourcePruningEnumerationCachedAdapter.run, dispatchResult, rawResult,
                                SourcePruningEnumerationCachedAdapter.adapt]
                          | nil =>
                              cases receipt : SourcePruningEnumerationCachedAdapter.adapt
                                  reachedCaller.checked.native.machine.heap before source target [.ok ((), core)] with
                              | none =>
                                  simp only [SourcePruningEnumerationCachedFold.run,
                                    SourcePruningEnumerationCachedAdapter.run, dispatchResult, rawResult, receipt]
                              | some recovered =>
                                  have rawKnown := dispatchKnown.2 action rfl core
                                    (by simp only [rawResult, List.mem_singleton])
                                  have nextKnown : KnownOrdinary bound reachedCaller.checked.native.machine.heap
                                      (EnumerationExpandableIndex.frame core recovered) := by
                                    intro handle scs member
                                    exact rawKnown handle scs member
                                  obtain ⟨next, final, post, querySame, nextRealized, nextPending,
                                    nextSelected, nextFits, nextAnnotated⟩ :=
                                    SourcePruningEnumerationFold.observed_singleton seed formulas solver inventory
                                      beforeCaller before.core source target rest checkEmpty memos initial realized
                                      targetPending selected fits room annotated dispatchResult rawResult
                                  have nextStored : Stored reachedCaller.checked.native := by
                                    simpa only [dispatchResult] using
                                      (SourceCurrentAllocatedNativeStoredDispatch.dispatch_native_stored seed.2
                                        checkEmpty n p h beforeCaller before.core source target memos.query
                                        initial.ready realized fits room stored)
                                  have recurse := ih (step seed) next reachedCaller
                                    (EnumerationExpandableIndex.frame core recovered) final post.context
                                    nextRealized nextPending nextSelected nextFits reservation.tail
                                    nextAnnotated nextStored nextKnown
                                  simp only [SourcePruningEnumerationCachedFold.run,
                                    SourcePruningEnumerationCachedAdapter.run, dispatchResult, rawResult, receipt]
                                  simpa only [querySame] using recurse

end MicroCFTA.SourceCurrentAllocatedNativeCachedFoldKnown
