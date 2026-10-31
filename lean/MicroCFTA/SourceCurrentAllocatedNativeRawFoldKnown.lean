import MicroCFTA.SourceCurrentAllocatedNativeDispatchKnown
import MicroCFTA.SourceCurrentAllocatedNativeStoredDispatch
import MicroCFTA.SourcePruningEnumerationFoldAdmission
import MicroCFTA.SourcePruningEnumerationCachedFold

/-!
# Whole ordinary-value bounds for actual raw fold rows

The source-list induction derives every next admission.
The cached-fold corollary retains raw Core bounds even when no cache is returned.
It does not assert full terminal closure or global worker progress.
-/
set_option autoImplicit false

namespace MicroCFTA.SourceCurrentAllocatedNativeRawFoldKnown
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
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- Every successful actual raw fold Core keeps the same whole ordinary-value cap. -/
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
    let actual := SourcePruningEnumerationFold.run checkEmpty n p h sources
      beforeCaller before.core target memos.query
    match actual.1 with
    | .ok (some rows) => ∀ after : Core, Except.ok ((), after) ∈ rows →
        KnownOrdinary bound actual.2.1.checked.native.machine.heap {before with core := after}
    | _ => True := by
  classical
  dsimp only
  induction sources generalizing seed inventory beforeCaller before memos with
  | nil =>
      change ∀ after : Core, Except.ok ((), after) ∈ [Except.ok ((), before.core)] →
        KnownOrdinary bound beforeCaller.checked.native.machine.heap {before with core := after}
      intro after member
      have same : after = before.core := congrArg Prod.snd (Except.ok.inj (List.mem_singleton.mp member))
      subst after
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
          | error _fault => simp only [SourcePruningEnumerationFold.run, dispatchResult]
          | ok possible =>
              cases possible with
              | none => simp only [SourcePruningEnumerationFold.run, dispatchResult]
              | some action =>
                  simp only [dispatchResult] at dispatchKnown
                  cases rawResult : ExceptT.run (action before.core) with
                  | nil =>
                      simpa only [SourcePruningEnumerationFold.run, dispatchResult, rawResult] using
                        (dispatchKnown.2 action rfl)
                  | cons first tail =>
                      cases first with
                      | error _rowError =>
                          simpa only [SourcePruningEnumerationFold.run, dispatchResult, rawResult] using
                            (dispatchKnown.2 action rfl)
                      | ok value =>
                          rcases value with ⟨valueUnit, core⟩
                          cases valueUnit
                          cases tail with
                          | cons _second _remaining =>
                              simpa only [SourcePruningEnumerationFold.run, dispatchResult, rawResult] using
                                (dispatchKnown.2 action rfl)
                          | nil =>
                              have nextKnown := dispatchKnown.2 action rfl core
                                (by simp only [rawResult, List.mem_singleton])
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
                              have recurse := ih (step seed) next reachedCaller {before with core := core}
                                final post.context nextRealized nextPending nextSelected nextFits
                                reservation.tail nextAnnotated nextStored nextKnown
                              simp only [SourcePruningEnumerationFold.run, dispatchResult, rawResult]
                              simpa only [querySame] using recurse

open scoped Classical in
/-- The actual cached fold retains raw Core bounds independently of its optional cache. -/
theorem cached_raw_known (bits bound : Nat) (seed : Seed)
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
    match actual.1.1 with
    | .ok (some rows) => ∀ after : Core, Except.ok ((), after) ∈ rows →
        KnownOrdinary bound actual.1.2.1.checked.native.machine.heap {before with core := after}
    | _ => True := by
  have raw := fold_known bits bound seed formulas solver inventory beforeCaller before sources
    checkEmpty n p h target memos initial realized targetPending selected fits reserved annotated stored known
  simpa only [SourcePruningEnumerationCachedFold.erase] using raw

end MicroCFTA.SourceCurrentAllocatedNativeRawFoldKnown
