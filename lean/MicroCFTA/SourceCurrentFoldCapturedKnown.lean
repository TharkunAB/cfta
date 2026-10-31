import MicroCFTA.SourceCurrentDispatchCapturedKnown
import MicroCFTA.SourcePruningEnumerationFoldAdmission

/-! The literal ordered fold retains the same entry captured cache on every tag. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentFoldCapturedKnown
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open EnumerationCorrectness EnumerationCompleteness
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourcePruningEnumerationIncomingReservation (Seed step Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {bits : Nat} [DecidableEq (EdgeKey Symbol Constraint)]
    [DecidableEq (Value Symbol Constraint)]

/-- Every returned caller retains an arbitrary cache known at the original entry. -/
theorem fold_captured (bound : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Core) (captured : Cached)
    (sources : List Nat) (checkEmpty : Bool) (n p h target : Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (realized : PendingRealized caller.checked.native.machine.heap before)
    (targetPending : PendingAt before target)
    (selected : ∀ source ∈ sources, PendingOrEliminated before source)
    (fits : Fits seed.2 caller.checked) (reserved : Reserved bits seed sources.length)
    (annotated : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (known : KnownOrdinary bound caller.checked.native.machine.heap captured) :
    KnownOrdinary bound (SourcePruningEnumerationFold.run checkEmpty n p h sources
      caller before target memos.query).2.1.checked.native.machine.heap captured := by
  induction sources generalizing seed inventory caller before memos with
  | nil => simpa only [SourcePruningEnumerationFold.run] using known
  | cons source rest ih =>
      have reservation : Reserved bits seed (rest.length + 1) := by
        simpa only [List.length_cons] using reserved
      have capturedKnown := SourceCurrentDispatchCapturedKnown.dispatch_captured bound seed.2
        formulas solver inventory caller before captured checkEmpty n p h source target memos memos.query
        initial realized fits reservation.head known
      cases dispatchResult : SourcePruningEnumerationDispatch.dispatch checkEmpty n p h
          caller before source target memos.query with
      | mk outcome saved =>
          rcases saved with ⟨reachedCaller, savedQueries⟩
          simp only [dispatchResult] at capturedKnown
          cases outcome with
          | error _fault => simpa only [SourcePruningEnumerationFold.run, dispatchResult] using capturedKnown
          | ok possible =>
              cases possible with
              | none => simpa only [SourcePruningEnumerationFold.run, dispatchResult] using capturedKnown
              | some action =>
                  cases rawResult : ExceptT.run (action before) with
                  | nil => simpa only [SourcePruningEnumerationFold.run, dispatchResult, rawResult] using capturedKnown
                  | cons first tail =>
                      cases first with
                      | error _rowError =>
                          simpa only [SourcePruningEnumerationFold.run, dispatchResult, rawResult] using capturedKnown
                      | ok value =>
                          rcases value with ⟨valueUnit, core⟩
                          cases valueUnit
                          cases tail with
                          | cons _second _remaining =>
                              simpa only [SourcePruningEnumerationFold.run, dispatchResult, rawResult] using capturedKnown
                          | nil =>
                              obtain ⟨next, final, post, querySame, nextRealized,
                                nextPending, nextSelected, nextFits, nextAnnotated⟩ :=
                                SourcePruningEnumerationFold.observed_singleton seed formulas solver inventory
                                  caller before source target rest checkEmpty memos initial realized targetPending
                                  selected fits reservation.head annotated dispatchResult rawResult
                              have tailKnown := ih (step seed) next reachedCaller core final
                                post.context nextRealized nextPending nextSelected nextFits reservation.tail
                                nextAnnotated capturedKnown
                              simpa only [SourcePruningEnumerationFold.run, dispatchResult, rawResult, querySame] using tailKnown

end MicroCFTA.SourceCurrentFoldCapturedKnown
