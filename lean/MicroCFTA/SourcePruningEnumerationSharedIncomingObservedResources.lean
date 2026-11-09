import MicroCFTA.SourcePruningEnumerationSharedIncomingQueryResources
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorkerActual

/-!
# Resources at observed shared incoming-query returns

Completed optional observations agree on their complete outcome and query
memo. Current admission therefore bounds the same checked state returned
by a supplied native query and optional check. Performed observations keep
their private snapshot. Skipped observations have no worker snapshot.

These proofs require successful native and completed optional observations.
They do not give resource bounds at arbitrary failed native observations.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedEnabledEmpty
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Worker" => SourceCurrentAllocatedSharedConjunctionWorker.call
local notation "budget" => SourceCurrentConjunctionTupleBudget.currentTupleBudget
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Any two completed optional checks retain the same full observation and query memo. -/
theorem optional_done_unique (flag : Bool)
    {p h P H : Nat} {query : Node} {before : Checked width} {memo : Fourth}
    {queries firstQueries secondQueries : Queries} {first second : Outcome width}
    {answer other : Bool}
    (one : (if flag then check p h query before memo queries else (.skipped before memo, queries)) =
      (first, firstQueries))
    (two : (if flag then check P H query before memo queries else (.skipped before memo, queries)) =
      (second, secondQueries))
    (oneCompleted : first.completed = some answer) (twoCompleted : second.completed = some other) :
    first = second ∧ firstQueries = secondQueries := by
  cases flag with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at one two
      exact Prod.mk.inj (one.symm.trans two)
  | true =>
      cases gate : SourceEndpointMemo.run query queries with
      | mk reached querySaved =>
          cases reached with
          | false =>
              simp only [↓reduceIte, check, gate, Bool.false_eq_true] at one two
              exact Prod.mk.inj (one.symm.trans two)
          | true =>
              simp only [↓reduceIte, check, gate] at one two
              cases firstCall : Worker p h budget query before memo with
              | failed fault checked saved snapshot =>
                  have impossible := oneCompleted
                  rw [← (Prod.mk.inj one).1, firstCall] at impossible
                  cases impossible
              | done firstAnswer firstAfter firstMemo firstSnapshot =>
                  cases secondCall : Worker P H budget query before memo with
                  | failed fault checked saved snapshot =>
                      have impossible := twoCompleted
                      rw [← (Prod.mk.inj two).1, secondCall] at impossible
                      cases impossible
                  | done secondAnswer secondAfter secondMemo secondSnapshot =>
                      obtain ⟨rfl, rfl, rfl, rfl⟩ :=
                        SourceCurrentAllocatedSharedConjunctionWorkerActual.call_done_unique
                          firstCall secondCall
                      simp only [firstCall] at one
                      simp only [secondCall] at two
                      exact Prod.mk.inj (one.symm.trans two)

end MicroCFTA.SourcePruningEnumerationSharedEnabledEmpty

namespace MicroCFTA.SourcePruningEnumerationSharedIncomingQuery
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedNativeCreditProfile (Admits)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Observed" => SourcePruningEnumerationSharedEnabledEmpty.Outcome
variable {bits : Nat}

/-- Current resources bound the exact observed return of a native query and shared check. -/
theorem raw_done_resources
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (alphabet : List Constraint) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (left right : Node) (checkEmpty : Bool) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (leftAvailable : Available beforeCaller.checked.native.machine.heap left)
    (rightAvailable : Available beforeCaller.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (fits : Fits profile beforeCaller.checked) (room : Admits bits profile)
    (known : Heap (fun guard => guard ∈ alphabet) beforeCaller.checked.native.machine.heap)
    {fuel p h : Nat} {query : Node} {queried : Checked (bits + 2)}
    {answer : Bool} {queries : Queries} {observed : Observed (bits + 2)}
    (native : SourceEqualityNativeDemand.execute fuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
      beforeCaller.checked = .done query queried)
    (phase : (if checkEmpty then
      SourcePruningEnumerationSharedEnabledEmpty.check p h query queried beforeCaller.fourth memos.query
      else (.skipped queried beforeCaller.fourth, memos.query)) = (observed, queries))
    (completed : observed.completed = some answer) :
    Fits (forecast alphabet profile) observed.state ∧
      Heap (fun guard => guard ∈ SourceCurrentGeneratedQueryGuardResources.forecast alphabet profile)
        observed.state.native.machine.heap := by
  obtain ⟨_next, result, reached, _producedAnswer, finish, _workerSaved, _final, savedQueries,
      _replacement, _handle, n, P, H, producedObservation, _source, _roots, _receipt,
      producedNative, producedPhase, producedCompleted, producedState, _producedMemo,
      _post, _querySame, _unfolding, _sound, _replacementSame, _available, _closed,
      _encoded, _decoded, _meaning, _disabled, _enabled, _queryFits, returnedFits,
      returnedCarrier, _fuelSame, _pSame, _hSame⟩ :=
    complete_resources alphabet profile formulas solver inventory beforeCaller left right checkEmpty memos
      initial leftAvailable rightAvailable leftClosed rightClosed fits room known
  have produced : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
      beforeCaller.checked = .done result reached := by
    simpa only [Nat.add_zero] using producedNative 0
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedNativeColdClosedExact.completed_unique fuel n _
    beforeCaller.checked queried reached query result native produced
  obtain ⟨sameObservation, _sameQueries⟩ :=
    SourcePruningEnumerationSharedEnabledEmpty.optional_done_unique checkEmpty phase
      (producedPhase P H (Nat.le_refl _) (Nat.le_refl _)) completed producedCompleted
  have sameState : observed.state = finish :=
    (congrArg SourcePruningEnumerationSharedEnabledEmpty.Outcome.state sameObservation).trans producedState
  rw [sameState]
  exact ⟨returnedFits, returnedCarrier⟩

end MicroCFTA.SourcePruningEnumerationSharedIncomingQuery
