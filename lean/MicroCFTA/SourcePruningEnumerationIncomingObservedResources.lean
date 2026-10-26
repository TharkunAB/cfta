import MicroCFTA.SourcePruningEnumerationIncomingQueryResources
import MicroCFTA.SourceCurrentAllocatedConjunctionWorkerActual

/-!
# Resources at observed incoming-query returns

Successful optional checks agree on their Boolean, complete checked state,
fourth memo and query memo. The initial resource producer therefore bounds
the same states returned by supplied literal successful executions.
-/
namespace MicroCFTA.SourcePruningEnumerationEnabledEmpty
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Successful optional checks identify every returned field at any successful bounds. -/
theorem optional_done_unique (flag : Bool)
    {p h P H : Nat} {query : Node} {before after later : Checked width}
    {memo saved current : Fourth} {queries firstQueries secondQueries : Queries}
    {answer other : Bool}
    (one : (if flag then check p h query before memo queries else (.done false before memo, queries)) =
      (.done answer after saved, firstQueries))
    (two : (if flag then check P H query before memo queries else (.done false before memo, queries)) =
      (.done other later current, secondQueries)) :
    answer = other ∧ after = later ∧ saved = current ∧ firstQueries = secondQueries := by
  cases flag with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at one two
      obtain ⟨outcomes, sameQueries⟩ := Prod.mk.inj (one.symm.trans two)
      obtain ⟨sameAnswer, sameState, sameMemo⟩ :=
        SourceCurrentAllocatedConjunctionWorker.Outcome.done.inj outcomes
      exact ⟨sameAnswer, sameState, sameMemo, sameQueries⟩
  | true =>
      cases observed : SourceEndpointMemo.run query queries with
      | mk reached querySaved =>
          cases reached with
          | false =>
              simp only [↓reduceIte, check, observed, Bool.false_eq_true] at one two
              obtain ⟨outcomes, sameQueries⟩ := Prod.mk.inj (one.symm.trans two)
              obtain ⟨sameAnswer, sameState, sameMemo⟩ :=
                SourceCurrentAllocatedConjunctionWorker.Outcome.done.inj outcomes
              exact ⟨sameAnswer, sameState, sameMemo, sameQueries⟩
          | true =>
              simp only [↓reduceIte, check, observed] at one two
              have first := (Prod.mk.inj one).1
              have second := (Prod.mk.inj two).1
              obtain ⟨sameAnswer, sameState, sameMemo⟩ :=
                SourceCurrentAllocatedConjunctionWorkerActual.call_done_unique first second
              exact ⟨sameAnswer, sameState, sameMemo,
                (Prod.mk.inj one).2.symm.trans (Prod.mk.inj two).2⟩

end MicroCFTA.SourcePruningEnumerationEnabledEmpty

namespace MicroCFTA.SourcePruningEnumerationIncomingQuery
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {bits : Nat}

/-- Initial resources bound the exact states returned by a successful query and optional check. -/
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
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    (known : Heap (fun guard => guard ∈ alphabet) beforeCaller.checked.native.machine.heap)
    {fuel p h : Nat} {query : Node} {queried checkedAfter : Checked (bits + 2)}
    {answer : Bool} {saved : Fourth} {queries : Queries}
    (native : SourceEqualityNativeDemand.execute fuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
      beforeCaller.checked = .done query queried)
    (phase : (if checkEmpty then
      SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth memos.query
      else (.done false queried beforeCaller.fourth, memos.query)) =
        (.done answer checkedAfter saved, queries)) :
    Fits (forecast alphabet profile) checkedAfter ∧
      Heap (fun guard => guard ∈ SourceCurrentGeneratedQueryGuardResources.forecast alphabet profile)
        checkedAfter.native.machine.heap := by
  obtain ⟨_next, result, reached, producedAnswer, finish, workerSaved, _final, savedQueries,
    _replacement, _handle, n, P, H, _source, _roots, _receipt, producedNative, producedPhase,
    _post, _querySame, _unfolding, _sound, _replacementSame, _available, _closed, _encoded,
    _decoded, _meaning, _disabled, _enabled, _queryFits, returnedFits, returnedCarrier,
    _fuelSame, _pSame, _hSame⟩ :=
    complete_resources alphabet profile formulas solver inventory beforeCaller left right checkEmpty memos
      initial leftAvailable rightAvailable leftClosed rightClosed fits room known
  have produced : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right))
      beforeCaller.checked = .done result reached := by
    simpa only [Nat.add_zero] using producedNative 0
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedNativeColdClosedExact.completed_unique fuel n _
    beforeCaller.checked queried reached query result native produced
  obtain ⟨_sameAnswer, sameState, _sameMemo, _sameQueries⟩ :=
    SourcePruningEnumerationEnabledEmpty.optional_done_unique checkEmpty phase
      (producedPhase P H (Nat.le_refl _) (Nat.le_refl _))
  rw [sameState]
  exact ⟨returnedFits, returnedCarrier⟩

end MicroCFTA.SourcePruningEnumerationIncomingQuery
