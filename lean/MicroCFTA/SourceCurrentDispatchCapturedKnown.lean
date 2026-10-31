import MicroCFTA.SourceCurrentAllocatedNativeIncomingOldKnown
import MicroCFTA.SourceCurrentConjunctionCallPost
import MicroCFTA.SourcePruningEnumerationDispatch

/-! Every actual dispatcher outcome retains the same entry captured cache. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentDispatchCapturedKnown
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation (PendingRealized)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {bits width : Nat} [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

theorem check_captured (bound p h : Nat) (query : Node)
    (caller : Caller width) (memos : Memos) (queries : Queries) (captured : Cached)
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    (context : Context formulas solver inventory caller memos)
    (available : Available caller.checked.native.machine.heap query) (closed : query.free = [])
    (known : KnownOrdinary bound caller.checked.native.machine.heap captured) :
    KnownOrdinary bound (SourcePruningEnumerationEnabledEmpty.check p h query
      caller.checked caller.fourth queries).1.state.native.machine.heap captured := by
  cases Subsingleton.elim (inferInstance : DecidableEq Node)
    (fun a b => Classical.propDecidable (a = b))
  letI : DecidableEq Node := fun a b => Classical.propDecidable (a = b)
  have callKnown := SourceSizedPrefixKnownOrdinaryHeap.post_known
    (SourceCurrentConjunctionCallPost.call_post p h 1000 query caller memos context available closed) known
  cases gate : (SourceEndpointMemo.run query queries).1
  · simpa [SourcePruningEnumerationEnabledEmpty.check, gate,
      SourceCurrentAllocatedPartialState.advance, SourceCurrentAllocatedConjunctionWorker.Outcome.state] using known
  · simpa [SourcePruningEnumerationEnabledEmpty.check, gate, SourceCurrentAllocatedPartialState.advance] using callKnown

private theorem after_query_captured (bound : Nat) (checkEmpty : Bool) (p h source target : Nat)
    (sourceScs targetScs : List Suspended) (query : Node) (queried : Checked width)
    (before : Caller width) (memos : Memos) (queries : Queries) (captured : Cached)
    {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    (context : Context formulas solver inventory
      (SourceCurrentAllocatedPartialState.advance before queried before.fourth before.merge) memos)
    (available : Available queried.native.machine.heap query) (closed : query.free = [])
    (known : KnownOrdinary bound queried.native.machine.heap captured) :
    KnownOrdinary bound (SourcePruningEnumerationDispatch.afterQuery (EnumGuard := Constraint)
      checkEmpty p h source target sourceScs targetScs query queried before queries).2.1.checked.native.machine.heap captured := by
  cases checkEmpty
  · simpa [SourcePruningEnumerationDispatch.afterQuery, SourceCurrentAllocatedPartialState.advance] using known
  · have checked := check_captured bound p h query
      (SourceCurrentAllocatedPartialState.advance before queried before.fourth before.merge)
      memos queries captured context available closed known
    dsimp only [SourceCurrentAllocatedPartialState.advance] at checked
    cases observed : SourcePruningEnumerationEnabledEmpty.check p h query queried before.fourth queries with
    | mk outcome saved =>
      simp only [observed] at checked
      cases outcome <;>
        simpa [SourcePruningEnumerationDispatch.afterQuery, observed, SourceCurrentAllocatedPartialState.advance,
          SourceCurrentAllocatedConjunctionWorker.Outcome.state] using checked

/-- The actual dispatcher retains any entry captured cache on every returned tag. -/
theorem dispatch_captured (bound : Nat) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Core) (captured : Cached)
    (checkEmpty : Bool) (n p h source target : Nat) (memos : Memos) (queries : Queries)
    (initial : Context formulas solver inventory caller memos)
    (realized : PendingRealized caller.checked.native.machine.heap before)
    (fits : Fits profile caller.checked) (room : Room bits profile)
    (known : KnownOrdinary bound caller.checked.native.machine.heap captured) :
    KnownOrdinary bound (SourcePruningEnumerationDispatch.dispatch checkEmpty n p h
      caller before source target queries).2.1.checked.native.machine.heap captured := by
  by_cases identical : source = target
  · simpa [SourcePruningEnumerationDispatch.dispatch, identical] using known
  cases sourceRead : before.values[source]? with
  | none => simpa [SourcePruningEnumerationDispatch.dispatch, identical, sourceRead] using known
  | some sourceValue => cases sourceValue with
    | eliminated => simpa [SourcePruningEnumerationDispatch.dispatch, identical, sourceRead] using known
    | enumerated fragment =>
      cases targetRead : before.values[target]? <;>
        simpa [SourcePruningEnumerationDispatch.dispatch, identical, sourceRead, targetRead] using known
    | unenumerated sourceNode sourceScs =>
      cases targetRead : before.values[target]? with
      | none => simpa [SourcePruningEnumerationDispatch.dispatch, identical, sourceRead, targetRead] using known
      | some targetValue => cases targetValue with
        | eliminated => simpa [SourcePruningEnumerationDispatch.dispatch, identical, sourceRead, targetRead] using known
        | enumerated fragment => simpa [SourcePruningEnumerationDispatch.dispatch, identical, sourceRead, targetRead] using known
        | unenumerated targetNode targetScs =>
          cases sourceNode with
          | none => simpa [SourcePruningEnumerationDispatch.dispatch, identical, sourceRead, targetRead] using known
          | some sourceHandle => cases targetNode with
            | none => simpa [SourcePruningEnumerationDispatch.dispatch, identical, sourceRead, targetRead] using known
            | some targetHandle =>
              obtain ⟨left, leftRead, leftAvailable, leftClosed⟩ := realized source sourceHandle sourceScs sourceRead
              obtain ⟨right, rightRead, rightAvailable, rightClosed⟩ := realized target targetHandle targetScs targetRead
              have nativeKnown := SourceCurrentAllocatedNativeIncomingOldKnown.native_query_old_known
                bits bound profile caller.checked captured left right n initial.ready
                leftAvailable rightAvailable leftClosed rightClosed fits room known
              have bounds := fits.room room
              simp only [SourcePruningEnumerationDispatch.dispatch, identical, ↓reduceIte,
                sourceRead, targetRead, leftRead, rightRead]
              cases actual : SourceEqualityNativeDemand.execute n
                  (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) caller.checked with
              | done query queried =>
                obtain ⟨next, _source, _roots, receipt, queryPost⟩ := SourceCurrentAllocatedTargetQuery.raw_done_caller_initial
                  bits n formulas solver inventory caller queried left right query memos initial
                  leftAvailable rightAvailable leftClosed rightClosed bounds.1 bounds.2.1 bounds.2.2 actual
                have queryKnown := SourceSizedPrefixKnownOrdinaryHeap.query_known receipt known
                exact after_query_captured bound checkEmpty p h source target sourceScs targetScs
                  query queried caller _ queries captured queryPost.context receipt.available receipt.closed queryKnown
              | yielded control current =>
                simpa [actual, SourceEqualityNativeDemand.Outcome.state, SourceCurrentAllocatedPartialState.advance] using nativeKnown
              | failed fault current =>
                simpa [actual, SourceEqualityNativeDemand.Outcome.state, SourceCurrentAllocatedPartialState.advance] using nativeKnown
              | constraintError message current =>
                simpa [actual, SourceEqualityNativeDemand.Outcome.state, SourceCurrentAllocatedPartialState.advance] using nativeKnown
              | blocked reason control current =>
                simpa [actual, SourceEqualityNativeDemand.Outcome.state, SourceCurrentAllocatedPartialState.advance] using nativeKnown

end MicroCFTA.SourceCurrentDispatchCapturedKnown
