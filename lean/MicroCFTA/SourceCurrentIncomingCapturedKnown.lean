import MicroCFTA.SourceCurrentDispatchCapturedKnown
import MicroCFTA.SourcePruningEnumerationIncomingNode

/-! The literal incoming worker retains an arbitrary entry captured cache. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingCapturedKnown
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
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
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {bits : Nat} [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every incoming return retains the same arbitrary cache known at entry. -/
theorem incoming_captured (bound : Nat) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Core) (captured : Cached)
    (checkEmpty : Bool) (r n p h target : Nat) (incoming : Node) (scs : List Suspended)
    (memos : Memos) (queries : Queries)
    (initial : Context formulas solver inventory caller memos)
    (realized : PendingRealized caller.checked.native.machine.heap before)
    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits profile caller.checked) (room : Room bits profile)
    (known : KnownOrdinary bound caller.checked.native.machine.heap captured) :
    KnownOrdinary bound (SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
      caller before target incoming scs queries).2.1.checked.native.machine.heap captured := by
  cases rootRead : UnionFind.findRoot r before.representatives target with
  | none => simpa [SourcePruningEnumerationIncomingNode.run, rootRead] using known
  | some found =>
      cases oldRead : before.values[found.representative]? with
      | none => simpa [SourcePruningEnumerationIncomingNode.run, rootRead, oldRead] using known
      | some oldValue => cases oldValue with
        | eliminated => simpa [SourcePruningEnumerationIncomingNode.run, rootRead, oldRead] using known
        | enumerated fragment => simpa [SourcePruningEnumerationIncomingNode.run, rootRead, oldRead] using known
        | unenumerated oldNode oldScs =>
          cases oldNode with
          | none =>
              cases encoded : encodeNode incoming <;>
                simpa [SourcePruningEnumerationIncomingNode.run, rootRead, oldRead, encoded] using known
          | some oldHandle =>
              obtain ⟨old, oldLookup, oldAvailable, oldClosed⟩ := realized found.representative oldHandle oldScs oldRead
              have nativeKnown := SourceCurrentAllocatedNativeIncomingOldKnown.native_query_old_known
                bits bound profile caller.checked captured incoming old n initial.ready
                available oldAvailable closed oldClosed fits room known
              have bounds := fits.room room
              simp only [SourcePruningEnumerationIncomingNode.run, rootRead, oldRead, oldLookup]
              cases actual : SourceEqualityNativeDemand.execute n
                  (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old)) caller.checked with
              | done query queried =>
                obtain ⟨next, _source, _roots, receipt, queryPost⟩ := SourceCurrentAllocatedTargetQuery.raw_done_caller_initial
                  bits n formulas solver inventory caller queried incoming old query memos initial
                  available oldAvailable closed oldClosed bounds.1 bounds.2.1 bounds.2.2 actual
                have queryKnown := SourceSizedPrefixKnownOrdinaryHeap.query_known receipt known
                cases checkEmpty with
                | false =>
                    cases encoded : encodeNode query <;>
                      simpa [encoded, SourceCurrentAllocatedPartialState.advance, SourceCurrentAllocatedConjunctionWorker.Outcome.state] using queryKnown
                | true =>
                    have checkedKnown := SourceCurrentDispatchCapturedKnown.check_captured bound p h query
                      (SourceCurrentAllocatedPartialState.advance caller queried caller.fourth caller.merge)
                      _ queries captured queryPost.context receipt.available receipt.closed queryKnown
                    dsimp only [SourceCurrentAllocatedPartialState.advance] at checkedKnown
                    cases observed : SourcePruningEnumerationEnabledEmpty.check p h query queried caller.fourth queries with
                    | mk outcome savedQueries =>
                        simp only [observed] at checkedKnown
                        cases outcome with
                        | done answer checkedAfter saved =>
                            cases encoded : encodeNode (if answer then .empty else query) <;>
                              simpa [observed, encoded, SourceCurrentAllocatedPartialState.advance,
                                SourceCurrentAllocatedConjunctionWorker.Outcome.state] using checkedKnown
                        | failed fault checkedAfter saved =>
                            simpa [observed, SourceCurrentAllocatedPartialState.advance,
                              SourceCurrentAllocatedConjunctionWorker.Outcome.state] using checkedKnown
              | yielded control current =>
                  simpa [actual, SourceEqualityNativeDemand.Outcome.state, SourceCurrentAllocatedPartialState.advance] using nativeKnown
              | failed fault current =>
                  simpa [actual, SourceEqualityNativeDemand.Outcome.state, SourceCurrentAllocatedPartialState.advance] using nativeKnown
              | constraintError message current =>
                  simpa [actual, SourceEqualityNativeDemand.Outcome.state, SourceCurrentAllocatedPartialState.advance] using nativeKnown
              | blocked reason control current =>
                  simpa [actual, SourceEqualityNativeDemand.Outcome.state, SourceCurrentAllocatedPartialState.advance] using nativeKnown

end MicroCFTA.SourceCurrentIncomingCapturedKnown
