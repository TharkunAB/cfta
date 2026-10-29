import MicroCFTA.SourcePruningEnumerationIncomingNodeResources
import MicroCFTA.SourcePruningEnumerationCheckedQueryPrefixForecast

namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

/-- Original incoming admissions bound the actual caller at every observed native stop. -/
theorem observed_native_error_stored
    (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Core EnumGuard)
    (checkEmpty : Bool) (r n p h uv : Nat) (incoming : Node) (incomingScs : List Suspended)
    (memos : Memos) (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile)
    {fault : SourceEqualityNativeDemand.Outcome (bits + 2) Node}
    {afterCaller : Caller (bits + 2)} {savedQueries : Queries} {read : Core EnumGuard}
    (observed : run checkEmpty r n p h beforeCaller before uv incoming incomingScs memos.query =
      (.error (.inl fault), afterCaller, savedQueries, read)) :
    InternedValueMassHeap.Stored (SourceCurrentAllocatedNativeResourceForecast.step profile).mass
      afterCaller.checked.native.machine.heap := by
  rw [run] at observed
  cases foundEq : UnionFind.findRoot r before.representatives uv with
  | none =>
      simp only [foundEq] at observed
      cases observed
  | some found =>
      simp only [foundEq] at observed
      cases stored : before.values[found.representative]? with
      | none =>
          simp only [stored] at observed
          cases observed
      | some value =>
          cases value with
          | eliminated | enumerated =>
              simp only [stored] at observed
              cases observed
          | unenumerated oldNode oldScs =>
              simp only [stored] at observed
              cases oldNode with
              | none =>
                  cases encoded : encodeNode incoming <;>
                    simp only [encoded] at observed <;> cases observed
              | some oldHandle =>
                  cases decoded : lookupNode beforeCaller.checked.native.machine.heap oldHandle with
                  | none =>
                      simp only [decoded] at observed
                      cases observed
                  | some old =>
                      obtain ⟨value, found, resident, oldClosed⟩ := realized _ oldHandle oldScs stored
                      have same := Option.some.inj (found.symm.trans decoded)
                      subst value
                      have prefixStored := SourcePruningEnumerationIncomingQuery.native_prefix_stored_profile
                        profile formulas solver inventory beforeCaller incoming old memos initial
                        available resident closed oldClosed fits room
                      simp only [decoded] at observed
                      cases native : SourceEqualityNativeDemand.execute n
                          (.code (SourceRecursiveIntersectionCode.requestNode
                            IntersectionEmptyDomain.emptyDomain incoming old)) beforeCaller.checked with
                      | yielded | failed | constraintError | blocked =>
                          simp only [native] at observed
                          have callerSame := congrArg (fun output => output.2.1) observed
                          dsimp only at callerSame
                          rw [← callerSame]
                          simpa only [native, SourceEqualityNativeDemand.Outcome.state,
                            SourceCurrentAllocatedPartialState.advance] using prefixStored n
                      | done query queried =>
                          simp only [native] at observed
                          cases phase : (if checkEmpty then
                              SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth memos.query
                              else (.done false queried beforeCaller.fourth, memos.query)) with
                          | mk outcome queries =>
                              simp only [phase] at observed
                              cases outcome with
                              | failed => cases observed
                              | done answer checkedAfter saved =>
                                  cases encoded : encodeNode (if answer then .empty else query) <;>
                                    simp only [encoded] at observed <;> cases observed

end MicroCFTA.SourcePruningEnumerationIncomingNode
