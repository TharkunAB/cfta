import MicroCFTA.SourceCurrentAllocatedNativeIncomingOldKnown
import MicroCFTA.SourceCurrentConjunctionWorkerEffects

set_option autoImplicit false
open scoped Classical

/-! Old-cache preservation at every actual incoming caller. -/
namespace MicroCFTA.SourceCurrentAllocatedNativeIncomingOldKnown
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentAllocatedFiniteOrdinaryStored (Stored)
open SourceSizedPrefixKnownOrdinary (KnownOrdinary)
open SourcePruningEnumerationObservation (PendingRealized)
open SourcePruningEnumerationNodes (lookupNode)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
private theorem physical_lookup_growth (before after : InternedConstructorTemplates.State Symbol Constraint)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (handle : Nat) (value : Node) (present : lookupNode before handle = some value) :
    lookupNode after handle = some value := by
  cases handle with
  | zero => exact present
  | succ identity =>
    cases issued : before.nodes.issued identity with
    | none => simp only [lookupNode, issued] at present; cases present
    | some key =>
      cases canonical : before.nodes.table key with
      | none => simp only [lookupNode, issued, canonical] at present; cases present
      | some entry =>
        by_cases winner : entry.identity = identity
        · simp only [lookupNode, issued, canonical, ite_eq_left winner] at present
          simpa only [lookupNode, history identity key issued, growth.nodes key entry canonical, ite_eq_left winner] using growth.nodeRecords key value present
        · simp only [lookupNode, issued, canonical, ite_eq_right winner] at present; cases present
variable [DecidableEq (EdgeKey Symbol Constraint)]
/-- Every actual current physical call endpoint retains each old decoded handle. -/
theorem call_lookup (p h budget : Nat) (query : Node) (before : Checked width) (memo : SourceCurrentEmptinessMemo.Memo)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before.native.machine.heap)
    (covered : Covered [] before.native.machine.heap) (available : Available before.native.machine.heap query) (closed : query.free = [])
    (handle : Nat) (value : Node) (present : lookupNode before.native.machine.heap handle = some value) :
    lookupNode (SourceCurrentAllocatedConjunctionWorker.call p h budget query before memo).state.native.machine.heap handle = some value := by
  have effects := SourceCurrentConjunctionWorkerEffects.allocated_call_effects p h budget memo query before semantic covered available closed
  have retained := physical_lookup_growth before.native.machine.heap _ effects.2.2.1 effects.2.2.2 handle value present
  apply Eq.mp ?_ retained
  congr; apply Subsingleton.elim
private theorem call_old_known (bound p h budget : Nat) (query : Node) (before : Checked width)
    (memo : SourceCurrentEmptinessMemo.Memo) (cached : Cached)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before.native.machine.heap)
    (covered : Covered [] before.native.machine.heap) (available : Available before.native.machine.heap query) (closed : query.free = [])
    (known : KnownOrdinary bound before.native.machine.heap cached) :
    KnownOrdinary bound (SourceCurrentAllocatedConjunctionWorker.call p h budget query before memo).state.native.machine.heap cached := by
  intro handle scs member
  obtain ⟨value, present, ordinary, height⟩ := known handle scs member
  exact ⟨value, call_lookup p h budget query before memo semantic covered available closed handle value present, ordinary, height⟩
private theorem check_old_known (bound p h : Nat) (query : Node) (before : Checked width)
    (memo : SourceCurrentEmptinessMemo.Memo) (queries : SourceEndpointMemo.Memos) (cached : Cached)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before.native.machine.heap)
    (covered : Covered [] before.native.machine.heap) (available : Available before.native.machine.heap query) (closed : query.free = [])
    (known : KnownOrdinary bound before.native.machine.heap cached) :
    KnownOrdinary bound (SourcePruningEnumerationEnabledEmpty.check p h query before memo queries).1.state.native.machine.heap cached := by
  unfold SourcePruningEnumerationEnabledEmpty.check
  dsimp only
  split
  · exact call_old_known bound p h 1000 query before memo cached semantic covered available closed known
  · exact known
/-- Every actual incoming caller retains the old cache, including a failed physical check. -/
theorem run_old_known (bits bound : Nat) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (r n p h uv : Nat) (incoming : Node)
    (incomingScs : List EnumerationState.Suspended) (memos : Memos) (queries : SourceEndpointMemo.Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (known : KnownOrdinary bound beforeCaller.checked.native.machine.heap before)
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile beforeCaller.checked) (room : Room bits profile)
    (stored : Stored beforeCaller.checked.native) :
    let result := SourcePruningEnumerationIncomingNode.run checkEmpty r n p h beforeCaller before.core uv incoming incomingScs queries
    Stored result.2.1.checked.native ∧ KnownOrdinary bound result.2.1.checked.native.machine.heap before := by
  constructor
  · exact SourceCurrentAllocatedNativeStoredIncoming.incoming_run_stored profile checkEmpty r n p h
      beforeCaller before.core uv incoming incomingScs queries initial.ready realized available closed fits room stored
  · cases reading : UnionFind.findRoot r before.core.representatives uv with
    | none => simpa only [SourcePruningEnumerationIncomingNode.run, reading] using known
    | some found =>
      simp only [SourcePruningEnumerationIncomingNode.run, reading]
      cases slot : before.core.values[found.representative]? with
      | none => exact known
      | some value => cases value with
        | enumerated _fragment => exact known
        | eliminated => exact known
        | unenumerated oldNode oldScs =>
          dsimp only []
          cases oldNode with
          | none => cases SourcePruningEnumerationNodes.encodeNode incoming <;> exact known
          | some oldHandle =>
            obtain ⟨old, decoded, oldAvailable, oldClosed⟩ := realized found.representative oldHandle oldScs slot
            have bounds := fits.room room
            have nativeKnown := native_query_old_known bits bound profile beforeCaller.checked before incoming old n
              initial.ready available oldAvailable closed oldClosed fits room known
            simp only [decoded]
            cases actual : SourceEqualityNativeDemand.execute n
                (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old)) beforeCaller.checked with
            | yielded control current =>
              change KnownOrdinary bound current.native.machine.heap before
              simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using nativeKnown
            | failed fault current =>
              change KnownOrdinary bound current.native.machine.heap before
              simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using nativeKnown
            | constraintError message current =>
              change KnownOrdinary bound current.native.machine.heap before
              simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using nativeKnown
            | blocked reason control current =>
              change KnownOrdinary bound current.native.machine.heap before
              simpa only [actual, SourceEqualityNativeDemand.Outcome.state] using nativeKnown
            | done query queried =>
              dsimp only []
              obtain ⟨next, _source, _roots, receipt, queryPost⟩ := SourceCurrentAllocatedTargetQuery.raw_done_caller_initial
                bits n formulas solver inventory beforeCaller queried incoming old query memos initial
                available oldAvailable closed oldClosed bounds.1 bounds.2.1 bounds.2.2 actual
              have queryKnown := SourceSizedPrefixKnownOrdinaryHeap.query_known receipt known
              have checkedKnown := check_old_known bound p h query queried beforeCaller.fourth queries before
                queryPost.context.ready.semantic.ready.semantic queryPost.context.ready.semantic.ready.covered receipt.available receipt.closed queryKnown
              generalize phaseEq : (if checkEmpty then SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries
                else (SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth, queries)) = phase
              obtain ⟨outcome, _phaseQueries⟩ := phase
              have phaseKnown : KnownOrdinary bound outcome.state.native.machine.heap before := by
                have observedPhase := congrArg Prod.fst phaseEq
                cases checkEmpty with
                | false =>
                  change SourceCurrentAllocatedConjunctionWorker.Outcome.done false queried beforeCaller.fourth = outcome at observedPhase
                  rw [← observedPhase]; exact queryKnown
                | true =>
                  change (SourcePruningEnumerationEnabledEmpty.check p h query queried beforeCaller.fourth queries).1 = outcome at observedPhase
                  simpa only [observedPhase] using checkedKnown
              cases outcome with
              | failed fault checkedAfter saved => exact phaseKnown
              | done answer checkedAfter saved =>
                cases answer <;> simp only [Bool.false_eq_true, ↓reduceIte]
                · cases SourcePruningEnumerationNodes.encodeNode query <;> exact phaseKnown
                · exact phaseKnown
end MicroCFTA.SourceCurrentAllocatedNativeIncomingOldKnown
