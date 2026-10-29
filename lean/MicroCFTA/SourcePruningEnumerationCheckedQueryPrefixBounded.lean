import MicroCFTA.SourcePruningEnumerationIncomingQueryResources
import MicroCFTA.InternedMuDepthInventory

namespace MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
open InternedConstructorTemplates InternedRecordCoherence SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {A : Type} {width steps : Nat} {control : Control A}
variable {before after : Checked width} {value : A}

/-- A finite physical return trace bounds the heap at every runtime fuel. -/
theorem Trace.prefix_bounded
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (trace : Trace steps control before (.code (.pure value)) after)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap) :
    ∃ bound, ∀ runtimeFuel, InternedMuDepthInventory.Bounded
      (execute runtimeFuel control before).state.native.machine.heap bound := by
  induction steps generalizing control before with
  | zero =>
      cases trace
      refine ⟨maximumDepth (nodeInventory after.native.machine.heap) + 1, ?_⟩
      intro runtimeFuel
      have same : (execute runtimeFuel (.code (.pure value)) after).state = after := by
        cases runtimeFuel <;> rfl
      rw [same]
      exact InternedMuDepthInventory.initial_bounded _ valid.machine.1
  | succ count ih =>
      cases trace with
      | cons start initial resume middle final result count inputs one tail =>
          have effects := SourceCurrentAllocatedNativePhysicalExecution.step_invariants
            control before valid ready inputs
          have middleValid : SourceCurrentAllocatedNativePhysicalCache.Valid middle.native := by
            simpa only [one, Outcome.state] using effects.1
          have middleReady : SourceEqualityRequiredCache.Ready middle.native.machine.heap := by
            simpa only [one, Outcome.state] using effects.2.2.ready
          obtain ⟨laterBound, laterBounded⟩ := ih tail middleValid middleReady
          let entryBound := maximumDepth (nodeInventory before.native.machine.heap) + 1
          have entryBounded : InternedMuDepthInventory.Bounded before.native.machine.heap entryBound :=
            InternedMuDepthInventory.initial_bounded _ valid.machine.1
          refine ⟨max entryBound laterBound, ?_⟩
          intro runtimeFuel
          cases runtimeFuel with
          | zero =>
              change InternedMuDepthInventory.Bounded before.native.machine.heap (max entryBound laterBound)
              intro key entry body depth ordinary present
              exact Nat.lt_of_lt_of_le (entryBounded key entry body depth ordinary present)
                (Nat.le_max_left entryBound laterBound)
          | succ fuel =>
              have bounded := laterBounded fuel
              change InternedMuDepthInventory.Bounded
                (execute (fuel + 1) control before).state.native.machine.heap (max entryBound laterBound)
              rw [execute, one]
              intro key entry body depth ordinary present
              exact Nat.lt_of_lt_of_le (bounded key entry body depth ordinary present)
                (Nat.le_max_right entryBound laterBound)
end MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion

namespace MicroCFTA.SourcePruningEnumerationIncomingQuery
open InternedConstructorTemplates InternedProbeProvenance SourceCurrentAllocatedNativeInventoryState
open SourceCurrentAllocatedPartialInvariant SourceCurrentAllocatedNativeResourceForecast
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {bits : Nat}

/-- Original caller admission bounds every checked native observation of the query. -/
theorem native_prefix_bounded
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)]
    (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (left right : Node) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (leftAvailable : Available beforeCaller.checked.native.machine.heap left)
    (rightAvailable : Available beforeCaller.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (fits : Fits profile beforeCaller.checked) (room : Room bits profile) :
    ∃ bound, ∀ nativeFuel, InternedMuDepthInventory.Bounded
      (SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode
          IntersectionEmptyDomain.emptyDomain left right))
        beforeCaller.checked).state.native.machine.heap bound := by
  have actualRoom := fits.room room
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left
    beforeCaller.checked.native.machine.heap initial.ready.good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right
    beforeCaller.checked.native.machine.heap initial.ready.good.native.machine.1.coherent rightAvailable rightClosed
  have ranges := SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits beforeCaller.checked
    initial.ready.good initial.ready.semantic left right leftOriginal rightOriginal leftAvailable rightAvailable
    actualRoom.1 actualRoom.2.1 actualRoom.2.2
  obtain ⟨_next, _query, _queried, _source, _roots, receipt⟩ :=
    SourceCurrentAllocatedTargetQuery.finite formulas solver inventory left right beforeCaller.checked
      initial.ready initial.admitted leftAvailable rightAvailable leftClosed rightClosed ranges.1
      memos initial.globals
  cases receipt.actual with
  | run trace => exact trace.prefix_bounded initial.ready.good.native initial.ready.good.heap

end MicroCFTA.SourcePruningEnumerationIncomingQuery
