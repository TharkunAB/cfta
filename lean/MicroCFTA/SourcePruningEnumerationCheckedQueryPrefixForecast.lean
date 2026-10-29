import MicroCFTA.SourcePruningEnumerationCheckedQueryPrefixBounded
import MicroCFTA.InternedValueMassBinderDepth

namespace MicroCFTA.InternedValueMassHeap
open InternedConstructorTemplates
variable {Symbol Guard : Type} {before after : State Symbol Guard} {bound : Nat}

/-- Preserved records inherit the later heap's complete payload bound. -/
theorem Stored.of_grows (stored : Stored bound after) (grows : Grows before after) :
    Stored bound before :=
  ⟨stored.positive,
    fun key value present => stored.nodes key value (grows.nodeRecords key value present),
    fun key edge present => stored.edges key edge (grows.edgeRecords key edge present)⟩

end MicroCFTA.InternedValueMassHeap

namespace MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion
open InternedConstructorTemplates InternedRecordCoherence SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {A : Type} {width steps bound : Nat} {control : Control A}
variable {before after : Checked width} {value : A}

/-- Every finite checked observation retains its physical records in the completed endpoint. -/
theorem Trace.prefix_extension
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (trace : Trace steps control before (.code (.pure value)) after)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap) :
    ∀ runtimeFuel, SourceRecursiveIntersectionKernel.Extension
      (execute runtimeFuel control before).state.native.machine after.native.machine := by
  induction steps generalizing control before with
  | zero =>
      cases trace
      intro runtimeFuel
      have same : (execute runtimeFuel (.code (.pure value)) after).state = after := by
        cases runtimeFuel <;> rfl
      rw [same]
      exact SourceRecursiveIntersectionKernel.Extension.refl _
  | succ count ih =>
      cases trace with
      | cons start initial resume middle final result count inputs one tail =>
          have effects := SourceCurrentAllocatedNativePhysicalExecution.step_invariants
            control before valid ready inputs
          have middleValid : SourceCurrentAllocatedNativePhysicalCache.Valid middle.native := by
            simpa only [one, Outcome.state] using effects.1
          have middleReady : SourceEqualityRequiredCache.Ready middle.native.machine.heap := by
            simpa only [one, Outcome.state] using effects.2.2.ready
          have middleExtension : SourceRecursiveIntersectionKernel.Extension
              before.native.machine middle.native.machine := by
            simpa only [one, Outcome.state] using effects.2.1
          have laterExtension := ih tail middleValid middleReady
          intro runtimeFuel
          cases runtimeFuel with
          | zero =>
              exact middleExtension.trans (laterExtension 0)
          | succ fuel =>
              change SourceRecursiveIntersectionKernel.Extension
                (execute (fuel + 1) control before).state.native.machine after.native.machine
              rw [execute, one]
              exact laterExtension fuel


/-- The endpoint payload ceiling bounds every actual checked observation. -/
theorem Trace.prefix_stored_of_final
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (trace : Trace steps control before (.code (.pure value)) after)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap)
    (stored : InternedValueMassHeap.Stored bound after.native.machine.heap) :
    ∀ runtimeFuel, InternedValueMassHeap.Stored bound
      (execute runtimeFuel control before).state.native.machine.heap := by
  intro runtimeFuel
  exact stored.of_grows (trace.prefix_extension valid ready runtimeFuel).heap

/-- The final body ceiling bounds each actual prefix of a completed checked trace. -/
theorem Trace.prefix_bounded_of_final
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (trace : Trace steps control before (.code (.pure value)) after)
    (valid : SourceCurrentAllocatedNativePhysicalCache.Valid before.native)
    (ready : SourceEqualityRequiredCache.Ready before.native.machine.heap)
    (bounded : InternedMuDepthInventory.Bounded after.native.machine.heap bound) :
    ∀ runtimeFuel, InternedMuDepthInventory.Bounded
      (execute runtimeFuel control before).state.native.machine.heap bound := by
  intro runtimeFuel key entry body depth ordinary present
  exact bounded key entry body depth ordinary
    ((trace.prefix_extension valid ready runtimeFuel).heap.nodeRecords key _ present)

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

/-- Original caller resources bound every stored payload at every checked query observation. -/
theorem native_prefix_stored_profile
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
    ∀ nativeFuel, InternedValueMassHeap.Stored (step profile).mass
      (SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode
          IntersectionEmptyDomain.emptyDomain left right))
        beforeCaller.checked).state.native.machine.heap := by
  obtain ⟨_next, _query, _queried, _source, _roots, receipt, _post, _done, returnedFits, _mass⟩ :=
    SourceCurrentAllocatedTargetQuery.finite_caller_resources profile formulas solver inventory
      beforeCaller left right memos initial fits room leftAvailable rightAvailable leftClosed rightClosed
  cases receipt.actual with
  | run trace =>
      exact trace.prefix_stored_of_final initial.ready.good.native initial.ready.good.heap returnedFits.stored

/-- Original caller resources compute one body ceiling for every checked query observation. -/
theorem native_prefix_bounded_profile
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
    ∀ nativeFuel, InternedMuDepthInventory.Bounded
      (SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode
          IntersectionEmptyDomain.emptyDomain left right))
        beforeCaller.checked).state.native.machine.heap (step profile).mass := by
  intro nativeFuel
  exact InternedValueMassBinderDepth.stored_bounded _ _
    (native_prefix_stored_profile profile formulas solver inventory beforeCaller left right memos
      initial leftAvailable rightAvailable leftClosed rightClosed fits room nativeFuel)

end MicroCFTA.SourcePruningEnumerationIncomingQuery
