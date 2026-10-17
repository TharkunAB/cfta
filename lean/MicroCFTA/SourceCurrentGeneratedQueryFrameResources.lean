import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources

/-!
# Initial query resources without a finite input cap

Closed resident operands construct the exact native query and its next
inventory. The trace retains the universal conditional joint cache laws.
Input caps are needed only when a caller asks for a result cap.
The complete return retains its original numeric forecast and query Frame.
-/
namespace MicroCFTA.SourceCurrentGeneratedQueryFrameResources
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapKernelJoint (Context)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
local notation "credit" => SourceCurrentAllocatedRecursiveMassTrace.credit
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The same actual query retains exact language, its full Frame, and initial numeric resources. -/
structure Receipt (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (fuel : Nat) (left right : Value Symbol Guard) (before : Checked width)
    (value : Value Symbol Guard) (after : Checked width) (memos : Memos) : Prop where
  /-- The actual return has exact intersection language and global memo laws. -/
  query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver inventory left right before value after memos
  /-- The same inventory and state admit the next query. -/
  frame : Frame formulas solver inventory after
  /-- The instruction count belongs to this exact physical trace. -/
  trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel
    (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before (.code (.pure value)) after
  /-- The initial profile bounds the literal trace length. -/
  count : fuel ≤ instructionBound profile.nodes profile.edges profile.mass
  /-- The initial computed fuel returns the same complete state. -/
  done : execute (instructionBound profile.nodes profile.edges profile.mass + 1)
    (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before = .done value after
  /-- The complete returned state fits the initial one-query forecast. -/
  fits : Fits (SourceCurrentAllocatedNativeResourceForecast.step profile) after
  /-- The returned payload fits the same initial mass schedule. -/
  mass : InternedValueMass.value value ≤
    massAfter (instructionBound profile.nodes profile.edges profile.mass) profile.mass

private theorem after_frame
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked width) (frame : Frame formulas solver inventory before)
    (same : before.native.machine.heap = inventory.source)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available inventory.source left) (rightAvailable : Available inventory.source right)
    (leftValid : (inventory.inputs (SourceEqualityPCSGuard.holds formulas solver)).valid (inputOf left))
    (rightValid : (inventory.inputs (SourceEqualityPCSGuard.holds formulas solver)).valid (inputOf right))
    (fuel : Nat) (value : Value Symbol Guard) (after : Checked width)
    (receipt : SourceCurrentAllocatedNativeCoveredQuery.Receipt inventory.source formulas solver
      (inventory.inputs (SourceEqualityPCSGuard.holds formulas solver)) fuel left right before value after) :
    Frame formulas solver inventory after := by
  let source := inventory.source
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let inputs := inventory.inputs holds
  let domains := SourceRecursiveIntersectionSourceInventory.domains source
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have current := SourceCurrentAllocatedRecursivePrefixState.initial source domains before frame.ready.good frame.ready.semantic same
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have ready : NodeReady before.native.machine request :=
    ⟨empty_domain _, leftAvailable.grows source _ frame.context.growth frame.context.history,
      rightAvailable.grows source _ frame.context.growth frame.context.history⟩
  have physical := SourceCurrentAllocatedRecursivePrefixCode.request_node source domains request before.native.machine
    ready scope (SourceRecursiveIntersectionSourceInventory.empty_mem source)
  have certificate : SourceCurrentConstrainedCapCheckedJointControl.Certified Plain source
      (.code (requestNode request.domain left right)) before.native.machine
      (fun _ result => SourceCurrentConstrainedCapCheckedJointCode.NodeLaw Plain source request result) :=
    fun _ _ _ _ _ law => law
  have joint := SourceCurrentConstrainedCapCheckedJointTrace.completed inventory.facts
    (SourceCurrentAllocatedRecursiveDomainCode.source_closed source inventory.facts) fuel
    (.code (requestNode request.domain left right)) before after value _ _ current physical (fun _ => trivial)
    frame.context certificate frame.joint receipt.trace
  have originalInputs : ∀ input, inputs.valid input → OriginalInput source input :=
    SourceCurrentAllocatedNativeInputInventoryModels.reachable_original source inventory.facts holds inventory.roots
      inventory.originals inventory.available inventory.closed
  have admitted : SourceCurrentAllocatedNativeAdmissionCache.NodeCovered inputs request :=
    ⟨⟨leftOriginal, rightOriginal, leftValid, rightValid⟩, SourceCurrentAllocatedNativePairAdmission.empty_seen inputs⟩
  have captured := SourceCurrentConstrainedCapCheckedJointOriginTrace.Trace.origins source holds inputs
    inventory.facts originalInputs receipt.trace (fun final value => Available final.heap value)
    frame.ready.good frame.ready.semantic frame.context.growth frame.context.history (fun _ => trivial) frame.origins
    (SourceCurrentAllocatedNativeAdmissionCode.requestNode_certified source holds inputs request before.native.machine scope admitted)
  have effects := SourceCurrentAllocatedNativeTraceEffects.effects receipt.trace frame.ready.good frame.ready.semantic
    frame.ready.costs (fun _ => trivial)
  exact ⟨⟨effects.1, effects.2.1.ready.semantic, effects.2.1.ready.costs, receipt.scopedCache, receipt.idle⟩,
    ⟨receipt.contextual, receipt.covered, joint.context.growth, joint.context.history⟩,
    joint.context, joint.stored, captured.1⟩

/-- Initial room and closed resident operands construct the full query Frame without input caps. -/
theorem complete (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked (bits + 2)) (frame : Frame formulas solver inventory before)
    (fits : Fits profile before) (room : Room bits profile)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ next fuel value after, Receipt profile formulas solver next fuel left right before value after memos := by
  have actualRoom := fits.room room
  let source := before.native.machine.heap
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  let next := SourceCurrentAllocatedNativeInventoryRebase.extend inventory source frame.ready.good.native.machine.1
    frame.admitted.growth frame.admitted.history left right leftAvailable rightAvailable leftClosed rightClosed
  have rebased := SourceCurrentAllocatedNativeInventoryRebase.rebase formulas solver inventory before frame.ready.good
    frame.admitted left right leftAvailable rightAvailable leftClosed rightClosed
  have jointRebased := SourceCurrentConstrainedCapCheckedJointRebase.rebase Plain inventory.source before.native
    inventory.facts frame.admitted.growth frame.admitted.history frame.ready.good.native frame.origins frame.joint
  have nextContext : Context Plain next.source before.native.machine :=
    ⟨frame.ready.good.native.machine, frame.context.semantic, frame.context.guards, grows_refl _, extends_refl _⟩
  have nextFrame : Frame formulas solver next before :=
    ⟨frame.ready, rebased.1, nextContext, jointRebased.1, jointRebased.2⟩
  have facts := frame.ready.good.native.machine.1
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent rightAvailable rightClosed
  have ranges := (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before frame.ready.good
    frame.ready.semantic left right leftOriginal rightOriginal leftAvailable rightAvailable
    actualRoom.1 actualRoom.2.1 actualRoom.2.2).1
  obtain ⟨fuel, value, after, covered⟩ := SourceCurrentAllocatedNativeCoveredQuery.query_complete
    next.source next.facts formulas solver (next.inputs holds) before frame.ready.good rebased.1.contextual
    rebased.1.covered frame.ready.scopedCache frame.ready.semantic frame.ready.idle (grows_refl _) (extends_refl _)
    left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
    rebased.2.2.2.1 rebased.2.2.2.2 ranges
  have finalFrame := after_frame formulas solver next before nextFrame rfl left right leftOriginal rightOriginal
    leftAvailable rightAvailable rebased.2.2.2.1 rebased.2.2.2.2 fuel value after covered
  have effects := SourceCurrentAllocatedNativeTraceEffects.effects covered.trace frame.ready.good frame.ready.semantic
    frame.ready.costs (fun _ => trivial)
  obtain ⟨events, runs, silent, globals⟩ := SourceCurrentAllocatedNativeGlobalMemos.trace_memos covered.trace
    frame.ready.good frame.ready.semantic frame.ready.costs (fun _ => trivial) memos valid
  have query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver next left right before value after memos :=
    ⟨.run covered.trace, finalFrame.ready, finalFrame.admitted, effects.2.1, effects.2.2, covered.result,
      covered.closed, covered.meaning, globals, events, runs, silent⟩
  have completes : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) :=
    SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right
      leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed
  have scope := initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable
  have ready : NodeReady before.native.machine request := ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have count := SourceCurrentAllocatedNativeInstructionTrace.node_prefix source facts holds request scope completes
    covered.trace frame.ready.good ready (grows_refl _) (extends_refl _)
  have initialCount := SourceCurrentAllocatedNativeComputedBudget.nodeBudget_le source facts holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed fits.stored
  have larger := SourceCurrentAllocatedNativeComputedBudget.instructionBound_mono fits.nodes fits.edges (Nat.le_refl profile.mass)
  have total : fuel ≤ instructionBound profile.nodes profile.edges profile.mass := Nat.le_trans (Nat.le_trans count initialCount) larger
  have exactResult := done_stable (fuel + 1) (instructionBound profile.nodes profile.edges profile.mass - fuel)
    (.code (requestNode request.domain request.left request.right)) before after value covered.done
  have sameFuel : fuel + 1 + (instructionBound profile.nodes profile.edges profile.mass - fuel) =
      instructionBound profile.nodes profile.edges profile.mass + 1 := by omega
  rw [sameFuel] at exactResult
  obtain ⟨_inputs, _certificate, _lastGood, _fields, stored, nodes, edges, domains⟩ :=
    SourceCurrentAllocatedNativeWidthTrace.prefix_bound covered.trace frame.ready.good (fun _ => trivial) fits.stored
      (SourceRecursiveIntersectionCodeMass.request_node request.domain request.left request.right before.native.machine profile.mass ready)
  have massBound := SourceCurrentAllocatedRecursiveMassMonotone.massAfter_count_mono total profile.mass
  have credits := SourceCurrentAllocatedRecursiveMassMonotone.credit_count_mono total profile.mass
  refine ⟨next, fuel, value, after, query, finalFrame, covered.trace, total, exactResult, ?_, ?_⟩
  · exact ⟨Nat.le_trans nodes (Nat.add_le_add fits.nodes credits),
      Nat.le_trans edges (Nat.add_le_add fits.edges credits), Nat.le_trans domains (Nat.add_le_add fits.domains total),
      stored.mono massBound⟩
  · exact Nat.le_trans (InternedValueMassHeap.available after.native.machine.heap stored value covered.result) massBound

end MicroCFTA.SourceCurrentGeneratedQueryFrameResources
