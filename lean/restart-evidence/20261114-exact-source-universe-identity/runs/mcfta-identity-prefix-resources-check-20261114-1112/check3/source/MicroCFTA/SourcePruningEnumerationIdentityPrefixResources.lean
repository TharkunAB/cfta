import MicroCFTA.SourcePruningEnumerationSharedPrefixResources
import MicroCFTA.SourcePruningEnumerationIdentityCompletion

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open InternedProbeProvenance SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open EnumerationCompressionFrame
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {width : Nat}
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- An actual repeated check retains the stored dependency levels. -/
private theorem identity_repeated_order
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (before readAfter after : Core) (fuel uv handle : Nat) (scs : List Suspended)
    (ready : EnumerationDriver.Ready uv readAfter)
    (stored : before.values[uv]? = some (.unenumerated (some handle) scs))
    (readFrame : Frame before readAfter)
    (checked : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      readAfter true after) :
    after.counter = before.counter ∧
      ∀ level frontier, EnumerationOrder.Stratified before level frontier →
        EnumerationOrder.Stratified after level frontier := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) readAfter true after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using checked
      exact (success_failure .unresolvedReference readAfter after true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at checked
        obtain ⟨root, resolved, reading, continued⟩ := (success_bind _ _ _ _ _).mp checked
        have same : root = uv :=
          (EnumerationDriver.representative_root fuel uv root readAfter resolved
            ready.safe ready.inside ready.root reading).1
        subst root
        have resolvedFrame := representative_frame fuel uv uv readAfter resolved ready.safe.1.total reading
        by_cases seen : recursionKey handle scs ∈ resolved.recursionAncestry uv
        · have shape : after = {resolved with values := resolved.values.set uv (.unenumerated (some handle) [])} := by
            simpa [Success, setValue, get, getThe, MonadStateOf.get, modify, modifyGet,
              MonadStateOf.modifyGet, bind, pure, StateT.pure, StateT.bind, StateT.get, StateT.modifyGet,
              ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run, seen, eq_comm] using continued
          have written : Success (setValue uv (.unenumerated (some handle) [])) resolved () after :=
            (EnumerationDriver.modify_success _ resolved after).mpr shape
          exact SourcePruningEnumerationParkedRestart.parked_order uv handle scs before resolved after
            stored (readFrame.trans resolvedFrame) written
        · simp [Success, get, getThe, MonadStateOf.get, bind, pure, StateT.pure, StateT.bind,
            StateT.get, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.mk, ExceptT.run, seen] at continued
      · simp [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, Success, pure,
          StateT.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at checked

variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The actual identity prefix retains its original packet and resource bounds. -/
theorem prefix_identity_complete_resources
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (metadata : Metadata Unit)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap) :
    ∃ bound, ∀ extra selected,
      SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata before = some (.expand selected) →
      CurrentPrefixResources none (fun _ _ => none) metadata formulas solver inventory selected caller before memos profile property
        (SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
          (fun _ _ _ node state => .done node state) graph [] none (fun _ _ => none) metadata
          (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          selected caller before memos.query) := by
  classical
  let _ := (checkEmpty, edgesOf)
  by_cases offered : ∃ uv,
      SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata before = some (.expand uv)
  · obtain ⟨uv, chosen⟩ := offered
    have selection : EnumerationPureSelection.next (fun _ => none) before = .expand uv :=
      Option.some.inj chosen
    obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
    have beforeReady := SourcePruningEnumerationSelection.ready caller.checked.native.machine.heap
      before (fun _ => none) uv packet.safe roots paths counts flags selection
    obtain ⟨fuel, handle, scs, value, readAfter, repeated, after,
        stored, _decoded, encoded, _available, _closed, reads, checks, readFrame,
        afterReady, afterPaths, afterRealized, afterCounts, afterFlags, _incoming, pending, running⟩ :=
      SourcePruningEnumerationSelectedStep.runPrefix_identity_selected_complete
        graph [] none (fun _ _ => none) metadata caller before memos.query (fun _ => none) uv roots
        packet.context.ready.good.heap packet.safe selection realized paths counts flags
    have readSuccess : Success (getValue fuel uv) before.core
        (.unenumerated (some handle) scs) readAfter := by
      rw [Success, ← Nat.add_zero fuel, reads 0]
      exact List.mem_singleton_self _
    have checkSuccess : Success
        (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap fuel uv handle scs)
        readAfter repeated after.core := by
      rw [Success, ← Nat.add_zero fuel, checks 0]
      exact List.mem_singleton_self _
    have validAfter : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller after :=
      ⟨roots, afterPaths, afterReady.safe.1, afterRealized, afterCounts, afterFlags⟩
    have resources : SourceCurrentConstrainedCapGeneratedQueryResources.Fits
          (SourceCurrentConstrainedCapEditForecast.headProfile profile) caller.checked ∧
        SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap :=
      ⟨bounded.mono (SourceCurrentConstrainedCapEditForecast.headProfile_ge profile), known⟩
    have advanced : SourceCurrentAllocatedPartialState.advance caller
        (advancePhysical caller.checked ⟨caller.checked.native.machine.heap, caller.checked.operations⟩)
        caller.fourth caller.merge = caller := rfl
    have post : Post formulas solver inventory caller
        (SourceCurrentAllocatedPartialState.advance caller
          (advancePhysical caller.checked ⟨caller.checked.native.machine.heap, caller.checked.operations⟩)
          caller.fourth caller.merge) memos := by
      simpa only [advanced] using Post.refl packet.context
    refine ⟨fuel, ?_⟩
    intro extra selected observed
    have same : selected = uv := Next.expand.inj (Option.some.inj (observed.symm.trans chosen))
    subst selected
    cases repeated with
    | true =>
        have readReady := (EnumerationDriver.getValue_ready fuel uv before.core readAfter
          (.unenumerated (some handle) scs) beforeReady readSuccess).1
        obtain ⟨counter, ordered⟩ := identity_repeated_order caller.checked.native.machine.heap
          before.core readAfter after.core fuel uv handle scs readReady stored readFrame checkSuccess
        have afterPacket : Packet formulas solver inventory caller memos metadata after := by
          refine ⟨packet.context, afterReady.safe, pending packet.pending, validAfter, ?_, ?_⟩
          · obtain ⟨level, frontier, oldOrder⟩ := packet.ordered
            exact ⟨level, frontier, ordered level frontier oldOrder⟩
          · simpa only [counter] using packet.bounded
        rw [(running extra (fuel + extra) (fuel + extra) (fuel + extra)).1 rfl]
        exact ⟨⟨after, rfl, rfl, rfl, afterPacket⟩, resources⟩
    | false =>
        have checkedFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
          caller.checked.native.machine.heap fuel uv handle scs readAfter after.core
          (readFrame.total packet.safe.1.total) checkSuccess
        have wholeFrame := readFrame.trans checkedFrame
        have waiting : after.waiting = before.waiting := by
          have sameCounts : EnumerationCanonicalWaiting.Correct roots before.core.values after.waiting := by
            simpa only [wholeFrame.values] using afterCounts
          funext slot
          exact (sameCounts slot).trans (counts slot).symm
        have afterStored : after.core.values[uv]? = some (.unenumerated (some handle) scs) := by
          simpa only [wholeFrame.values] using stored
        have afterPacket : Packet formulas solver inventory caller memos metadata after := by
          refine ⟨packet.context, afterReady.safe, pending packet.pending, validAfter, ?_, ?_⟩
          · obtain ⟨level, frontier, oldOrder⟩ := packet.ordered
            exact ⟨level, frontier,
              EnumerationOrder.frame_stratified before.core after.core wholeFrame level frontier oldOrder⟩
          · simpa only [wholeFrame.counter] using packet.bounded
        by_cases emptyValue : value = .empty
        · rw [((running extra (fuel + extra) (fuel + extra) (fuel + extra)).2 rfl).1 emptyValue]
          refine ⟨?_, ?_⟩
          · exact ⟨rfl, rfl, value, caller.checked.native.machine.heap,
              (reject : EnumerateM Symbol Constraint Unit), memos, rfl, rfl, post, rfl,
              Or.inl ⟨emptyValue, rfl, rfl, rfl⟩⟩
          · simpa only [SourcePruningEnumerationSelectedStep.Resources, advanced] using resources
        · rw [((running extra (fuel + extra) (fuel + extra) (fuel + extra)).2 rfl).2 emptyValue]
          refine ⟨?_, ?_⟩
          · refine ⟨rfl, rfl, value, caller.checked.native.machine.heap,
              (pure () : EnumerateM Symbol Constraint Unit), memos, rfl, rfl, post, rfl, Or.inr ?_⟩
            exact ⟨handle, scs, after, emptyValue, encoded, rfl, rfl, rfl,
              afterReady, afterStored, waiting, by simpa only [advanced] using afterPacket⟩
          · simpa only [SourcePruningEnumerationSelectedStep.Resources, advanced] using resources
  · refine ⟨0, ?_⟩
    intro _ selected chosen
    exact False.elim (offered ⟨selected, chosen⟩)

end MicroCFTA.SourcePruningEnumerationSharedRecursive

#print axioms MicroCFTA.SourcePruningEnumerationSharedRecursive.prefix_identity_complete_resources
