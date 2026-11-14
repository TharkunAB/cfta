import MicroCFTA.SourcePruningEnumerationIdentityPrefixResources
import MicroCFTA.SourcePruningEnumerationPrefixMass

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open InternedProbeProvenance SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open EnumerationCompressionFrame
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationPrefixAdmission (suspendedBound)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- One actual identity phase retains its original mass and admission facts. -/
theorem identity_checkpoint_resources
    (graph : Graph Symbol Constraint)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (metadata : Metadata Unit)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap property caller.checked.native.machine.heap)
    (uv : Nat)
    (chosen : SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata before = some (.expand uv)) :
    ∃ fuel,
      (∃ after : Cached,
        suspendedBound after.core ≤ suspendedBound before.core ∧
        ∀ extra,
          SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
            (fun _ _ _ node state => .done node state) graph [] none (fun _ _ => none) metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query =
          .parked after.core (some after)
            (some (ExceptT.run (SourcePruningEnumerationRestart.run none (fun _ _ => none) metadata after after.core))) ∧
          CurrentPrefixResources none (fun _ _ => none) metadata formulas solver inventory uv caller before memos profile property
            (SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
              (fun _ _ _ node state => .done node state) graph [] none (fun _ _ => none) metadata
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
              uv caller before memos.query)) ∨
      (∃ checked : Core,
        ∀ extra,
          SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
            (fun _ _ _ node state => .done node state) graph [] none (fun _ _ => none) metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query =
          .narrowed checked (.done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) caller.checked.native.machine.heap)
            (SourceCurrentAllocatedPartialState.advance caller
              (advancePhysical caller.checked ⟨caller.checked.native.machine.heap, caller.checked.operations⟩)
              caller.fourth caller.merge)
            memos.query (some []) none none none ∧
          CurrentPrefixResources none (fun _ _ => none) metadata formulas solver inventory uv caller before memos profile property
            (SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
              (fun _ _ _ node state => .done node state) graph [] none (fun _ _ => none) metadata
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
              uv caller before memos.query)) ∨
      (∃ (handle : Nat) (scs : List Suspended) (value : Node) (after : Cached),
        value ≠ .empty ∧ encodeNode value = some handle ∧
        EnumerationDriver.Ready uv after.core ∧
        after.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
        EnumerationReferences.IncomingAvoid uv after.core ∧
        scs.length ≤ suspendedBound before.core ∧
        suspendedBound after.core = suspendedBound before.core ∧
        ∀ extra,
          SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
            (fun _ _ _ node state => .done node state) graph [] none (fun _ _ => none) metadata
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
            uv caller before memos.query =
          .narrowed after.core (.done (value, some (pure () : EnumerateM Symbol Constraint Unit)) caller.checked.native.machine.heap)
            (SourceCurrentAllocatedPartialState.advance caller
              (advancePhysical caller.checked ⟨caller.checked.native.machine.heap, caller.checked.operations⟩)
              caller.fourth caller.merge)
            memos.query (some [.ok ((), after.core)]) (some after)
            (some [.ok ((false, metadata), after.core)]) none ∧
          CurrentPrefixResources none (fun _ _ => none) metadata formulas solver inventory uv caller before memos profile property
            (SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
              (fun _ _ _ node state => .done node state) graph [] none (fun _ _ => none) metadata
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
              uv caller before memos.query)) := by
  classical
  have selection : EnumerationPureSelection.next (fun _ => none) before = .expand uv :=
    Option.some.inj chosen
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨fuel, handle, scs, value, readAfter, repeated, after,
      stored, _decoded, encoded, _available, _closed, reads, checks, readFrame,
      afterReady, _afterPaths, _afterRealized, _afterCounts, _afterFlags, incoming, _pending, running⟩ :=
    SourcePruningEnumerationSelectedStep.runPrefix_identity_selected_complete
      graph [] none (fun _ _ => none) metadata caller before memos.query (fun _ => none) uv roots
      packet.context.ready.good.heap packet.safe selection realized paths counts flags
  obtain ⟨resourceFuel, resources⟩ := prefix_identity_complete_resources
    graph checkEmpty edgesOf metadata formulas solver inventory caller memos before packet profile property bounded known
  let bound := fuel + resourceFuel
  have current (extra : Nat) :
      CurrentPrefixResources none (fun _ _ => none) metadata formulas solver inventory uv caller before memos profile property
        (SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
          (fun _ _ _ node state => .done node state) graph [] none (fun _ _ => none) metadata
          (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
          uv caller before memos.query) := by
    have common : resourceFuel + (fuel + extra) = bound + extra := by dsimp only [bound]; omega
    simpa only [common] using resources (fuel + extra) uv chosen
  have readSuccess : Success (getValue fuel uv) before.core
      (.unenumerated (some handle) scs) readAfter := by
    rw [Success, ← Nat.add_zero fuel, reads 0]
    exact List.mem_singleton_self _
  have checkSuccess : Success
      (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap fuel uv handle scs)
      readAfter repeated after.core := by
    rw [Success, ← Nat.add_zero fuel, checks 0]
    exact List.mem_singleton_self _
  have shift (extra : Nat) : fuel + (resourceFuel + extra) = bound + extra := by
    dsimp only [bound]
    omega
  refine ⟨bound, ?_⟩
  cases repeated with
  | true =>
      have mass := SourcePruningEnumerationPrefixMass.parked_mass caller.checked.native.machine.heap
        fuel fuel uv handle scs before.core readAfter after.core packet.safe readSuccess checkSuccess
      refine Or.inl ⟨after, mass, ?_⟩
      intro extra
      have actual := (running (resourceFuel + extra) (bound + extra) (bound + extra) (bound + extra)).1 rfl
      rw [shift] at actual
      exact ⟨actual, current extra⟩
  | false =>
      have checkedFrame := SourcePruningEnumerationRecursionOrder.checkRepeated_false_frame
        caller.checked.native.machine.heap fuel uv handle scs readAfter after.core
        (readFrame.total packet.safe.1.total) checkSuccess
      have wholeFrame := readFrame.trans checkedFrame
      have mass : suspendedBound after.core = suspendedBound before.core :=
        SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after.core wholeFrame.values
      by_cases emptyValue : value = .empty
      · subst value
        refine Or.inr (Or.inl ⟨after.core, ?_⟩)
        intro extra
        have actual := ((running (resourceFuel + extra) (bound + extra) (bound + extra) (bound + extra)).2 rfl).1 rfl
        rw [shift] at actual
        exact ⟨actual, current extra⟩
      · have bucketLength : scs.length ≤ suspendedBound before.core := by
          have member : (.unenumerated (some handle) scs : UVarValue Symbol) ∈ before.core.values :=
            List.mem_of_getElem? stored
          unfold suspendedBound
          generalize before.core.values = values at member ⊢
          induction values with
          | nil => cases member
          | cons first rest ih =>
              rcases List.mem_cons.mp member with same | listed
              · subst first
                simp only [List.map_cons, List.sum_cons]
                exact Nat.le_add_right _ _
              · have bounded := ih listed
                simp only [List.map_cons, List.sum_cons]
                omega
        have afterStored : after.core.values[uv]? = some (.unenumerated (some handle) scs) := by
          simpa only [wholeFrame.values] using stored
        refine Or.inr (Or.inr ⟨handle, scs, value, after, emptyValue, encoded, afterReady,
          afterStored, incoming, bucketLength, mass, ?_⟩)
        intro extra
        have actual := ((running (resourceFuel + extra) (bound + extra) (bound + extra) (bound + extra)).2 rfl).2 emptyValue
        rw [shift] at actual
        exact ⟨actual, current extra⟩

end MicroCFTA.SourcePruningEnumerationSharedRecursive

#print axioms MicroCFTA.SourcePruningEnumerationSharedRecursive.identity_checkpoint_resources
