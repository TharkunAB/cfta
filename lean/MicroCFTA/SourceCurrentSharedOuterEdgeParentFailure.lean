import MicroCFTA.SourceCurrentSharedParentUniformEnvelope
import MicroCFTA.SourceCurrentAllocatedSharedPartialCallSteps
import MicroCFTA.SourceCurrentAllocatedSharedPartialWorker

/-!
# Initial reservations exclude local Parent faults

An edge demand can select an earlier captured owner. Its initial context
provides that owner's input facts. Uniform reservations complete its
Parent call at the supplied nine lower fuels. This excludes every Parent
fault without assuming that the enclosing outer call succeeds. The proof uses
the actual stored owner and the same nine observed lower bounds.
-/
namespace MicroCFTA.SourceCurrentSharedOuterEdgeParentFailure
open InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)]

/-- Initial owner support and sufficient lower fuels exclude every local Parent fault. -/
theorem edge_no_parent_failure
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : EdgeRequest)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked)
    (entry : Profile) (fits : Fits entry before.checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet)
      before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready
      before.checked.operations.constraints request.inherited)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (uniform : SourceCurrentSharedParentAlphabetReservation.UniformReserved bits budget alphabet entry)
    (f g s r e p h m c n : Nat)
    (hg : SourceCurrentSharedParentUniformEnvelope.fuel budget alphabet entry ≤ g)
    (hs : SourceCurrentSharedParentUniformEnvelope.fuel budget alphabet entry ≤ s)
    (hr : SourceCurrentSharedParentUniformEnvelope.fuel budget alphabet entry ≤ r)
    (he : SourceCurrentSharedParentUniformEnvelope.fuel budget alphabet entry ≤ e)
    (hp : SourceCurrentSharedParentUniformEnvelope.fuel budget alphabet entry ≤ p)
    (hh : SourceCurrentSharedParentUniformEnvelope.fuel budget alphabet entry ≤ h)
    (hm : SourceCurrentSharedParentUniformEnvelope.fuel budget alphabet entry ≤ m)
    (hc : SourceCurrentSharedParentUniformEnvelope.fuel budget alphabet entry ≤ c)
    (hn : SourceCurrentSharedParentUniformEnvelope.fuel budget alphabet entry ≤ n)
    (observation : SourceCurrentAllocatedSharedParentWorker.Fault (bits + 2))
    (after : Caller (bits + 2)) :
    SourceCurrentAllocatedSharedPartialWorker.edgeCall f g s r e p h m c n budget request before ≠
      .failed (.parent observation) after := by
  intro failed
  generalize started : beginEdge request before = demanded
  obtain ⟨handle, phase, running⟩ := demanded
  cases phase with
  | ready value =>
      simp only [SourceCurrentAllocatedSharedPartialWorker.edgeCall, started] at failed
      cases failed
  | evaluate original =>
      obtain ⟨runningContext, owner, _key, _cell⟩ :=
        SourceCurrentAllocatedSharedPartialCallSteps.edge_start formulas solver initial inherited resident started
      have components := beginEdge_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checked, _merge, _fourth, _nodes⟩ := components
      have runningFrame : Frame formulas solver inventory running.checked := by
        simpa only [checked] using frame
      have runningFits : Fits entry running.checked := by
        simpa only [checked] using fits
      have runningKnown : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet)
          running.checked.native.machine.heap := by
        simpa only [checked] using known
      obtain ⟨_loaded, result, state, fourth, memo, _next, _final, _receipt, _numeric, done⟩ :=
        SourceCurrentSharedParentUniformEnvelope.complete formulas solver inventory budget alphabet original
          running memos runningContext runningFrame entry runningFits runningKnown
          owner.inherited owner.input uniform
      have parentDone := done g s r e p h m c n hg hs hr he hp hh hm hc hn
      simp only [SourceCurrentAllocatedSharedPartialWorker.edgeCall, started,
        SourceCurrentAllocatedSharedPartialWorker.edgeBody, parentDone,
        SourceCurrentAllocatedSharedPartialWorker.Outcome.bind] at failed
      cases failed
  | busy =>
      simp only [SourceCurrentAllocatedSharedPartialWorker.edgeCall, started] at failed
      cases failed
  | absent =>
      simp only [SourceCurrentAllocatedSharedPartialWorker.edgeCall, started] at failed
      cases failed

end MicroCFTA.SourceCurrentSharedOuterEdgeParentFailure
