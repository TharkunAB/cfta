import MicroCFTA.SourceCurrentParentUniformGuardAlphabet
import MicroCFTA.SourceCurrentEdgeCallNumeric
import MicroCFTA.SourceCurrentAllocatedPartialWorkerStability

/-!
# Uniform Parent bounds at observed outer edge returns

Initial semantic and numeric facts construct complete body and caller
receipts. Successful-return uniqueness identifies their full states with
an observed return. The observed fuels need no forecast comparison.
The carrier and common profile include both cold owners and ready hits.
-/
namespace MicroCFTA.SourceCurrentOuterEdgeGuardAlphabet
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Edge" => EdgeValue Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "UniformReserved" => SourceCurrentParentAlphabetReservation.UniformReserved
local notation "outputProfile" => SourceCurrentParentUniformEnvelope.profile
local notation "outputAlphabet" => SourceCurrentParentUniformGuardAlphabet.forecast
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

private theorem body_complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : EdgeRequest)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (entry : Profile) (fits : Fits entry before.checked)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (uniform : UniformReserved bits budget alphabet entry) :
    ∃ result after next final,
      SourceCurrentEdgeBodyNumeric.Receipt formulas solver next entry budget request before memos result after final ∧
      Fits (outputProfile budget alphabet entry) after.checked ∧
      Carrier (fun guard => guard ∈ outputAlphabet budget alphabet entry) after.checked.native.machine.heap := by
  have reserved := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory budget alphabet request
    before memos initial entry fits known inherited resident uniform
  obtain ⟨computed, state, next, final, receipt⟩ := SourceCurrentEdgeBodyNumeric.complete formulas solver inventory
    budget request before memos initial frame entry fits (fun _ => resident) (fun _ => inherited) reserved
  obtain ⟨loaded,result,checked,fourth,memo,_next,_final,_parent,numeric,carrier,done⟩ :=
    SourceCurrentParentUniformGuardAlphabet.complete formulas solver inventory budget alphabet request before memos
      initial frame entry fits known inherited resident uniform
  let bound := max (SourceCurrentParentForecast.residentFuel budget request before.checked entry)
    (SourceCurrentParentUniformEnvelope.fuel budget alphabet entry)
  have bodyDone := receipt.run 0 bound bound bound bound bound bound bound bound bound
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have parentDone := done bound bound bound bound bound bound bound bound bound
    (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have uniformDone : SourceCurrentAllocatedPartialWorker.edgeBody 0 bound bound bound bound bound bound bound bound bound
      budget request before = .done result (advance before checked fourth memo) := by
    simp only [SourceCurrentAllocatedPartialWorker.edgeBody,parentDone]
  obtain ⟨sameResult,sameState⟩ :=
    SourceCurrentAllocatedPartialWorkerStability.edgeBody_done_unique bodyDone uniformDone
  refine ⟨computed,state,next,final,receipt,?_,?_⟩
  · rw [sameState]
    exact numeric
  · rw [sameState]
    exact carrier

/-- Initial support derives the complete body receipt and common carrier at any successful fuels. -/
theorem edge_body
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : EdgeRequest)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (entry : Profile) (fits : Fits entry before.checked)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (uniform : UniformReserved bits budget alphabet entry)
    {f g s r e p h m c n : Nat} {result : Edge} {after : Caller (bits + 2)}
    (observed : SourceCurrentAllocatedPartialWorker.edgeBody f g s r e p h m c n budget request before = .done result after) :
    ∃ next final,
      SourceCurrentEdgeBodyNumeric.Receipt formulas solver next entry budget request before memos result after final ∧
      Fits (outputProfile budget alphabet entry) after.checked ∧
      Carrier (fun guard => guard ∈ outputAlphabet budget alphabet entry) after.checked.native.machine.heap := by
  obtain ⟨computed,state,next,final,receipt,numeric,carrier⟩ := body_complete formulas solver inventory budget alphabet
    request before memos initial frame entry fits known inherited resident uniform
  let bound := SourceCurrentParentForecast.residentFuel budget request before.checked entry
  have done := receipt.run 0 bound bound bound bound bound bound bound bound bound
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨sameResult,sameState⟩ := SourceCurrentAllocatedPartialWorkerStability.edgeBody_done_unique observed done
  subst computed state
  exact ⟨next,final,receipt,numeric,carrier⟩

/-- Initial owner support derives the full edge call at its arbitrary successful return. -/
theorem edge_call
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : EdgeRequest)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (entry : Profile) (fits : Fits entry before.checked)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (uniform : UniformReserved bits budget alphabet entry)
    {f g s r e p h m c n : Nat} {result : Edge} {after : Caller (bits + 2)}
    (observed : SourceCurrentAllocatedPartialWorker.edgeCall f g s r e p h m c n budget request before = .done result after) :
    ∃ next final,
      SourceCurrentEdgeCallNumeric.Receipt formulas solver next entry budget request before memos result after final ∧
      Fits (outputProfile budget alphabet entry) after.checked ∧
      Carrier (fun guard => guard ∈ outputAlphabet budget alphabet entry) after.checked.native.machine.heap := by
  generalize started : beginEdge request before = observation
  obtain ⟨handle,phase,running⟩ := observation
  cases phase with
  | ready value =>
      obtain ⟨same,receipt⟩ := SourceCurrentEdgeCallNumeric.ready formulas solver inventory budget request before memos
        initial frame entry fits inherited resident started
      subst running
      have done := SourceCurrentAllocatedPartialWorker.edgeCall_ready f g s r e p h m c n budget request before before handle value started
      obtain ⟨sameResult,sameState⟩ := SourceCurrentAllocatedPartialWorkerStability.edgeCall_done_unique observed done
      subst value after
      have enlarged : Le entry (outputProfile budget alphabet entry) :=
        (SourceCurrentInitialSelectionForecast.cover_ge _ _).trans (SourceCurrentMkEdgeNumeric.finalProfile_ge _ _)
      exact ⟨inventory,memos,receipt,fits.mono enlarged,
        fun key edge found => SourceCurrentParentUniformGuardAlphabet.initial_mem budget alphabet entry (known key edge found)⟩
  | evaluate original =>
      obtain ⟨runningContext,owner,_key,_cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start
        formulas solver initial inherited resident started
      have components := beginEdge_components request before
      rw [started] at components
      dsimp only at components
      obtain ⟨checked,_merge,_fourth,_nodes⟩ := components
      have runningFrame : Frame formulas solver inventory running.checked := by simpa only [checked] using frame
      have runningFits : Fits entry running.checked := by simpa only [checked] using fits
      have runningKnown : Carrier (fun guard => guard ∈ alphabet) running.checked.native.machine.heap := by
        simpa only [checked] using known
      have parentReserved := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory budget alphabet
        original running memos runningContext entry runningFits runningKnown owner.inherited owner.input uniform
      have reserved : SourceCurrentEdgeCallNumeric.Reserved bits budget request before entry := by
        simpa only [SourceCurrentEdgeCallNumeric.Reserved,started] using parentReserved
      obtain ⟨computed,state,next,final,receipt,_returned⟩ := SourceCurrentEdgeCallNumeric.evaluated formulas solver inventory
        budget request before memos initial frame entry fits inherited resident reserved started
      obtain ⟨bodyResult,middle,_next,_final,body,numeric,carrier⟩ := body_complete formulas solver inventory budget alphabet
        original running memos runningContext runningFrame entry runningFits runningKnown owner.inherited owner.input uniform
      let bound := max (SourceCurrentEdgeCallNumeric.fuel budget request before entry)
        (SourceCurrentParentForecast.residentFuel budget original running.checked entry)
      have done := receipt.run 0 bound bound bound bound bound bound bound bound bound
        (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
        (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      have bodyDone := body.run 0 bound bound bound bound bound bound bound bound bound
        (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
      have fullDone := SourceCurrentAllocatedPartialWorker.edgeCall_body_done 0 bound bound bound bound bound bound bound bound bound
        budget request original before running middle handle bodyResult started bodyDone
      have same := SourceCurrentAllocatedPartialWorkerStability.edgeCall_done_unique done fullDone
      have finalFits : Fits (outputProfile budget alphabet entry) state.checked := by rw [same.2]; exact numeric
      have finalCarrier : Carrier (fun guard => guard ∈ outputAlphabet budget alphabet entry) state.checked.native.machine.heap := by
        rw [same.2]
        exact carrier
      obtain ⟨sameResult,sameState⟩ := SourceCurrentAllocatedPartialWorkerStability.edgeCall_done_unique observed done
      subst computed state
      exact ⟨next,final,receipt,finalFits,finalCarrier⟩
  | busy =>
      simp only [SourceCurrentAllocatedPartialWorker.edgeCall,started] at observed
      cases observed
  | absent =>
      simp only [SourceCurrentAllocatedPartialWorker.edgeCall,started] at observed
      cases observed

end MicroCFTA.SourceCurrentOuterEdgeGuardAlphabet
