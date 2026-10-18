import MicroCFTA.SourceCurrentParentGuardAlphabet
import MicroCFTA.SourceCurrentParentUniformEnvelope

/-!
# A finite initial guard image for resident Parent calls

Exact own records and bounded child counts determine the carrier image.
Each full class forecast already enumerates ordered ambient guard words.
The initial carrier and Top cover both constructor and early branches.
No future Parent entry or returned guard is an input to this forecast.
-/
namespace MicroCFTA.SourceCurrentParentUniformGuardAlphabet
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentParentAlphabetReservation (ownRecordImage UniformReserved)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap

/-- Join all finite initial full-class guard images and retain the constructor guards. -/
noncomputable def forecast (budget : Nat) (alphabet : List Guard) (entry : Profile) : List Guard :=
  top :: (alphabet ++ (ownRecordImage alphabet).flatMap fun records =>
    (List.range (entry.mass + 1)).flatMap fun count =>
      SourceCurrentClassesGuardAlphabet.forecast budget count records alphabet entry)

/-- The uniform image retains every initial guard. -/
theorem initial_mem (budget : Nat) (alphabet : List Guard) (entry : Profile) {guard : Guard}
    (member : guard ∈ alphabet) : guard ∈ forecast budget alphabet entry :=
  List.mem_cons_of_mem _ (List.mem_append_left _ member)

/-- Top belongs to the initial forecast even when the initial alphabet is empty. -/
theorem top_mem (budget : Nat) (alphabet : List Guard) (entry : Profile) :
    top ∈ forecast budget alphabet entry := List.mem_cons_self

/-- Every exact finite initial class case is included in the same carrier image. -/
theorem case_subset (budget : Nat) (alphabet : List Guard) (entry : Profile)
    (records : List SourceEqualityClassOrder.Record) (selected : records ∈ ownRecordImage alphabet)
    (count : Nat) (bounded : count ≤ entry.mass) :
    SourceCurrentClassesGuardAlphabet.forecast budget count records alphabet entry ⊆ forecast budget alphabet entry := by
  intro guard member
  exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨records,selected,List.mem_flatMap.mpr ⟨count,List.mem_range.mpr (by omega),member⟩⟩))

variable {bits : Nat} [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial resident facts place the actual Parent carrier in the finite uniform image. -/
theorem resident_subset
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : Request)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (entry : Profile) (fits : Fits entry before.checked)
    (known : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) :
    SourceCurrentParentGuardAlphabet.residentForecast alphabet budget request before.checked entry ⊆
      forecast budget alphabet entry := by
  classical
  cases raw : SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint with
  | true =>
      simp only [SourceCurrentParentGuardAlphabet.residentForecast,raw,ite_true]
      intro guard member
      rcases List.mem_cons.mp member with rfl | member
      · exact top_mem budget alphabet entry
      · exact initial_mem budget alphabet entry member
  | false =>
      obtain ⟨loaded,own,branch,receipt⟩ := SourceCurrentAllocatedPrecheck.resident_complete formulas solver inventory
        before.checked initial.ready initial.admitted request.value resident request.inherited inherited
      have countBound : request.value.children.length ≤ entry.mass := by
        have mass := InternedValueMassHeap.resident _ fits.stored request.value resident
        have length : request.value.children.length ≤ InternedValueMass.values request.value.children := by
          rw [InternedValueMass.values_eq_length_sum]
          omega
        rw [InternedValueMass.edge_children] at mass
        omega
      have original := known _ _ resident
      simp only [SourceCurrentParentGuardAlphabet.residentForecast,raw,Bool.false_eq_true,ite_false,receipt.load,
        SourceCurrentParentGuardAlphabet.forecast,SourceCurrentLocalGuardAlphabet.forecast,receipt.actual]
      cases branch with
      | unchanged | emptyChildren =>
          intro guard member
          rcases List.mem_cons.mp member with rfl | member
          · exact top_mem budget alphabet entry
          rcases List.mem_cons.mp member with rfl | member
          · exact initial_mem budget alphabet entry original
          · exact initial_mem budget alphabet entry member
      | classes records =>
          obtain ⟨_proper,originals,read,_classes,same,_coherent⟩ := receipt.classes records rfl
          have selected : records ∈ ownRecordImage alphabet := by
            apply List.mem_map.mpr
            refine ⟨request.value.entry.key.constraint,original,?_⟩
            rw [read]
            exact same.symm
          intro guard member
          rcases List.mem_cons.mp member with rfl | member
          · exact top_mem budget alphabet entry
          rcases List.mem_cons.mp member with rfl | member
          · exact initial_mem budget alphabet entry original
          · exact case_subset budget alphabet entry records selected _ countBound member

variable [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)]

/-- Initial uniform reservations construct the actual Parent with the common output and replay bounds. -/
theorem complete
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : Request)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (entry : Profile) (fits : Fits entry before.checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (uniform : UniformReserved bits budget alphabet entry) :
    ∃ loaded result after savedFourth saved next final,
      SourceCurrentParentNumeric.Receipt formulas solver next entry budget request.value.entry.key.symbol
        request.value.entry.key.constraint loaded request.inherited request.value.children before memos
        result after savedFourth saved final ∧ Fits (SourceCurrentParentUniformEnvelope.profile budget alphabet entry) after ∧
      Carrier (fun guard => guard ∈ forecast budget alphabet entry) after.native.machine.heap ∧
      ∀ g s r e p h m c n,
        SourceCurrentParentUniformEnvelope.fuel budget alphabet entry ≤ g → SourceCurrentParentUniformEnvelope.fuel budget alphabet entry ≤ s → SourceCurrentParentUniformEnvelope.fuel budget alphabet entry ≤ r →
        SourceCurrentParentUniformEnvelope.fuel budget alphabet entry ≤ e → SourceCurrentParentUniformEnvelope.fuel budget alphabet entry ≤ p → SourceCurrentParentUniformEnvelope.fuel budget alphabet entry ≤ h →
        SourceCurrentParentUniformEnvelope.fuel budget alphabet entry ≤ m → SourceCurrentParentUniformEnvelope.fuel budget alphabet entry ≤ c → SourceCurrentParentUniformEnvelope.fuel budget alphabet entry ≤ n →
        SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
          request.value.entry.key.constraint request.inherited request.value.children
          before.checked before.fourth before.merge = .done result after savedFourth saved := by
  have reserved := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory budget alphabet request
    before memos initial entry fits known inherited resident uniform
  have bounds := SourceCurrentParentUniformEnvelope.resident_bounds formulas solver inventory budget alphabet request before memos initial entry fits
    known inherited resident
  obtain ⟨loaded,result,after,savedFourth,saved,next,final,receipt,numeric,carrier,done⟩ :=
    SourceCurrentParentGuardAlphabet.resident_complete alphabet formulas solver inventory budget request before memos
      initial frame entry fits (fun _ => resident) (fun _ => inherited) reserved known
  have included := resident_subset formulas solver inventory budget alphabet request before memos initial entry fits
    known inherited resident
  refine ⟨loaded,result,after,savedFourth,saved,next,final,receipt,numeric.mono bounds.1,
    (fun key edge found => included (carrier key edge found)),?_⟩
  intro g s r e p h m c n hg hs hr he hp hh hm hc hn
  exact done g s r e p h m c n (Nat.le_trans bounds.2 hg) (Nat.le_trans bounds.2 hs) (Nat.le_trans bounds.2 hr)
    (Nat.le_trans bounds.2 he) (Nat.le_trans bounds.2 hp) (Nat.le_trans bounds.2 hh)
    (Nat.le_trans bounds.2 hm) (Nat.le_trans bounds.2 hc) (Nat.le_trans bounds.2 hn)

end MicroCFTA.SourceCurrentParentUniformGuardAlphabet
