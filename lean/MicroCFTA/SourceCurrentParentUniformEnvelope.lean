import MicroCFTA.SourceCurrentParentAlphabetReservation
import MicroCFTA.SourceCurrentInitialSelectionForecast

/-!
# Finite common resources for initial resident Parent calls

Exact own records, bounded original child counts and bounded ambient guard
lists determine a finite profile join and fuel maximum. The join retains
full path, index and callback syntax. Initial resident facts identify the
actual Parent forecast inside this finite envelope.
-/
namespace MicroCFTA.SourceCurrentParentUniformEnvelope
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedNativeResourceForecast (Profile Le)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentParentAlphabetReservation (ownRecordImage wordsThrough UniformReserved)
open SourceCurrentInitialSelectionForecast (cover cover_ge cover_member maximum maximum_member)
open SourceEqualityClassOrder (Record)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards

/-- Join the exact class schedules over all finite initial own, count and ambient cases. -/
noncomputable def classesProfile (budget : Nat) (alphabet : List Guard) (entry : Profile) : Profile :=
  cover ((ownRecordImage alphabet).flatMap fun records =>
    (List.range (entry.mass + 1)).flatMap fun count =>
      (wordsThrough alphabet entry.edges).map fun ambient =>
        SourceCurrentClassesForecast.finalProfile budget count records ambient entry) entry

/-- One constructor at the maximum original child count follows the joined class profile. -/
noncomputable def profile (budget : Nat) (alphabet : List Guard) (entry : Profile) : Profile :=
  SourceCurrentMkEdgeNumeric.finalProfile entry.mass (classesProfile budget alphabet entry)

/-- Every exact finite class schedule contributes to the common nine-stage fuel ceiling. -/
noncomputable def fuel (budget : Nat) (alphabet : List Guard) (entry : Profile) : Nat :=
  maximum ((ownRecordImage alphabet).flatMap fun records =>
    (List.range (entry.mass + 1)).flatMap fun count =>
      (wordsThrough alphabet entry.edges).map fun ambient =>
        SourceCurrentClassesForecast.fuel budget count records ambient entry)

/-- Every finite initial case fits the common class profile and common fuel ceiling. -/
theorem case_bounds (budget : Nat) (alphabet : List Guard) (entry : Profile)
    (records : List Record) (selected : records ∈ ownRecordImage alphabet)
    (count : Nat) (countBound : count ≤ entry.mass)
    (ambient : List Guard) (ambientMember : ambient ∈ wordsThrough alphabet entry.edges) :
    Le (SourceCurrentClassesForecast.finalProfile budget count records ambient entry)
      (classesProfile budget alphabet entry) ∧
    SourceCurrentClassesForecast.fuel budget count records ambient entry ≤ fuel budget alphabet entry := by
  constructor
  · apply cover_member
    exact List.mem_flatMap.mpr ⟨records,selected,List.mem_flatMap.mpr
      ⟨count,List.mem_range.mpr (by omega),List.mem_map.mpr ⟨ambient,ambientMember,rfl⟩⟩⟩
  · apply maximum_member
    exact List.mem_flatMap.mpr ⟨records,selected,List.mem_flatMap.mpr
      ⟨count,List.mem_range.mpr (by omega),List.mem_map.mpr ⟨ambient,ambientMember,rfl⟩⟩⟩

private theorem constructor_bound (budget : Nat) (alphabet : List Guard) (entry : Profile)
    (count : Nat) (counts : count ≤ entry.mass) :
    Le (SourceCurrentMkEdgeNumeric.finalProfile count entry) (profile budget alphabet entry) :=
  (SourceCurrentMkEdgeNumeric.finalProfile_mono count (cover_ge _ _)).trans
    (SourceCurrentMkEdgeNumeric.finalProfile_count_mono counts _)

variable {bits : Nat} [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial resident facts bound the literal selected Parent forecast without a future-state premise. -/
theorem resident_bounds
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : Request)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (entry : Profile) (fits : Fits entry before.checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) :
    Le (SourceCurrentParentForecast.residentProfile budget request before.checked entry) (profile budget alphabet entry) ∧
      SourceCurrentParentForecast.residentFuel budget request before.checked entry ≤ fuel budget alphabet entry := by
  classical
  cases raw : SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint with
  | true =>
      exact ⟨by simpa only [SourceCurrentParentForecast.residentProfile,raw,ite_true] using
        constructor_bound budget alphabet entry 0 (Nat.zero_le _), by simp only
        [SourceCurrentParentForecast.residentFuel,raw,ite_true,Nat.zero_le]⟩
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
      simp only [SourceCurrentParentForecast.residentProfile,SourceCurrentParentForecast.residentFuel,raw,
        Bool.false_eq_true,ite_false,receipt.load,SourceCurrentParentForecast.finalProfile,
        SourceCurrentParentForecast.fuel,SourceCurrentLocalForecast.finalProfile,
        SourceCurrentLocalForecast.fuel,receipt.actual]
      cases branch with
      | unchanged | emptyChildren =>
          exact ⟨constructor_bound budget alphabet entry _ countBound,Nat.zero_le _⟩
      | classes records =>
          obtain ⟨_proper,originals,read,_classes,same,_coherent⟩ := receipt.classes records rfl
          have selected : records ∈ ownRecordImage alphabet := by
            apply List.mem_map.mpr
            refine ⟨request.value.entry.key.constraint,known _ _ resident,?_⟩
            rw [read]
            exact same.symm
          have ambient : guards before.checked.native.machine.heap ∈ wordsThrough alphabet entry.edges := by
            apply SourceCurrentParentAlphabetReservation.wordsThrough_member
            · have length := List.length_filterMap_le
                (SourceRecursiveIntersectionSourceProfile.edgeRead before.checked.native.machine.heap)
                (List.range before.checked.native.machine.heap.edges.next)
              simp only [SourceCurrentConjunctionGuardUniverse.guards,SourceRecursiveIntersectionSourceProfile.edgePayloads,
                List.length_map,List.length_range] at length ⊢
              exact Nat.le_trans length fits.edges
            · intro guard member
              obtain ⟨edge,present,rfl⟩ := List.mem_map.mp member
              have facts := initial.ready.semantic.ready.semantic.1.normal.facts
              have checked : EdgeResident before.checked.native.machine.heap edge := by
                obtain ⟨index,_range,read⟩ := List.mem_filterMap.mp present
                unfold SourceRecursiveIntersectionSourceProfile.edgeRead at read
                cases found : before.checked.native.machine.heap.edges.issued index with
                | none => simp only [found,Option.bind_none] at read; cases read
                | some key =>
                    have stored : before.checked.native.machine.heap.edgeRecords key = some edge := by
                      simpa only [found,Option.bind_some] using read
                    have same := (facts.coherent.edges key edge stored).2.1
                    simpa only [EdgeResident,same] using stored
              exact known _ _ checked
          have bounds := case_bounds budget alphabet entry records selected request.value.children.length countBound _ ambient
          exact ⟨(SourceCurrentMkEdgeNumeric.finalProfile_mono _ bounds.1).trans
            (SourceCurrentMkEdgeNumeric.finalProfile_count_mono countBound _),bounds.2⟩

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
        result after savedFourth saved final ∧ Fits (profile budget alphabet entry) after ∧
      ∀ g s r e p h m c n,
        fuel budget alphabet entry ≤ g → fuel budget alphabet entry ≤ s → fuel budget alphabet entry ≤ r →
        fuel budget alphabet entry ≤ e → fuel budget alphabet entry ≤ p → fuel budget alphabet entry ≤ h →
        fuel budget alphabet entry ≤ m → fuel budget alphabet entry ≤ c → fuel budget alphabet entry ≤ n →
        SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
          request.value.entry.key.constraint request.inherited request.value.children
          before.checked before.fourth before.merge = .done result after savedFourth saved := by
  have reserved := SourceCurrentParentAlphabetReservation.resident_reserved formulas solver inventory budget alphabet request
    before memos initial entry fits known inherited resident uniform
  have bounds := resident_bounds formulas solver inventory budget alphabet request before memos initial entry fits
    known inherited resident
  obtain ⟨loaded,result,after,savedFourth,saved,next,final,receipt,numeric,done⟩ :=
    SourceCurrentParentNumeric.resident_complete formulas solver inventory budget request before memos
      initial frame entry fits (fun _ => resident) (fun _ => inherited) reserved
  refine ⟨loaded,result,after,savedFourth,saved,next,final,receipt,numeric.mono bounds.1,?_⟩
  intro g s r e p h m c n hg hs hr he hp hh hm hc hn
  exact done g s r e p h m c n (Nat.le_trans bounds.2 hg) (Nat.le_trans bounds.2 hs) (Nat.le_trans bounds.2 hr)
    (Nat.le_trans bounds.2 he) (Nat.le_trans bounds.2 hp) (Nat.le_trans bounds.2 hh)
    (Nat.le_trans bounds.2 hm) (Nat.le_trans bounds.2 hc) (Nat.le_trans bounds.2 hn)

end MicroCFTA.SourceCurrentParentUniformEnvelope
