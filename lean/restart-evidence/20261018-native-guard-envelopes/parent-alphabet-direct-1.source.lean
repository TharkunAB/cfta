import MicroCFTA.SourceCurrentParentNumeric
import MicroCFTA.SourceCurrentConjunctionTupleBounds
import MicroCFTA.SourceEqualityConstraintInventory

/-!
# Finite initial reservations for a resident Parent request

A supplied guard alphabet gives a finite image of exact own records.
The initial edge counter bounds the ambient guard list. Stored payload
mass bounds the original child count. The reservation checks these finite
inputs before execution. It does not inspect future caller states.
-/
namespace MicroCFTA.SourceCurrentParentAlphabetReservation
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceEqualityClassOrder (Record ordered)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Request" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
variable {bits : Nat}

/-- Each initial guard contributes its exact ordered own records or an empty fallback. -/
def ownRecordImage (alphabet : List Guard) : List (List Record) :=
  alphabet.map fun guard => match SourceEqualityPhysicalPayload.own guard with
    | .ok (some records) => ordered records
    | _ => []

/-- Enumerate every ambient guard list up to the initial edge-counter bound. -/
def wordsThrough (alphabet : List Guard) (limit : Nat) : List (List Guard) :=
  (List.range (limit + 1)).flatMap (SourceCurrentConjunctionTupleBounds.words alphabet)

/-- Length and literal membership place a guard list in the finite enumeration. -/
theorem wordsThrough_member (alphabet : List Guard) (limit : Nat) (word : List Guard)
    (length : word.length ≤ limit) (members : ∀ guard ∈ word, guard ∈ alphabet) :
    word ∈ wordsThrough alphabet limit := by
  exact List.mem_flatMap.mpr ⟨word.length, List.mem_range.mpr (by omega),
    (SourceCurrentConjunctionTupleBounds.words_mem_iff alphabet word.length word).mpr ⟨rfl,members⟩⟩

/-- Pure finite reservations cover exact own records, child counts, and ambient lists. -/
noncomputable def UniformReserved (bits budget : Nat) (alphabet : List Guard) (profile : Profile) : Prop :=
  ∀ records ∈ ownRecordImage alphabet, ∀ count ∈ List.range (profile.mass + 1),
    ∀ ambient ∈ wordsThrough alphabet profile.edges,
      SourceCurrentClassesForecast.Reserved bits budget count records ambient profile

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial resident inputs derive the exact Parent reservation without a future-entry callback. -/
theorem resident_reserved
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (alphabet : List Guard) (request : Request)
    (before : Caller (bits + 2)) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (uniform : UniformReserved bits budget alphabet profile) :
    SourceCurrentParentForecast.residentReserved bits budget request before.checked profile := by
  cases raw : SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint with
  | true => simp only [SourceCurrentParentForecast.residentReserved,raw,ite_true]
  | false =>
    obtain ⟨loaded,own,branch,receipt⟩ := SourceCurrentAllocatedPrecheck.resident_complete formulas solver inventory
      before.checked initial.ready initial.admitted request.value resident request.inherited inherited
    simp only [SourceCurrentParentForecast.residentReserved,raw,Bool.false_eq_true,ite_false,receipt.load,
      SourceCurrentParentForecast.Reserved,SourceCurrentLocalForecast.Reserved,receipt.actual]
    cases branch with
    | unchanged | emptyChildren => trivial
    | classes records =>
      obtain ⟨_proper,originals,read,_classes,same,_coherent⟩ := receipt.classes records rfl
      have selected : records ∈ ownRecordImage alphabet := by
        apply List.mem_map.mpr
        refine ⟨request.value.entry.key.constraint,known _ _ resident,?_⟩
        rw [read]
        exact same.symm
      have count : request.value.children.length ≤ profile.mass := by
        have mass := InternedValueMassHeap.resident _ fits.stored request.value resident
        have length : request.value.children.length ≤ InternedValueMass.values request.value.children := by
          rw [InternedValueMass.values_eq_length_sum]
          omega
        rw [InternedValueMass.edge_children] at mass
        omega
      have ambient : guards before.checked.native.machine.heap ∈ wordsThrough alphabet profile.edges := by
        apply wordsThrough_member
        · have length := List.length_filterMap_le
            (SourceRecursiveIntersectionSourceProfile.edgeRead before.checked.native.machine.heap)
            (List.range before.checked.native.machine.heap.edges.next)
          simp only [SourceCurrentConjunctionGuardUniverse.guards,SourceRecursiveIntersectionSourceProfile.edgePayloads,
            List.length_map,List.length_range] at length ⊢
          exact Nat.le_trans length fits.edges
        · intro guard member
          obtain ⟨edge,present,rfl⟩ := List.mem_map.mp member
          have facts := frame.ready.semantic.ready.semantic.1.normal.facts
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
      exact uniform records selected request.value.children.length (List.mem_range.mpr (by omega)) _ ambient

end MicroCFTA.SourceCurrentParentAlphabetReservation
