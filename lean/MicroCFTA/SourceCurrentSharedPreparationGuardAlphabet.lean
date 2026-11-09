import MicroCFTA.SourceCurrentSharedScanRequiredNumeric
import MicroCFTA.SourceCurrentAllocatedSharedRecordScanWorkerStability
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceCurrentSharedParentAlphabetReservation

/-!
# Initial finite guards through complete Scan and Required preparation

The original edge counter bounds the initial ambient guard word. A finite
union of exact Scan alphabets covers each such word. Required copies raw
guards and preserves this alphabet without adding Top. The producer retains
the original preparation receipt and its exact caller and worker return.
-/
namespace MicroCFTA.SourceCurrentSharedPreparationGuardAlphabet
open Cache EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityClassOrder (Record Coherent)
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "guards" => SourceCurrentConjunctionGuardUniverse.guards
local notation "wordsThrough" => SourceCurrentSharedParentAlphabetReservation.wordsThrough
local notation "schedule" => SourceCurrentSharedScanNumericForecast.schedule
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source

/-- All bounded initial ambient words contribute their exact final Scan alphabets. -/
noncomputable def forecast (budget count : Nat) (records : List Record)
    (alphabet : List Guard) (profile : Profile) : List Guard :=
  (wordsThrough alphabet profile.edges).flatMap fun ambient =>
    (schedule budget count (records.map Record.paths) ambient profile).1

variable {width bits : Nat}

private theorem ambient_member {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory}
    {before : Checked width} (frame : Frame formulas solver inventory before)
    {profile : Profile} (fits : Fits profile before) {alphabet : List Guard}
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap) :
    guards before.native.machine.heap ∈ wordsThrough alphabet profile.edges := by
  apply SourceCurrentSharedParentAlphabetReservation.wordsThrough_member
  · have length := List.length_filterMap_le
      (SourceRecursiveIntersectionSourceProfile.edgeRead before.native.machine.heap)
      (List.range before.native.machine.heap.edges.next)
    simp only [SourceCurrentConjunctionGuardUniverse.guards,SourceRecursiveIntersectionSourceProfile.edgePayloads,
      List.length_map,List.length_range] at length ⊢
    exact Nat.le_trans length fits.edges
  · intro guard member
    obtain ⟨edge,present,rfl⟩ := List.mem_map.mp member
    have facts := frame.ready.semantic.ready.semantic.1.normal.facts
    obtain ⟨index,_range,read⟩ := List.mem_filterMap.mp present
    unfold SourceRecursiveIntersectionSourceProfile.edgeRead at read
    cases found : before.native.machine.heap.edges.issued index with
    | none => simp only [found,Option.bind_none] at read; cases read
    | some key =>
        have stored : before.native.machine.heap.edgeRecords key = some edge := by
          simpa only [found,Option.bind_some] using read
        have same := (facts.coherent.edges key edge stored).2.1
        exact known _ _ (by simpa only [same] using stored)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

private theorem scan_carrier
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (values : List (Value Symbol Guard)) (records : List Record)
    (before : Caller (bits+2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (active : ∀ record ∈ records, Nontrivial record.paths)
    (reserved : SourceCurrentSharedScanNumericForecast.Reserved bits budget values.length (records.map Record.paths)
      (guards before.checked.native.machine.heap) profile)
    {g s p h n outcome selected after saved}
    (actual : SourceCurrentAllocatedSharedRecordScanWorker.scan g s p h n budget values records
      before.checked before.fourth = .done (outcome, selected) after saved) :
    ∃ next, Frame formulas solver next after ∧ Values after.native.machine.heap values ∧
      Heap (fun guard => guard ∈ (schedule budget values.length (records.map Record.paths)
        (guards before.checked.native.machine.heap) profile).1) after.native.machine.heap := by
  have known := SourceCurrentConjunctionGuardUniverse.initial before.checked.native.machine.heap
    frame.ready.semantic.ready.semantic.1.normal.facts
  obtain ⟨chosen, kept, later, current, next, final, receipt⟩ := SourceCurrentSharedScanCallerNumeric.complete
    formulas solver inventory (guards before.checked.native.machine.heap) budget values records before memos
    initial frame profile fits available proper active reserved known
  let fuel := SourceCurrentSharedScanNumericForecast.fuel budget values.length (records.map Record.paths)
    (guards before.checked.native.machine.heap) profile
  have canonical := receipt.run fuel fuel fuel fuel fuel
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  have same := (SourceCurrentAllocatedSharedRecordScanWorkerStability.scan_done_unique actual canonical).2.1
  exact ⟨next, by simpa only [same] using receipt.frame,
    by simpa only [same] using receipt.available, by simpa only [same] using receipt.carrier⟩

/-- Initial preparation support constructs its full receipt and a finite raw guard carrier. -/
theorem complete (alphabet : List Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (values : List (Value Symbol Guard)) (records : List Record)
    (before : Caller (bits+2)) (memos : Memos) (initial : Context formulas solver inventory before memos)
    (frame : Frame formulas solver inventory before.checked) (profile : Profile) (fits : Fits profile before.checked)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (coherent : ∀ record ∈ records, Coherent record) (active : ∀ record ∈ records, Nontrivial record.paths)
    (reserved : SourceCurrentSharedScanNumericForecast.Reserved bits budget values.length (records.map Record.paths)
      (guards before.checked.native.machine.heap) profile)
    (known : Heap (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ outcome kept results after saved next final,
      SourceCurrentSharedScanRequiredNumeric.Receipt formulas solver next profile budget records values before memos
        outcome kept results after saved final ∧
      Heap (fun guard => guard ∈ forecast budget values.length records alphabet profile) after.native.machine.heap := by
  obtain ⟨outcome,kept,results,after,saved,next,final,receipt⟩ :=
    SourceCurrentSharedScanRequiredNumeric.complete formulas solver inventory budget values records before memos initial
      frame profile fits available proper coherent active reserved
  have carrier : Heap (fun guard => guard ∈ (schedule budget values.length (records.map Record.paths)
      (guards before.checked.native.machine.heap) profile).1) after.native.machine.heap := by
    cases receipt.actual with
    | stopped scanned =>
        obtain ⟨_next, _frame, _available, fields⟩ := scan_carrier formulas solver inventory budget values
          records before memos initial frame profile fits available proper active reserved scanned
        exact fields
    | prepared scanned required =>
        obtain ⟨_next, returned, originals, fields⟩ := scan_carrier formulas solver inventory budget values
          records before memos initial frame profile fits available proper active reserved scanned
        exact (SourceCurrentRequiredHeapEffects.requireAll _ _ _ _ _ _ _ _ required
          returned.ready.semantic returned.ready.costs fields originals).2.2.2.1
  refine ⟨outcome,kept,results,after,saved,next,final,receipt,?_⟩
  intro key edge present
  exact List.mem_flatMap.mpr ⟨guards before.checked.native.machine.heap,
    ambient_member frame fits known,carrier key edge present⟩

end MicroCFTA.SourceCurrentSharedPreparationGuardAlphabet
