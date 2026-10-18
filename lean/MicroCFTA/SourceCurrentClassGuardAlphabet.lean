import MicroCFTA.SourceCurrentFiniteEditGuardAlphabet
import MicroCFTA.SourceCurrentClassPassNumeric

/-!
# Initial finite guard carriers through complete class edits

One final class profile bounds each node in its compiled forest scan.
Original forest lengths bound the carrier count. Tail-first class folds
thread the exact predicted profile and carrier through each fresh capture.
-/
namespace MicroCFTA.SourceCurrentClassGuardAlphabet
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects (ChildrenReceipt ListSafe)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Le Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedClassEditPlan
open SourceEqualityProjectionPathDomain (ForestClosed)
namespace Forecast
export SourceCurrentConstrainedCapClassForecast (classProfile classFuel foldProfile foldFuel Reserved)
end Forecast
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "advanceAlphabet" => SourceCurrentNativeGuardAlphabet.advance
local notation "nodeBound" => SourceCurrentEditGuardBudget.nodeBound
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "listProfile" => SourceCurrentEditListNumeric.finalProfile
local notation "listFuel" => SourceCurrentEditListNumeric.fuel
local notation "planProfile" => SourceCurrentConstrainedCapEditForecast.planProfile
local notation "stageFuel" => SourceCurrentConstrainedCapEditForecast.stageFuel

/-- Original forest length bounds the compiled edit scan at one fixed final ceiling. -/
noncomputable def listCount (record : SourceEqualityClassOrder.Record) (count : Nat)
    (edits : Edits EqualityNormalize.Path) (length : Nat) (profile : Profile) : Nat :=
  match edits with
  | .editAt _ => 0
  | .editBelow _ => length * nodeBound record count (listProfile record count edits length profile) (sizeOf edits)

/-- Each class captures the original forest and runs its complete compiled list. -/
noncomputable def classCount (record : SourceEqualityClassOrder.Record) (count : Nat) (profile : Profile) : Nat :=
  listCount record count (compiled record) count profile

/-- The literal tail executes before the head uses its predicted entry profile. -/
noncomputable def foldCount : List SourceEqualityClassOrder.Record → Nat → Profile → Nat
  | [], _, _ => 0
  | record :: records, count, profile =>
      foldCount records count profile + classCount record count (Forecast.foldProfile records count profile)

private theorem reframe {bits : Nat} [DecidableEq (EdgeKey Symbol Guard)] {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory next : Inventory}
    {records values results} {before after : Checked (bits + 2)} {memo saved : Memo} {memos final : Memos}
    (receipt : SourceCurrentAllocatedClassPass.Receipt formulas solver inventory records values before memo results after saved memos final)
    (frame : Frame formulas solver next after) :
    SourceCurrentAllocatedClassPass.Receipt formulas solver next records values before memo results after saved memos final :=
  ⟨receipt.ready, frame.admitted, receipt.effects, receipt.extension, receipt.stored, receipt.covered,
    receipt.available, receipt.transport, receipt.domains, receipt.retained, receipt.globals, receipt.language⟩

variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial support constructs the complete compiled forest and its finite carrier. -/
theorem list_complete
    (alphabet : List Guard) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (base : Heap) (before : SharedState (bits + 2)) (profile : Profile)
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (known : Values base originals)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (edits : Edits EqualityNormalize.Path) (populated : Populated edits) (allowed : Allowed record edits)
    (values : List (Value Symbol Guard)) (available : Values before.checked.native.machine.heap values)
    (safe : ListSafe edits values) (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (reserved : SourceCurrentEditListNumeric.Reserved bits record originals.length edits values.length profile)
    (knownAlphabet : Carrier (fun guard => guard ∈ alphabet) before.checked.native.machine.heap) :
    ∃ results after next final, ∃ actual : EditList record originals edits values before results after,
      ListReads formulas solver base actual memos final ∧
      ChildrenReceipt formulas solver next record originals base values before results after memos final ∧
      Frame formulas solver next after.checked ∧ Fits (listProfile record originals.length edits values.length profile) after.checked ∧
      Carrier (fun guard => guard ∈ advanceAlphabet alphabet
        (listCount record originals.length edits values.length profile)) after.checked.native.machine.heap ∧
      SourceCurrentAllocatedSharedEditWorker.editList (SourceCurrentAllocatedSharedEditWorker.edit record originals
        (listFuel record originals.length edits values.length profile) (listFuel record originals.length edits values.length profile)
        (listFuel record originals.length edits values.length profile) (listFuel record originals.length edits values.length profile)
        (listFuel record originals.length edits values.length profile) (listFuel record originals.length edits values.length profile))
        edits values before = .done results after := by
  cases edits with
  | editAt target =>
      have reads : ListReads formulas solver base (EditList.leaf (record := record) (originals := originals)
          (target := target) (values := values) (state := before)) memos memos := .leaf
      obtain ⟨_inventory, receipt⟩ := SourceCurrentAllocatedSharedEditEffects.list_effects reads populated allowed
        ready available safe valid
      exact ⟨values,before,inventory,memos,.leaf,reads,
        SourceCurrentConstrainedCapEditReceipt.children_receipt receipt frame,frame,fits,knownAlphabet,rfl⟩
  | editBelow entries =>
      let level := sizeOf (Edits.editBelow entries : Edits EqualityNormalize.Path)
      let ceiling := listProfile record originals.length (.editBelow entries) values.length profile
      have sizes : ∀ index child, (index, child) ∈ entries → sizeOf child ≤ level := by
        intro index child member
        have smaller := List.sizeOf_lt_of_mem member
        simp only [Prod.mk.sizeOf_spec] at smaller
        dsimp only [level]
        simp only [Edits.editBelow.sizeOf_spec]
        omega
      have node := SourceCurrentFiniteEditGuardAlphabet.node_complete
        (bits := bits) (level := level) (roof := ceiling)
        (formulas := formulas) (solver := solver) (record := record) (originals := originals) (base := base)
        known domains coherent active
      obtain ⟨results,after,next,final,children,reads,receipt,returned,finalFits,carrier,done⟩ :=
        SourceCurrentEditGuardScans.children formulas solver record originals base level alphabet ceiling node
          entries sizes 0 values before inventory profile populated allowed ready frame fits available safe
          memos valid (Le.refl _) reserved knownAlphabet
      have allReads : ListReads formulas solver base (.children children) memos final := .children reads
      have editEnough : SourceCurrentEditGuardScans.editFuel level ≤
          listFuel record originals.length (.editBelow entries) values.length profile := Nat.le_max_left _ _
      have stageEnough : stageFuel record originals.length ceiling ≤
          listFuel record originals.length (.editBelow entries) values.length profile := Nat.le_max_right _ _
      have lifted := SourceCurrentAllocatedSharedEditWorkerStability.children_edit_done_stable done
        editEnough stageEnough stageEnough stageEnough stageEnough stageEnough
      exact ⟨results,after,next,final,.children children,allReads,receipt,returned,finalFits,carrier,
        by simpa only [SourceCurrentAllocatedSharedEditWorker.editList] using lifted⟩

section Single
open SourceCurrentAllocatedClassEdits (Class ClassReads Receipt)
local notation "classProfile" => Forecast.classProfile
local notation "classFuel" => Forecast.classFuel

/-- Initial selected domains and one final-profile room test construct the full class return. -/
theorem complete (alphabet : List Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (room : Room bits (classProfile record values.length profile))
    (knownAlphabet : Carrier (fun guard => guard ∈ alphabet) before.native.machine.heap) :
    ∃ results after saved next final, ∃ actual : Class record values before memo results after saved,
      ClassReads formulas solver actual memos final ∧
      Receipt formulas solver next record values before memo results after saved memos final ∧
      Frame formulas solver next after ∧ Fits (classProfile record values.length profile) after ∧
      Carrier (fun guard => guard ∈ advanceAlphabet alphabet (classCount record values.length profile)) after.native.machine.heap ∧
      results.length = values.length ∧
      SourceCurrentAllocatedClassWorker.runClass
        (classFuel record values.length profile) (classFuel record values.length profile)
        (classFuel record values.length profile) (classFuel record values.length profile)
        (classFuel record values.length profile) (classFuel record values.length profile)
        record values before memo = .done results after saved ∧
      ∀ e p h m c n, classFuel record values.length profile ≤ e → classFuel record values.length profile ≤ p →
        classFuel record values.length profile ≤ h → classFuel record values.length profile ≤ m →
        classFuel record values.length profile ≤ c → classFuel record values.length profile ≤ n →
        SourceCurrentAllocatedClassWorker.runClass e p h m c n record values before memo = .done results after saved := by
  have ready := SourceCurrentAllocatedSharedTargetState.initial_ready
    formulas solver inventory record values before.native.machine.heap before memo frame.ready frame.admitted
    (SourceEqualityRequiredCache.pure_keeps _ frame.ready.semantic.ready) physical covered
  have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
    obtain ⟨entries, built⟩ := compiled_children record coherent active
    rw [built]
    exact compiled_safe record coherent values domains entries built
  have reserved : SourceCurrentEditListNumeric.Reserved bits record values.length
      (compiled record) values.length profile := by
    obtain ⟨entries, built⟩ := compiled_children record coherent active
    simpa only [SourceCurrentEditListNumeric.Reserved, built, SourceCurrentConstrainedCapClassForecast.classProfile,
      SourceCurrentEditListNumeric.finalProfile, SourceCurrentConstrainedCapEditListNumeric.finalProfile] using room
  obtain ⟨results, shared, next, final, lower, lowerReads, lowerReceipt, returned, numeric, carrier, done⟩ :=
    list_complete alphabet formulas solver inventory record values
      before.native.machine.heap (SourceCurrentAllocatedSharedTargetState.initial before memo) profile ready frame fits
      available domains coherent active (compiled record) (compiled_populated record) (compiled_allowed record)
      values available safe memos valid reserved knownAlphabet
  have actual : Class record values before memo results shared.checked shared.memo := .edit lower
  have reads : ClassReads formulas solver actual memos final := .edit lowerReads
  obtain ⟨_previousInventory, previous⟩ := SourceCurrentAllocatedClassEdits.verified formulas solver inventory record
    coherent active reads frame.ready frame.admitted available domains physical covered valid
  have receipt : Receipt formulas solver next record values before memo results shared.checked shared.memo memos final :=
    ⟨previous.ready, returned.admitted, previous.effects, previous.extension, previous.stored, previous.covered,
      previous.available, previous.transport, previous.domains, previous.retained, previous.globals, previous.language⟩
  refine ⟨results, shared.checked, shared.memo, next, final, actual, reads, receipt, returned,
    numeric, carrier, (All₂.length_eq lowerReceipt.transport).symm, ?_⟩
  have fuel_eq : SourceCurrentEditListNumeric.fuel record values.length (compiled record) values.length profile =
      classFuel record values.length profile := by rfl
  have returnedWorker : SourceCurrentAllocatedClassWorker.runClass
      (classFuel record values.length profile) (classFuel record values.length profile)
      (classFuel record values.length profile) (classFuel record values.length profile)
      (classFuel record values.length profile) (classFuel record values.length profile)
      record values before memo = .done results shared.checked shared.memo := by
    simp only [SourceCurrentAllocatedClassWorker.runClass, ← fuel_eq, done]
  exact ⟨returnedWorker, fun _ _ _ _ _ _ he hp hh hm hc hn =>
    SourceCurrentAllocatedClassWorkerStability.runClass_done_stable returnedWorker he hp hh hm hc hn⟩


end Single

section Multiple
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Receipt)
namespace Worker
export SourceCurrentAllocatedClassWorker (fold pass)
end Worker

/-- One initial forecast constructs the complete tail-first fold and its exact common-fuel return. -/
theorem fold (alphabet : List Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (records : List SourceEqualityClassOrder.Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (reserved : Forecast.Reserved bits records values.length profile)
    (knownAlphabet : Carrier (fun guard => guard ∈ alphabet) before.native.machine.heap) :
    ∃ results after saved next final, ∃ actual : Fold records values before memo results after saved,
      FoldReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before memo results after saved memos final ∧
      Frame formulas solver next after ∧ Fits (Forecast.foldProfile records values.length profile) after ∧
      Carrier (fun guard => guard ∈ advanceAlphabet alphabet (foldCount records values.length profile)) after.native.machine.heap ∧
      results.length = values.length ∧
      Worker.fold (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
        (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
        (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
        records values before memo = .done results after saved ∧
      ∀ e p h m c n, Forecast.foldFuel records values.length profile ≤ e → Forecast.foldFuel records values.length profile ≤ p →
        Forecast.foldFuel records values.length profile ≤ h → Forecast.foldFuel records values.length profile ≤ m →
        Forecast.foldFuel records values.length profile ≤ c → Forecast.foldFuel records values.length profile ≤ n →
        Worker.fold e p h m c n records values before memo = .done results after saved := by
  induction records generalizing alphabet inventory values before memo profile memos with
  | nil =>
      have reads : FoldReads formulas solver (Fold.nil (values := values) (before := before) (memo := memo))
          memos memos := .nil
      obtain ⟨_next, receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads
        coherent active frame.ready frame.admitted available domains physical covered valid
      exact ⟨values, before, memo, inventory, memos, .nil, reads, reframe receipt frame,
        frame, fits, knownAlphabet, rfl, rfl, by intros; rfl⟩
  | cons record records ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      have tailDomains := fun own member => domains own (List.mem_cons_of_mem record member)
      obtain ⟨middle, step, current, tailInventory, stepMemos, tailActual, tailReads, first,
          tailFrame, tailFits, tailCarrier, sameLength, tailDone, _tailStable⟩ :=
        ih alphabet inventory tailCoherent tailActive values before memo profile frame fits available tailDomains
          physical covered memos valid
          (SourceCurrentConstrainedCapClassForecast.reserved_tail bits record records values.length profile reserved) knownAlphabet
      have headRoom := SourceCurrentConstrainedCapClassForecast.reserved_head bits record records values.length profile reserved
      have classRoom : SourceCurrentAllocatedNativeResourceForecast.Room bits
          (Forecast.classProfile record middle.length (Forecast.foldProfile records values.length profile)) := by
        simpa only [sameLength] using headRoom
      obtain ⟨results, after, saved, next, final, classActual, classReads, _last, returned,
          finalFits, classCarrier, classLength, classDone, _classStable⟩ :=
        complete (advanceAlphabet alphabet (foldCount records values.length profile)) formulas solver tailInventory record
          (coherent record List.mem_cons_self) (active record List.mem_cons_self) middle step current
          (Forecast.foldProfile records values.length profile) tailFrame tailFits first.available
          (fun path member => first.domains _ (domains record List.mem_cons_self path member))
          first.stored first.covered stepMemos first.globals.valid classRoom tailCarrier
      let actual : Fold (record :: records) values before memo results after saved := .cons tailActual classActual
      have reads : FoldReads formulas solver actual memos final := .cons tailReads classReads
      obtain ⟨_next, receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads
        coherent active frame.ready frame.admitted available domains physical covered valid
      have tailEnough : Forecast.foldFuel records values.length profile ≤
          Forecast.foldFuel (record :: records) values.length profile := Nat.le_max_left _ _
      have classEnough : Forecast.classFuel record middle.length (Forecast.foldProfile records values.length profile) ≤
          Forecast.foldFuel (record :: records) values.length profile := by
        rw [sameLength]
        exact Nat.le_max_right _ _
      have liftedTail := SourceCurrentAllocatedClassWorkerStability.fold_done_stable tailDone
        tailEnough tailEnough tailEnough tailEnough tailEnough tailEnough
      have liftedClass := SourceCurrentAllocatedClassWorkerStability.runClass_done_stable classDone
        classEnough classEnough classEnough classEnough classEnough classEnough
      refine ⟨results, after, saved, next, final, actual, reads, reframe receipt returned, returned,
        ?_, ?_, classLength.trans sameLength, ?_⟩
      · simpa only [Forecast.foldProfile, sameLength] using finalFits
      · simpa only [foldCount, sameLength, SourceCurrentNativeGuardAlphabet.advance_add] using classCarrier
      · have done : Worker.fold
            (Forecast.foldFuel (record :: records) values.length profile) (Forecast.foldFuel (record :: records) values.length profile)
            (Forecast.foldFuel (record :: records) values.length profile) (Forecast.foldFuel (record :: records) values.length profile)
            (Forecast.foldFuel (record :: records) values.length profile) (Forecast.foldFuel (record :: records) values.length profile)
            (record :: records) values before memo = .done results after saved := by
          simp only [Worker.fold, liftedTail, SourceCurrentAllocatedClassWorker.Outcome.bind]
          exact liftedClass
        exact ⟨done, fun _ _ _ _ _ _ he hp hh hm hc hn =>
          SourceCurrentAllocatedClassWorkerStability.fold_done_stable done he hp hh hm hc hn⟩

/-- Source empty propagation follows the constructed fold and retains its complete checked return. -/
theorem pass (alphabet : List Guard)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (records : List SourceEqualityClassOrder.Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (reserved : Forecast.Reserved bits records values.length profile)
    (knownAlphabet : Carrier (fun guard => guard ∈ alphabet) before.native.machine.heap) :
    ∃ results after saved next final, ∃ actual : Pass records values before memo results after saved,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before memo results after saved memos final ∧
      Frame formulas solver next after ∧ Fits (Forecast.foldProfile records values.length profile) after ∧
      Carrier (fun guard => guard ∈ advanceAlphabet alphabet (foldCount records values.length profile)) after.native.machine.heap ∧
      results.length = values.length ∧
      Worker.pass (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
        (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
        (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
        records values before memo = .done results after saved ∧
      ∀ e p h m c n, Forecast.foldFuel records values.length profile ≤ e → Forecast.foldFuel records values.length profile ≤ p →
        Forecast.foldFuel records values.length profile ≤ h → Forecast.foldFuel records values.length profile ≤ m →
        Forecast.foldFuel records values.length profile ≤ c → Forecast.foldFuel records values.length profile ≤ n →
        Worker.pass e p h m c n records values before memo = .done results after saved := by
  obtain ⟨results, after, saved, next, final, actual, reads, _receipt, returned, finalFits,
      carrier, sameLength, done, _stable⟩ :=
    fold alphabet formulas solver inventory records coherent active values before memo profile frame fits available domains
      physical covered memos valid reserved knownAlphabet
  have passReads : PassReads formulas solver (.done actual) memos final := .done reads
  obtain ⟨_next, receipt⟩ := SourceCurrentAllocatedClassPass.Pass.verified formulas solver inventory passReads
    coherent active frame.ready frame.admitted available domains physical covered valid
  refine ⟨EqualityLeafProjectionRuntimeEmpty.propagate results, after, saved, next, final, .done actual, passReads,
    reframe receipt returned, returned, finalFits, carrier, ?_, ?_⟩
  · unfold EqualityLeafProjectionRuntimeEmpty.propagate
    split
    · simpa only [EqualityLeafProjectionRuntimeEmpty.erase, List.length_map] using sameLength
    · exact sameLength
  · have passDone : Worker.pass
        (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
        (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
        (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
        records values before memo = .done (EqualityLeafProjectionRuntimeEmpty.propagate results) after saved := by
      simp only [Worker.pass, done, SourceCurrentAllocatedClassWorker.Outcome.bind]
    exact ⟨passDone, fun _ _ _ _ _ _ he hp hh hm hc hn =>
      SourceCurrentAllocatedClassWorkerStability.pass_done_stable passDone he hp hh hm hc hn⟩


end Multiple

end MicroCFTA.SourceCurrentClassGuardAlphabet
