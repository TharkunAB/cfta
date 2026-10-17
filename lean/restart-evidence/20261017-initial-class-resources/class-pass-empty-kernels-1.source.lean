import MicroCFTA.SourceCurrentConstrainedCapClassPassNumeric

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.ClassPassEmptyInitial
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedClassPass (Pass PassReads Receipt)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The empty initial pass needs no numeric room and returns its exact input state at every fuel tuple. -/
theorem no_room (depth : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (profile : Profile) (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (merged : MergeStored memo) (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (caps : ∀ value ∈ values, Cap depth value) :
    ∃ next final, ∃ actual : Pass [] values before memo (EqualityLeafProjectionRuntimeEmpty.propagate values) before memo,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next [] values before memo (EqualityLeafProjectionRuntimeEmpty.propagate values)
        before memo memos final ∧ Frame formulas solver next before ∧ Fits profile before ∧
      ∀ e p h m s n, SourceCurrentAllocatedClassWorker.pass e p h m s n [] values before memo =
        .done (EqualityLeafProjectionRuntimeEmpty.propagate values) before memo := by
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, returned, finalFits,
      _finalMerged, _finalCaps, _sameLength, done⟩ :=
    SourceCurrentConstrainedCapClassPassNumeric.pass depth formulas solver inventory []
      (by simp) (by simp) values before memo profile frame fits available (by simp)
      physical covered merged memos valid caps True.intro
  have same : EqualityLeafProjectionRuntimeEmpty.propagate values = results ∧ before = after ∧ memo = saved := by
    apply SourceCurrentAllocatedClassWorker.Outcome.done.inj
    simpa only [SourceCurrentConstrainedCapClassForecast.foldFuel, SourceCurrentAllocatedClassWorker.pass,
      SourceCurrentAllocatedClassWorker.fold, SourceCurrentAllocatedClassWorker.Outcome.bind] using done
  rcases same with ⟨rfl, rfl, rfl⟩
  exact ⟨next, final, actual, reads, receipt, returned, finalFits, fun _ _ _ _ _ _ => rfl⟩

end MicroCFTA.ClassPassEmptyInitial

#check @MicroCFTA.ClassPassEmptyInitial.no_room
#print axioms MicroCFTA.ClassPassEmptyInitial.no_room
#print MicroCFTA.ClassPassEmptyInitial.no_room
