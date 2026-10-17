import MicroCFTA.SourceCurrentClassNumeric
import MicroCFTA.SourceCurrentAllocatedClassWorkerStability

/-!
# Complete class folds from initial numeric reservations

The tail executes before the head class captures its actual returned forest.
The initial profile follows that order. Every class clears its own target
slots and retains the native state, equality state, Merge table, and globals.
Final empty propagation changes no checked state or memo table.
-/
namespace MicroCFTA.SourceCurrentClassPassNumeric
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Receipt)
open SourceEqualityProjectionPathDomain (ForestClosed)
namespace Forecast
export SourceCurrentConstrainedCapClassForecast (classProfile classFuel foldProfile foldFuel Reserved)
end Forecast
namespace Worker
export SourceCurrentAllocatedClassWorker (fold pass)
end Worker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
variable {bits : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem reframe {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory next : Inventory}
    {records values results} {before after : Checked (bits + 2)} {memo saved : Memo} {memos final : Memos}
    (receipt : Receipt formulas solver inventory records values before memo results after saved memos final)
    (frame : Frame formulas solver next after) :
    Receipt formulas solver next records values before memo results after saved memos final :=
  ⟨receipt.ready, frame.admitted, receipt.effects, receipt.extension, receipt.stored, receipt.covered,
    receipt.available, receipt.transport, receipt.domains, receipt.retained, receipt.globals, receipt.language⟩

variable [DecidableEq Symbol]

/-- One initial forecast constructs the complete tail-first fold and its exact common-fuel return. -/
theorem fold
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
    (reserved : Forecast.Reserved bits records values.length profile) :
    ∃ results after saved next final, ∃ actual : Fold records values before memo results after saved,
      FoldReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before memo results after saved memos final ∧
      Frame formulas solver next after ∧ Fits (Forecast.foldProfile records values.length profile) after ∧
      results.length = values.length ∧
      Worker.fold (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
        (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
        (Forecast.foldFuel records values.length profile) (Forecast.foldFuel records values.length profile)
        records values before memo = .done results after saved ∧
      ∀ e p h m c n, Forecast.foldFuel records values.length profile ≤ e → Forecast.foldFuel records values.length profile ≤ p →
        Forecast.foldFuel records values.length profile ≤ h → Forecast.foldFuel records values.length profile ≤ m →
        Forecast.foldFuel records values.length profile ≤ c → Forecast.foldFuel records values.length profile ≤ n →
        Worker.fold e p h m c n records values before memo = .done results after saved := by
  induction records generalizing inventory values before memo profile memos with
  | nil =>
      have reads : FoldReads formulas solver (Fold.nil (values := values) (before := before) (memo := memo))
          memos memos := .nil
      obtain ⟨_next, receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads
        coherent active frame.ready frame.admitted available domains physical covered valid
      exact ⟨values, before, memo, inventory, memos, .nil, reads, reframe receipt frame,
        frame, fits, rfl, rfl, by intros; rfl⟩
  | cons record records ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      have tailDomains := fun own member => domains own (List.mem_cons_of_mem record member)
      obtain ⟨middle, step, current, tailInventory, stepMemos, tailActual, tailReads, first,
          tailFrame, tailFits, sameLength, tailDone, _tailStable⟩ :=
        ih inventory tailCoherent tailActive values before memo profile frame fits available tailDomains
          physical covered memos valid
          (SourceCurrentConstrainedCapClassForecast.reserved_tail bits record records values.length profile reserved)
      have headRoom := SourceCurrentConstrainedCapClassForecast.reserved_head bits record records values.length profile reserved
      have classRoom : SourceCurrentAllocatedNativeResourceForecast.Room bits
          (Forecast.classProfile record middle.length (Forecast.foldProfile records values.length profile)) := by
        simpa only [sameLength] using headRoom
      obtain ⟨results, after, saved, next, final, classActual, classReads, _last, returned,
          finalFits, classLength, classDone, _classStable⟩ :=
        SourceCurrentClassNumeric.complete formulas solver tailInventory record
          (coherent record List.mem_cons_self) (active record List.mem_cons_self) middle step current
          (Forecast.foldProfile records values.length profile) tailFrame tailFits first.available
          (fun path member => first.domains _ (domains record List.mem_cons_self path member))
          first.stored first.covered stepMemos first.globals.valid classRoom
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
        ?_, classLength.trans sameLength, ?_⟩
      · simpa only [Forecast.foldProfile, sameLength] using finalFits
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
theorem pass
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
    (reserved : Forecast.Reserved bits records values.length profile) :
    ∃ results after saved next final, ∃ actual : Pass records values before memo results after saved,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before memo results after saved memos final ∧
      Frame formulas solver next after ∧ Fits (Forecast.foldProfile records values.length profile) after ∧
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
      sameLength, done, _stable⟩ :=
    fold formulas solver inventory records coherent active values before memo profile frame fits available domains
      physical covered memos valid reserved
  have passReads : PassReads formulas solver (.done actual) memos final := .done reads
  obtain ⟨_next, receipt⟩ := SourceCurrentAllocatedClassPass.Pass.verified formulas solver inventory passReads
    coherent active frame.ready frame.admitted available domains physical covered valid
  refine ⟨EqualityLeafProjectionRuntimeEmpty.propagate results, after, saved, next, final, .done actual, passReads,
    reframe receipt returned, returned, finalFits, ?_, ?_⟩
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

end MicroCFTA.SourceCurrentClassPassNumeric
