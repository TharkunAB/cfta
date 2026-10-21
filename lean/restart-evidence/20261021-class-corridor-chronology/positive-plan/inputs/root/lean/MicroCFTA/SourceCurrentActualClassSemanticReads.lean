import MicroCFTA.SourceCurrentClassNumeric
import MicroCFTA.SourceCurrentClassPassNumeric
import MicroCFTA.SourceCurrentClassSelectedChildLineage

/-!
# Semantic class reads at literal successful returns

Initial numeric reservations construct semantic reads. Worker uniqueness
identifies their values, checked state, and Merge memo with an observed
successful call. The observed fuels need no comparison with the forecast.
-/
namespace MicroCFTA.SourceCurrentActualClassSemanticReads
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedClassEditPlan
open SourceCurrentAllocatedClassEdits (Class ClassReads Receipt)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "classProfile" => SourceCurrentConstrainedCapClassForecast.classProfile
local notation "classFuel" => SourceCurrentConstrainedCapClassForecast.classFuel
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]


/-- Initial class facts produce semantic reads at any literal successful return. -/
theorem class_reads
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
    {e p h m c n : Nat} {results : List (Value Symbol Guard)}
    {after : Checked (bits + 2)} {saved : Memo}
    (observed : SourceCurrentAllocatedClassWorker.runClass e p h m c n
      record values before memo = .done results after saved) :
    ∃ next final, ∃ actual : Class record values before memo results after saved,
      ClassReads formulas solver actual memos final ∧
      Receipt formulas solver next record values before memo results after saved memos final ∧
      Frame formulas solver next after ∧ Fits (classProfile record values.length profile) after ∧
      results.length = values.length := by
  obtain ⟨computed, state, current, next, final, actual, reads, receipt, returned, numeric,
      sameLength, done, _stable⟩ := SourceCurrentClassNumeric.complete formulas solver inventory record
    coherent active values before memo profile frame fits available domains physical covered memos valid room
  obtain ⟨sameValues, sameState, sameMemo⟩ :=
    SourceCurrentAllocatedClassWorkerStability.runClass_done_unique observed done
  subst computed state current
  exact ⟨next, final, actual, reads, receipt, returned, numeric, sameLength⟩

/-- Initial fold reservations produce tail-first reads at any literal successful return. -/
theorem fold_reads
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
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (reserved : SourceCurrentConstrainedCapClassForecast.Reserved bits records values.length profile)
    {e p h m c n : Nat} {results : List (Value Symbol Guard)}
    {after : Checked (bits + 2)} {saved : Memo}
    (observed : SourceCurrentAllocatedClassWorker.fold e p h m c n
      records values before memo = .done results after saved) :
    ∃ next final, ∃ actual : SourceCurrentAllocatedClassPass.Fold records values before memo results after saved,
      SourceCurrentAllocatedClassPass.FoldReads formulas solver actual memos final ∧
      SourceCurrentAllocatedClassPass.Receipt formulas solver next records values before memo results after saved memos final ∧
      Frame formulas solver next after ∧
      Fits (SourceCurrentConstrainedCapClassForecast.foldProfile records values.length profile) after ∧
      results.length = values.length := by
  obtain ⟨computed, state, current, next, final, actual, reads, receipt, returned, numeric,
      sameLength, done, _stable⟩ := SourceCurrentClassPassNumeric.fold formulas solver inventory records
    coherent active values before memo profile frame fits available domains physical covered memos valid reserved
  obtain ⟨sameValues, sameState, sameMemo⟩ :=
    SourceCurrentAllocatedClassWorkerStability.fold_done_unique observed done
  subst computed state current
  exact ⟨next, final, actual, reads, receipt, returned, numeric, sameLength⟩

/-- Initial class facts and history derive the selected child schedule without supplied reads. -/
theorem class_selected
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
    {e p h m c n : Nat} {results : List (Value Symbol Guard)}
    {after : Checked (bits + 2)} {saved : Memo}
    (observed : SourceCurrentAllocatedClassWorker.runClass e p h m c n
      record values before memo = .done results after saved)
    (history : SourceCurrentNativeEdgeWriterGrowth.History before)
    {index : Nat} {result : Value Symbol Guard} {edits : SourceEqualityEdits.Edits EqualityNormalize.Path}
    (output : results[index]? = some result)
    (selected : ∀ entries, compiled record = .editBelow entries →
      SourceEqualityNeededMap.lookup (index : Int) entries = some edits) :
    ∃ final, SourceCurrentClassSelectedChildLineage.Selection formulas solver record values before memo
      results after saved memos final index result edits after.native.machine.heap := by
  obtain ⟨next, final, actual, reads, _receipt, _returned, _numeric, _sameLength⟩ :=
    class_reads formulas solver inventory record coherent active values before memo profile frame fits
      available domains physical covered memos valid room observed
  exact ⟨final, SourceCurrentClassSelectedChildLineage.class_selected reads coherent active frame.ready
    frame.admitted available domains physical covered valid history output selected⟩

end MicroCFTA.SourceCurrentActualClassSemanticReads
