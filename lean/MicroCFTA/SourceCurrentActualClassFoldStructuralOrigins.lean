import MicroCFTA.SourceCurrentClassFoldStructuralOrigins
import MicroCFTA.SourceCurrentActualClassSemanticReads

/-!
# Structural sources at literal completed class fold returns

Initial numeric reservations construct semantic reads. Worker uniqueness
matches those reads with the observed return. Structural sources then
follow the actual chronological class calls. The statement also applies
to a completed tail before an enclosing traversal returns.
-/
namespace MicroCFTA.SourceCurrentActualClassFoldStructuralOrigins
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentRequiredRowOrigins (RowAt)
open SourceCurrentRequiredGuardOrigins (RowOrigin)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- An observed fold return derives its actual structural source or historical native/Head event. -/
theorem fold
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (records : List SourceEqualityClassOrder.Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List Node) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (physical : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (reserved : SourceCurrentConstrainedCapClassForecast.Reserved bits records values.length profile)
    {e p h m c n : Nat} {results : List Node} {after : Checked (bits + 2)} {saved : Memo}
    (observed : SourceCurrentAllocatedClassWorker.fold e p h m c n records values before memo =
      .done results after saved)
    (history : SourceCurrentNativeEdgeWriterGrowth.History before)
    (index : Nat) (value : Node) (selected : results[index]? = some value)
    {positions rowIndex row} (occurrence : RowAt value positions rowIndex row) :
    ∃ next final, ∃ actual : SourceCurrentAllocatedClassPass.Fold records values before memo results after saved,
      SourceCurrentAllocatedClassPass.FoldReads formulas solver actual memos final ∧
      SourceCurrentAllocatedClassPass.Receipt formulas solver next records values before memo
        results after saved memos final ∧
      Frame formulas solver next after ∧
      Fits (SourceCurrentConstrainedCapClassForecast.foldProfile records values.length profile) after ∧
      results.length = values.length ∧
      ((∃ original, values[index]? = some original ∧
          ∃ sourcePath sourceIndex source, RowAt original sourcePath sourceIndex source ∧ RowOrigin source row) ∨
        ∃ event residual sourceIndex source,
          SourceCurrentClassFoldStructuralOrigins.FoldEvent formulas solver actual index event ∧
          RowAt event residual sourceIndex source ∧ RowOrigin source row) := by
  obtain ⟨next,final,actual,reads,receipt,returned,numeric,length⟩ :=
    SourceCurrentActualClassSemanticReads.fold_reads formulas solver inventory records coherent active values before memo
      profile frame fits available domains physical covered memos valid reserved observed
  exact ⟨next,final,actual,reads,receipt,returned,numeric,length,
    SourceCurrentClassFoldStructuralOrigins.fold reads inventory coherent active frame.ready frame.admitted
      available domains physical covered valid history index value selected occurrence⟩

end MicroCFTA.SourceCurrentActualClassFoldStructuralOrigins
