import MicroCFTA.SourceCurrentTargetNumeric
import MicroCFTA.SourceCurrentAllocatedTargetWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedSharedTargetState

/-!
# Semantic target reads at literal successful worker endpoints

Initial numeric completion constructs the semantic target execution.
Successful-return uniqueness identifies its complete result and both
returned states with any literal completed call. The observed fuel tuple
needs no comparison with the forecast fuel. Selected domains, initial
Frame and numeric reservations remain explicit. Untouched roots can be
open. A historical slot receipt also retains explicit transport from
that target return into the actual reader.
-/
namespace MicroCFTA.SourceCurrentActualTargetSemanticReads
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedTargetGraph (Target)
open SourceCurrentAllocatedTargetComplete (Receipt TargetReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "Stored" => SourceCurrentMemoMergeEffects.Stored
local notation "Covered" => SourceCurrentMemoMergeLanguage.CacheCovers
local notation "Forecast" => SourceCurrentConstrainedCapTargetForecast.targetProfile
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial target support constructs semantic reads at the exact observed return for any successful fuels. -/
theorem target
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (values : List Node) (paths : List (List Int))
    (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values) (domains : ∀ path ∈ paths, Domain path values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, Covered (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (reserved : SourceCurrentConstrainedCapTargetForecast.TargetReserved bits values.length paths profile)
    {p h m s n : Nat} {result : Node} {after : Checked (bits + 2)} {saved : Memo}
    (actual : SourceCurrentAllocatedTargetWorker.target p h m s n values paths before memo =
      .done result after saved) :
    ∃ next final, ∃ graph : Target values paths before memo result after saved,
      TargetReads formulas solver graph memos final ∧
      Receipt formulas solver next values paths before memo result after saved memos final ∧
      Frame formulas solver next after ∧ Fits (Forecast values.length paths profile) after := by
  obtain ⟨next,value,current,returned,final,graph,reads,receipt,lastFrame,lastFits,done⟩ :=
    SourceCurrentTargetNumeric.complete formulas solver inventory values paths before memo profile frame fits
      available domains stored covered memos valid reserved
  obtain ⟨rfl,rfl,rfl⟩ := SourceCurrentAllocatedTargetWorkerCompletion.target_done_unique actual done
  exact ⟨next,final,graph,reads,receipt,lastFrame,lastFits⟩

/-- A literal historical target and its initial support construct the full semantic slot receipt. -/
theorem slot_receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : Record) (values : List Node) (path : EqualityNormalize.Path)
    (member : path ∈ record.paths) (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ selected ∈ SourceEqualityClassTarget.operandPaths record.paths path, Domain selected values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, Covered (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (reserved : SourceCurrentConstrainedCapTargetForecast.TargetReserved bits values.length
      (SourceEqualityClassTarget.operandPaths record.paths path) profile)
    {p h m s n : Nat} {result : Node} {after : Checked (bits + 2)} {saved : Memo}
    (actual : SourceCurrentAllocatedTargetWorker.target p h m s n values
      (SourceEqualityClassTarget.operandPaths record.paths path) before memo = .done result after saved)
    (reader : Heap) (readerMemo : Memo)
    (keeps : SourceEqualityRequiredCache.Keeps after.native.machine.heap reader)
    (retained : Extends saved readerMemo) :
    SourceCurrentAllocatedSharedTargetState.SlotReceipt (bits + 2) formulas solver record values
      reader readerMemo path result := by
  obtain ⟨next,final,graph,reads,receipt,_lastFrame,_lastFits⟩ :=
    target formulas solver inventory values (SourceEqualityClassTarget.operandPaths record.paths path)
      before memo profile frame fits available domains stored covered memos valid reserved actual
  exact ⟨member,before,after,next,memo,saved,memos,final,graph,reads,receipt,keeps,retained⟩

end MicroCFTA.SourceCurrentActualTargetSemanticReads
