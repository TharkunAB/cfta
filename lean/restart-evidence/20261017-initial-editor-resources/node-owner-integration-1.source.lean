import MicroCFTA.SourceCurrentConstrainedCapEditNumeric

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

namespace MicroCFTA.EditNumericInitialKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedSharedEditEffects (NodeReceipt)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
namespace Forecast
export SourceCurrentConstrainedCapEditForecast (planProfile stageFuel)
end Forecast
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentConstrainedCapMixedShared.Stored
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Cap" => SourceCurrentConstrainedCap.Cap Plain
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Own initial completion supplies the same result cap and every larger six-fuel return. -/
theorem completed_cap_and_larger (capturedDepth inputDepth level : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
    (known : Values base originals)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) originals)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (capturedCaps : ∀ original ∈ originals, Cap capturedDepth original)
    (edits : Edits EqualityNormalize.Path) (input : Value Symbol Guard) (before : SharedState (bits + 2))
    (inventory : Inventory) (profile : Profile) (small : sizeOf edits ≤ level)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (frame : Frame formulas solver inventory before.checked) (fits : Fits profile before.checked)
    (available : Available before.checked.native.machine.heap input) (safe : Safe edits input)
    (inputCap : Cap inputDepth input) (stored : Stored record originals before)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos)
    (room : Room bits (Forecast.planProfile record originals.length level profile)) :
    ∃ result after next final, ∃ actual : EditNode record originals edits input before result after,
      NodeReads formulas solver base actual memos final ∧
      NodeReceipt formulas solver next record originals base input before result after memos final ∧
      Frame formulas solver next after.checked ∧
      Fits (Forecast.planProfile record originals.length level profile) after.checked ∧
      Stored record originals after ∧
      Cap (SourceCurrentConstrainedCapMixedEdit.outputDepth capturedDepth inputDepth edits) result ∧
      ∀ e p h m s n,
        SourceCurrentConstrainedCapEditScans.editFuel level ≤ e →
        Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length level profile) ≤ p →
        Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length level profile) ≤ h →
        Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length level profile) ≤ m →
        Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length level profile) ≤ s →
        Forecast.stageFuel record originals.length (Forecast.planProfile record originals.length level profile) ≤ n →
        SourceCurrentAllocatedSharedEditWorker.edit record originals e p h m s n edits input before = .done result after := by
  obtain ⟨result, after, next, final, actual, reads, receipt, returned, numeric, saved, done⟩ :=
    SourceCurrentConstrainedCapEditNumeric.node_complete capturedDepth inputDepth level formulas solver record
      originals base known domains coherent active capturedCaps edits input before inventory profile small populated
      nonempty allowed ready frame fits available safe inputCap stored memos valid room
  have bounded := SourceCurrentConstrainedCapMixedEdit.node reads inventory capturedDepth inputDepth populated
    nonempty allowed ready available safe valid known domains stored capturedCaps inputCap
  refine ⟨result, after, next, final, actual, reads, receipt, returned, numeric, saved, bounded.2, ?_⟩
  intro e p h m s n he hp hh hm hs hn
  exact SourceCurrentAllocatedSharedEditWorkerStability.edit_done_stable done he hp hh hm hs hn

#print axioms completed_cap_and_larger
#check @completed_cap_and_larger
end MicroCFTA.EditNumericInitialKernels
