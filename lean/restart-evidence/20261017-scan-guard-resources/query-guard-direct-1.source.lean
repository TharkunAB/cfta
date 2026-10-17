import MicroCFTA.SourceCurrentGeneratedQueryFrameResources
import MicroCFTA.SourceCurrentNativeGuardTrace

/-!
# Initial finite guard forecasts for complete native queries

The original profile bounds the number of guard extensions. The query
constructs its own physical trace. Its same return retains the full query
receipt and a guard carrier computed before execution.
-/
namespace MicroCFTA.SourceCurrentGeneratedQueryGuardResources
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound
variable {width bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The initial profile determines a finite carrier for every guard the query can write. -/
noncomputable def forecast (alphabet : List Guard) (profile : Profile) : List Guard :=
  SourceCurrentNativeGuardAlphabet.advance alphabet (instructionBound profile.nodes profile.edges profile.mass)

/-- The one-query guard forecast retains every initial guard. -/
theorem forecast_ge (alphabet : List Guard) (profile : Profile) : alphabet ⊆ forecast alphabet profile :=
  fun _ member => SourceCurrentNativeGuardAlphabet.mem_advance_of_mem member _

/-- The actual trace in a complete query receipt derives its initial guard forecast. -/
theorem of_query {profile : Profile} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {inventory : Inventory} {fuel : Nat}
    {left right result : Value Symbol Guard} {before after : Checked width} {memos : Memos}
    (actual : SourceCurrentGeneratedQueryFrameResources.Receipt profile formulas solver inventory fuel
      left right before result after memos)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before) (alphabet : List Guard)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap) :
    Heap (fun guard => guard ∈ forecast alphabet profile) after.native.machine.heap :=
  (SourceCurrentNativeGuardTrace.bounded alphabet _ actual.trace good (fun _ => trivial)
    known (fun _ => trivial) actual.count).1

/-- Initial query invariants construct the complete return and its finite guard carrier together. -/
theorem complete (alphabet : List Guard) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked (bits + 2)) (frame : Frame formulas solver inventory before)
    (fits : Fits profile before) (room : Room bits profile)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ next fuel value after,
      SourceCurrentGeneratedQueryFrameResources.Receipt profile formulas solver next fuel left right before value after memos ∧
      Heap (fun guard => guard ∈ forecast alphabet profile) after.native.machine.heap := by
  obtain ⟨next, fuel, value, after, actual⟩ := SourceCurrentGeneratedQueryFrameResources.complete profile
    formulas solver inventory before frame fits room left right leftAvailable rightAvailable leftClosed rightClosed memos valid
  exact ⟨next, fuel, value, after, actual, of_query actual frame.ready.good alphabet known⟩

end MicroCFTA.SourceCurrentGeneratedQueryGuardResources
