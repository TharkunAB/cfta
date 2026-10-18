import MicroCFTA.SourceCurrentGeneratedQueryGuardResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardLimits

/-!
# Raw guard envelopes from initial native query support

The finite alphabet retains literal source conjunctions. Numeric guard
limits follow the same extension schedule. Initial query support constructs
its actual return and bounds every stored raw guard at that return.
The heap annotation imposes no hereditary finite ordinary domain.
-/
namespace MicroCFTA.SourceCurrentNativeGuardEnvelope
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits Bounds)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound

/-- Iterate raw guard limits in the literal alphabet extension order. -/
def advance (limits : Limits) : Nat → Limits
  | 0 => limits
  | count + 1 => advance (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.step limits) count

private theorem alphabet_step (alphabet : List Guard) (limits : Limits)
    (bounded : ∀ guard ∈ alphabet, Bounds limits guard) :
    ∀ guard ∈ SourceCurrentNativeGuardAlphabet.step alphabet,
      Bounds (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.step limits) guard := by
  intro guard member
  rcases List.mem_append.mp member with earlier | pair
  · rcases List.mem_append.mp earlier with initial | top
    · exact SourceCurrentAllocatedFiniteOrdinaryGuardLimits.bounds_mono guard (bounded guard initial)
        (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.step_ge limits)
    · have same : guard = SourceEqualityConstraintConstructors.top := List.mem_singleton.mp top
      subst guard
      exact SourceCurrentAllocatedFiniteOrdinaryGuardLimits.top_bounds _
  · obtain ⟨first, firstMember, mapped⟩ := List.mem_flatMap.mp pair
    obtain ⟨second, secondMember, rfl⟩ := List.mem_map.mp mapped
    letI : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
    exact SourceCurrentAllocatedFiniteOrdinaryGuardLimits.conjoin_step GuardStructuralOrder.le first second limits
      (bounded first firstMember) (bounded second secondMember)

/-- Initial alphabet bounds cover every guard in the computed extension schedule. -/
theorem alphabet_advance (alphabet : List Guard) (limits : Limits) (count : Nat)
    (bounded : ∀ guard ∈ alphabet, Bounds limits guard) :
    ∀ guard ∈ SourceCurrentNativeGuardAlphabet.advance alphabet count, Bounds (advance limits count) guard := by
  induction count generalizing alphabet limits with
  | zero => exact bounded
  | succ count ih => exact ih _ _ (alphabet_step alphabet limits bounded)

variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial query facts construct the actual return with a computed flat raw guard envelope. -/
theorem complete (alphabet : List Guard) (limits : Limits) (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Checked (bits + 2)) (frame : Frame formulas solver inventory before)
    (fits : Fits profile before) (room : Room bits profile)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left) (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap)
    (bounded : ∀ guard ∈ alphabet, Bounds limits guard)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ next fuel result after,
      SourceCurrentGeneratedQueryFrameResources.Receipt profile formulas solver next fuel
        left right before result after memos ∧
      Heap (Bounds (advance limits (instructionBound profile.nodes profile.edges profile.mass)))
        after.native.machine.heap := by
  obtain ⟨next, fuel, result, after, receipt, carrier⟩ :=
    SourceCurrentGeneratedQueryGuardResources.complete alphabet profile formulas solver inventory before
      frame fits room left right leftAvailable rightAvailable leftClosed rightClosed known memos valid
  refine ⟨next, fuel, result, after, receipt, ?_⟩
  intro key edge found
  exact alphabet_advance alphabet limits _ bounded key.constraint (carrier key edge found)

end MicroCFTA.SourceCurrentNativeGuardEnvelope
