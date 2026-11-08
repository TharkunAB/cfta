import MicroCFTA.SourceCurrentAllocatedTargetCallerResources
import MicroCFTA.SourceCurrentAllocatedNativeCreditProfile
import MicroCFTA.SourceCurrentAllocatedNativeCreditCompletion

/-!
# Native entry admission for actual target callers

Either the earlier Room certificate or initial instruction credit constructs
the same native request. The returned physical state supplies the existing
caller receipt and numeric forecast. Closed operands derive their own scope.
-/
namespace MicroCFTA.SourceCurrentAllocatedTargetQuery
open InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile step)
open SourceCurrentAllocatedNativeCreditProfile (Entry Admits)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound
local notation "massAfter" => SourceCurrentAllocatedRecursiveMassTrace.massAfter
variable {bits : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Either numeric entry certificate derives words for every raw prefix. -/
theorem ready_admitted_ranges (profile : Profile) (before : Checked (bits + 2))
    (ready : SourceCurrentConjunctionClassScan.Ready before) (fits : Fits profile before)
    (room : Admits bits profile) (left right : Value Symbol Guard)
    (leftAvailable : Available before.native.machine.heap left)
    (rightAvailable : Available before.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before := by
  let source := before.native.machine.heap
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left source
    ready.good.native.machine.1.coherent leftAvailable leftClosed
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right source
    ready.good.native.machine.1.coherent rightAvailable rightClosed
  rcases room with oldRoom | creditRoom
  · have actualRoom := fits.room oldRoom
    exact (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before ready.good ready.semantic
      left right leftOriginal rightOriginal leftAvailable rightAvailable actualRoom.1 actualRoom.2.1 actualRoom.2.2).1
  · have actualRoom := creditRoom.mono (show SourceCurrentAllocatedNativeResourceForecast.Le
        ⟨source.nodes.next, source.edges.next, before.native.machine.domains.next, profile.mass⟩ profile from
        ⟨fits.nodes, fits.edges, fits.domains, Nat.le_refl _⟩)
    have count := SourceCurrentAllocatedNativeComputedBudget.nodeBudget_le source ready.good.native.machine.1
      (fun _ _ => true)
      left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed fits.stored
    exact SourceCurrentAllocatedNativeCreditWordRanges.word_ranges bits
      (fun _ _ => true) before ready.good ready.semantic left right leftAvailable rightAvailable leftClosed rightClosed
      actualRoom.1 actualRoom.2.1 (Nat.lt_of_le_of_lt (Nat.add_le_add_left count _) actualRoom.2.2)

/-- Initial caller facts construct the exact query return and its next resource profile. -/
theorem finite_caller_admitted_resources (profile : Profile)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller (bits + 2)) (left right : Value Symbol Guard) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (fits : Fits profile before.checked) (room : Admits bits profile)
    (leftAvailable : Available before.checked.native.machine.heap left)
    (rightAvailable : Available before.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ next value after,
      next.source = before.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      Receipt formulas solver next left right before.checked value after memos ∧
      Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after before.fourth before.merge) memos ∧
      SourceEqualityNativeDemand.execute (instructionBound profile.nodes profile.edges profile.mass + 1)
        (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked = .done value after ∧
      Fits (step profile) after ∧
      InternedValueMass.value value ≤ massAfter (instructionBound profile.nodes profile.edges profile.mass) profile.mass := by
  rcases room with oldRoom | creditRoom
  · exact finite_caller_resources profile formulas solver inventory before left right memos initial fits oldRoom
      leftAvailable rightAvailable leftClosed rightClosed
  · have actualRoom := creditRoom.mono (show SourceCurrentAllocatedNativeResourceForecast.Le
        ⟨before.checked.native.machine.heap.nodes.next, before.checked.native.machine.heap.edges.next,
          before.checked.native.machine.domains.next, profile.mass⟩ profile from
        ⟨fits.nodes, fits.edges, fits.domains, Nat.le_refl _⟩)
    obtain ⟨fuel, value, after, physical, _idle, count, _done, stored, mass, nodes, edges, domains⟩ :=
      SourceCurrentAllocatedNativeCreditCompletion.computed bits (SourceEqualityPCSGuard.holds formulas solver)
        before.checked initial.ready.good initial.ready.semantic initial.ready.idle left right
        leftAvailable rightAvailable leftClosed rightClosed fits.stored actualRoom.1 actualRoom.2.1 actualRoom.2.2
    have actual : Step left right before.checked value after := .run physical.trace
    obtain ⟨next, source, roots, receipt, post⟩ := actual.caller_post initial
      leftAvailable rightAvailable leftClosed rightClosed
    have larger := SourceCurrentAllocatedNativeComputedBudget.instructionBound_mono
      fits.nodes fits.edges (Nat.le_refl profile.mass)
    have total := Nat.le_trans count larger
    have done := SourceEqualityNativeDemand.done_stable (fuel + 1)
      (instructionBound profile.nodes profile.edges profile.mass - fuel)
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked after value physical.done
    have sameFuel : fuel + 1 + (instructionBound profile.nodes profile.edges profile.mass - fuel) =
        instructionBound profile.nodes profile.edges profile.mass + 1 := by omega
    rw [sameFuel] at done
    have massBound := SourceCurrentAllocatedRecursiveMassMonotone.massAfter_count_mono larger profile.mass
    have credits := SourceCurrentAllocatedRecursiveMassMonotone.credit_count_mono larger profile.mass
    refine ⟨next, value, after, source, roots, receipt, post, done, ?_, Nat.le_trans mass massBound⟩
    exact ⟨Nat.le_trans nodes (Nat.add_le_add fits.nodes credits),
      Nat.le_trans edges (Nat.add_le_add fits.edges credits),
      Nat.le_trans domains (Nat.add_le_add fits.domains larger), stored.mono massBound⟩
/-- Every successful raw return has the same caller laws and resource bounds at its full state. -/
theorem raw_done_caller_admitted_resources (profile : Profile) (fuel : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller (bits + 2)) (after : Checked (bits + 2))
    (left right value : Value Symbol Guard) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (fits : Fits profile before.checked) (room : Admits bits profile)
    (leftAvailable : Available before.checked.native.machine.heap left)
    (rightAvailable : Available before.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (done : SourceEqualityNativeDemand.execute fuel
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) before.checked = .done value after) :
    ∃ next,
      next.source = before.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
      Receipt formulas solver next left right before.checked value after memos ∧
      Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after before.fourth before.merge) memos ∧
      Fits (step profile) after ∧
      InternedValueMass.value value ≤ massAfter (instructionBound profile.nodes profile.edges profile.mass) profile.mass := by
  obtain ⟨next, result, reached, source, roots, receipt, post, produced, bounded, mass⟩ :=
    finite_caller_admitted_resources profile formulas solver inventory before left right memos initial fits room
      leftAvailable rightAvailable leftClosed rightClosed
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedNativeColdClosedExact.completed_unique
    fuel (instructionBound profile.nodes profile.edges profile.mass + 1) _ before.checked
      after reached value result done produced
  exact ⟨next, source, roots, receipt, post, bounded, mass⟩


end MicroCFTA.SourceCurrentAllocatedTargetQuery
