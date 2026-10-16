import MicroCFTA.SourceCurrentAllocatedSeededLanguage

#print axioms MicroCFTA.SourceCurrentAllocatedSeededLanguage.fold_complete
#print axioms MicroCFTA.SourceCurrentAllocatedSeededLanguage.seeded_complete
#print axioms MicroCFTA.SourceCurrentAllocatedSeededLanguage.Seeded.receipt
#print axioms MicroCFTA.SourceCurrentAllocatedSeededLanguage.false_class_complete
#print axioms MicroCFTA.SourceCurrentAllocatedSeededLanguage.false_class_receipt
#check @MicroCFTA.SourceCurrentAllocatedSeededLanguage.Includes
#check @MicroCFTA.SourceCurrentAllocatedSeededLanguage.Receipt
#check @MicroCFTA.SourceCurrentAllocatedSeededLanguage.fold_complete
#check @MicroCFTA.SourceCurrentAllocatedSeededLanguage.seeded_complete
#check @MicroCFTA.SourceCurrentAllocatedSeededLanguage.Seeded.receipt
#check @MicroCFTA.SourceCurrentAllocatedSeededLanguage.false_class_complete
#check @MicroCFTA.SourceCurrentAllocatedSeededLanguage.false_class_receipt

namespace MicroCFTA.SourceCurrentAllocatedSeededLanguageIndependentProbes
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
open SourceCurrentAllocatedSeededQuery (Operand Fold Seeded SeededRanges)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedSeededLanguage
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
  (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool)
  (anchor : State Symbol Guard) (anchorSemantic : SemanticReady anchor)
  (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
  (values : List (Value Symbol Guard)) (before : Checked width)
  (good : Good before) (ready : Ready (physical before))
  (scopes : SourceCurrentAllocatedNativeScopeCache.Scoped before.native)
  (idle : SourceRecursiveIntersectionNative.Idle before.native)
  (admitted : At formulas solver inventory before)
  (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
include anchorSemantic anchorReady good ready scopes idle admitted available growth

-- Empty input returns literal empty and the exact unchanged complete checked state.
theorem empty_seed : ∃ next, Receipt formulas solver next before .empty before ∧
    At formulas solver next before := by
  obtain ⟨result, after, next, actual, receipt, _⟩ := seeded_complete formulas solver inventory
    (fun _ => false) anchor anchorSemantic anchorReady values [] before trivial good ready scopes idle admitted
    available growth (by intro path absent; cases absent) (by intro path absent; cases absent)
  have equal := actual.unique (Seeded.nil before)
  rcases equal with ⟨rfl, rfl⟩
  exact ⟨next, receipt, receipt.admitted⟩

-- Two paths use the second projection before the first-seed projection, then one checked request.
theorem two_path_order (first second : List Int)
    (ranges : SeededRanges values [first, second] before)
    (supported : ∀ path ∈ [first, second], PathSupport unconstrained anchor path values)
    (nonroot : ∀ path ∈ [first, second], path ≠ []) :
    ∃ secondValue middle firstValue later fuel result after next,
      Operand second values before secondValue middle ∧ Operand first values middle firstValue later ∧
      SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain secondValue firstValue)) later
        (.code (.pure result)) after ∧
      Receipt formulas solver next before result after ∧ Includes formulas solver values [first, second] result := by
  obtain ⟨result, after, next, actual, receipt, included⟩ := seeded_complete formulas solver inventory
    unconstrained anchor anchorSemantic anchorReady values [first, second] before ranges good ready scopes idle
    admitted available growth supported nonroot
  cases actual with
  | nonempty fold =>
      cases fold with
      | cons own rest trace =>
          cases rest with
          | one seed => exact ⟨_, _, _, _, _, result, after, next, own, seed, trace, receipt, included (by simp)⟩

-- Three paths preserve both actual native calls and the source right-fold order.
theorem three_path_order (first second third : List Int)
    (ranges : SeededRanges values [first, second, third] before)
    (supported : ∀ path ∈ [first, second, third], PathSupport unconstrained anchor path values)
    (nonroot : ∀ path ∈ [first, second, third], path ≠ []) :
    ∃ secondValue middle thirdValue later firstValue seedAfter tail tailAfter tailFuel fuel result after next,
      Operand second values before secondValue middle ∧ Operand third values middle thirdValue later ∧
      Operand first values later firstValue seedAfter ∧
      SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace tailFuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain thirdValue firstValue)) seedAfter
        (.code (.pure tail)) tailAfter ∧
      SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel
        (.code (requestNode IntersectionEmptyDomain.emptyDomain secondValue tail)) tailAfter
        (.code (.pure result)) after ∧
      Receipt formulas solver next before result after ∧ Includes formulas solver values [first, second, third] result := by
  obtain ⟨result, after, next, actual, receipt, included⟩ := seeded_complete formulas solver inventory
    unconstrained anchor anchorSemantic anchorReady values [first, second, third] before ranges good ready scopes idle
    admitted available growth supported nonroot
  cases actual with
  | nonempty fold =>
      cases fold with
      | cons own rest trace =>
          cases rest with
          | cons other remaining checked =>
              cases remaining with
              | one seed =>
                  exact ⟨_, _, _, _, _, _, _, _, _, _, result, after, next,
                    own, other, seed, checked, trace, receipt, included (by simp)⟩

-- A supplied actual seeded trace gets the derived physical and language facts by full-state uniqueness.
theorem actual_trace_receipt (paths : List (List Int)) {result : Value Symbol Guard} {after : Checked width}
    (actual : Seeded values paths before result after)
    (ranges : SeededRanges values paths before)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (nonroot : ∀ path ∈ paths, path ≠ []) :
    ∃ next, At formulas solver next after ∧ Good after ∧ result.free = [] ∧
      Available after.native.machine.heap result ∧
      SourceCurrentConjunctionEquality.Fields after.operations after.native.machine.heap ∧
      (paths ≠ [] → Includes formulas solver values paths result) := by
  obtain ⟨next, receipt, included⟩ := SourceCurrentAllocatedSeededLanguage.Seeded.receipt formulas solver inventory
    unconstrained anchor anchorSemantic anchorReady actual ranges good ready scopes idle admitted available growth supported nonroot
  exact ⟨next, receipt.admitted, receipt.good, receipt.closed, receipt.available, receipt.good.fields, included⟩

-- A whole seeded fold can feed the next generated query using only that next reached range bound.
theorem seeded_then_generated (paths : List (List Int)) (nonempty : paths ≠ [])
    (ranges : SeededRanges values paths before)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (nonroot : ∀ path ∈ paths, path ≠ []) :
    ∃ result after next, Seeded values paths before result after ∧
      Receipt formulas solver next before result after ∧ Includes formulas solver values paths result ∧
      ∀ _nextRanges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
        (.code (requestNode IntersectionEmptyDomain.emptyDomain result result)) after,
        ∃ finalInventory : Inventory, ∃ fuel value final,
          finalInventory.source = after.native.machine.heap ∧ finalInventory.roots = next.roots ++ [result, result] ∧
          execute (fuel + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain result result)) after = .done value final ∧
          At formulas solver finalInventory final ∧ value.free = [] ∧ Available final.native.machine.heap value ∧
          Includes formulas solver values paths value := by
  obtain ⟨result, after, next, actual, receipt, included⟩ := seeded_complete formulas solver inventory
    unconstrained anchor anchorSemantic anchorReady values paths before ranges good ready scopes idle admitted available growth supported nonroot
  have common := included nonempty
  refine ⟨result, after, next, actual, receipt, common, ?_⟩
  intro nextRanges
  obtain ⟨finalInventory, fuel, value, final, sourceEq, rootsEq, native, finalAt⟩ :=
    SourceCurrentAllocatedNativeInventoryState.query_complete next formulas solver after receipt.good receipt.admitted
      receipt.scopes receipt.effects.ready.semantic receipt.idle result result receipt.available receipt.available
      receipt.closed receipt.closed nextRanges
  refine ⟨finalInventory, fuel, value, final, sourceEq, rootsEq, native.toWarmReceipt.done,
    finalAt, native.closed, native.result, ?_⟩
  intro ambient symbol terms part accepted selected
  have acceptedResult := common ambient symbol terms part accepted selected
  exact (native.meaning ambient part).mpr ⟨acceptedResult, acceptedResult⟩

end MicroCFTA.SourceCurrentAllocatedSeededLanguageIndependentProbes

#print axioms MicroCFTA.SourceCurrentAllocatedSeededLanguageIndependentProbes.empty_seed
#print axioms MicroCFTA.SourceCurrentAllocatedSeededLanguageIndependentProbes.two_path_order
#print axioms MicroCFTA.SourceCurrentAllocatedSeededLanguageIndependentProbes.three_path_order
#print axioms MicroCFTA.SourceCurrentAllocatedSeededLanguageIndependentProbes.actual_trace_receipt
#print axioms MicroCFTA.SourceCurrentAllocatedSeededLanguageIndependentProbes.seeded_then_generated
#check @MicroCFTA.SourceCurrentAllocatedSeededLanguageIndependentProbes.empty_seed
#check @MicroCFTA.SourceCurrentAllocatedSeededLanguageIndependentProbes.two_path_order
#check @MicroCFTA.SourceCurrentAllocatedSeededLanguageIndependentProbes.three_path_order
#check @MicroCFTA.SourceCurrentAllocatedSeededLanguageIndependentProbes.actual_trace_receipt
#check @MicroCFTA.SourceCurrentAllocatedSeededLanguageIndependentProbes.seeded_then_generated
