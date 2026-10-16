import MicroCFTA.SourceCurrentAllocatedNativeInventoryState

#print axioms MicroCFTA.SourceCurrentAllocatedNativeInventoryState.At.advanceNative
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInventoryState.At.advance
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInventoryState.initial
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInventoryState.query_complete
#check @MicroCFTA.SourceCurrentAllocatedNativeInventoryState.Inventory
#check @MicroCFTA.SourceCurrentAllocatedNativeInventoryState.Inventory.inputs
#check @MicroCFTA.SourceCurrentAllocatedNativeInventoryState.At
#check @MicroCFTA.SourceCurrentAllocatedNativeInventoryState.At.advanceNative
#check @MicroCFTA.SourceCurrentAllocatedNativeInventoryState.At.advance
#check @MicroCFTA.SourceCurrentAllocatedNativeInventoryState.initial
#check @MicroCFTA.SourceCurrentAllocatedNativeInventoryState.query_complete

namespace MicroCFTA.SourceCurrentAllocatedNativeInventoryStateProbes
open Cache Language IntersectSchedule InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeInventoryState
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

-- The actual cold native start requires no cache-result law.
theorem cold_initial (inventory : Inventory) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (width : Nat)
    (operations : SourceEqualityConstraintMemoAllocation.State) :
    At formulas solver inventory
      ⟨SourceRecursiveIntersectionThunks.initial width ⟨inventory.source, Cache.emptyState⟩, operations⟩ :=
  initial inventory formulas solver width _ operations (grows_refl _) (extends_refl _)

-- Literal heap and operation advancement retains the same model and native cells.
theorem physical_advance {inventory : Inventory} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {before : Checked width}
    (current : At formulas solver inventory before)
    (after : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula)
    (extension : Extension before.native.machine
      (SourceCurrentAllocatedQueryMemo.advancePhysical before after).native.machine) :
    At formulas solver inventory (SourceCurrentAllocatedQueryMemo.advancePhysical before after) ∧
      (SourceCurrentAllocatedQueryMemo.advancePhysical before after).native.nodes = before.native.nodes ∧
      (SourceCurrentAllocatedQueryMemo.advancePhysical before after).native.edges = before.native.edges ∧
      (SourceCurrentAllocatedQueryMemo.advancePhysical before after).operations = after.equality :=
  ⟨current.advance after extension, rfl, rfl, rfl⟩

section Query
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  (inventory : Inventory) (formulas : SourceGuards.Formulas FullSyntax.Formula)
  (solver : SourceGuards.Entailment FullSyntax.Formula)
  (state : Checked width) (good : Good state) (current : At formulas solver inventory state)
  (scopedCache : SourceCurrentAllocatedNativeScopeCache.Scoped state.native)
  (semantic : SemanticReady state.native.machine.heap) (idle : SourceRecursiveIntersectionNative.Idle state.native)
  (left right : Value Symbol Guard)
  (leftAvailable : Available state.native.machine.heap left) (rightAvailable : Available state.native.machine.heap right)
  (leftClosed : left.free = []) (rightClosed : right.free = [])
  (ranges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state)
include good current scopedCache semantic idle leftAvailable rightAvailable leftClosed rightClosed ranges

-- The same actual checked return has exact language, a computed inventory, and causal coverage.
theorem query_exact : ∃ next : Inventory, ∃ fuel value after,
    next.source = state.native.machine.heap ∧ next.roots = inventory.roots ++ [left, right] ∧
    execute (fuel + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state = .done value after ∧
    value.free = [] ∧ Available after.native.machine.heap value ∧
    At formulas solver next after ∧
    SourceCurrentAllocatedNativeInputModelTransport.Admitted
      (view next.source (SourceEqualityPCSGuard.holds formulas solver))
      (finiteInputMeaning (view next.source (SourceEqualityPCSGuard.holds formulas solver))
        (next.inputs (SourceEqualityPCSGuard.holds formulas solver))) after.native ∧
    SourceCurrentAllocatedNativeContextRebase.SeenAdmitted
      (next.inputs (SourceEqualityPCSGuard.holds formulas solver)) after.native ∧
    ∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term := by
  obtain ⟨next, fuel, value, after, sourceEq, rootsEq, receipt, afterAt⟩ := query_complete inventory formulas solver
    state good current scopedCache semantic idle left right leftAvailable rightAvailable leftClosed rightClosed ranges
  exact ⟨next, fuel, value, after, sourceEq, rootsEq, receipt.toWarmReceipt.done, receipt.closed, receipt.result,
    afterAt, afterAt.covered.admitted, afterAt.covered.seen_admitted, receipt.meaning⟩

-- A generated output is admitted to a second query with only its next reached range bound.
theorem two_queries : ∃ first : Inventory, ∃ fuel value after,
    first.source = state.native.machine.heap ∧ first.roots = inventory.roots ++ [left, right] ∧
    execute (fuel + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state = .done value after ∧
    ∀ _nextRanges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain value right)) after,
      ∃ next : Inventory, ∃ count result final,
        next.source = after.native.machine.heap ∧ next.roots = first.roots ++ [value, right] ∧
        execute (count + 1) (.code (requestNode IntersectionEmptyDomain.emptyDomain value right)) after = .done result final ∧
        At formulas solver next final ∧ result.free = [] ∧ Available final.native.machine.heap result ∧
        ∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output result term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term := by
  obtain ⟨first, fuel, value, after, sourceEq, rootsEq, receipt, afterAt⟩ := query_complete inventory formulas solver
    state good current scopedCache semantic idle left right leftAvailable rightAvailable leftClosed rightClosed ranges
  refine ⟨first, fuel, value, after, sourceEq, rootsEq, receipt.toWarmReceipt.done, ?_⟩
  intro nextRanges
  obtain ⟨next, count, result, final, nextSource, nextRoots, second, finalAt⟩ := query_complete first formulas solver
    after receipt.good afterAt receipt.scopedCache receipt.semantic receipt.idle value right receipt.result
    (receipt.keeps.available right rightAvailable) receipt.closed rightClosed nextRanges
  refine ⟨next, count, result, final, nextSource, nextRoots, second.toWarmReceipt.done,
    finalAt, second.closed, second.result, ?_⟩
  intro output term
  rw [second.meaning, receipt.meaning]
  exact ⟨fun proof => proof.1, fun proof => ⟨proof, proof.2⟩⟩
end Query
end MicroCFTA.SourceCurrentAllocatedNativeInventoryStateProbes

#print axioms MicroCFTA.SourceCurrentAllocatedNativeInventoryStateProbes.cold_initial
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInventoryStateProbes.physical_advance
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInventoryStateProbes.query_exact
#print axioms MicroCFTA.SourceCurrentAllocatedNativeInventoryStateProbes.two_queries
#check @MicroCFTA.SourceCurrentAllocatedNativeInventoryStateProbes.cold_initial
#check @MicroCFTA.SourceCurrentAllocatedNativeInventoryStateProbes.physical_advance
#check @MicroCFTA.SourceCurrentAllocatedNativeInventoryStateProbes.query_exact
#check @MicroCFTA.SourceCurrentAllocatedNativeInventoryStateProbes.two_queries
