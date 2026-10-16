import MicroCFTA.SourceCurrentAllocatedSeededWorkerSound

namespace MicroCFTA.SeededWorkerSoundKernels
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedSeededQuery (Fold Seeded FoldRanges SeededRanges)
open SourceCurrentAllocatedSeededWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "Scoped" => SourceCurrentAllocatedNativeScopeCache.Scoped
local notation "Idle" => SourceRecursiveIntersectionNative.Idle
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

theorem successful_result_physical
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width)
    (ranges : SeededRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (p h n : Nat) (result : Value Symbol Guard) (after : Checked width)
    (done : seeded p h n values paths before = .done result after) :
    Seeded values paths before result after ∧
      InternedFreshOrdinaryCostHeap.Heap after.native.machine.heap ∧
      SourceCurrentConjunctionEquality.Fields after.operations after.native.machine.heap ∧
      Available after.native.machine.heap result ∧ result.free = [] := by
  obtain ⟨actual, _, effects, _, _, _, resident, closed⟩ :=
    SourceCurrentAllocatedSeededWorkerSound.seeded_verified unconstrained anchor anchorSemantic anchorReady
      values paths before ranges good ready scopes idle available growth supported p h n result after done
  exact ⟨actual, effects.ready.costs, effects.ready.fields, resident, closed⟩

theorem successful_seeded_then_next_query
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width)
    (ranges : SeededRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (nonroot : ∀ path ∈ paths, path ≠ [])
    (p h n : Nat) (result right : Value Symbol Guard) (after : Checked width)
    (done : seeded p h n values paths before = .done result after)
    (rightAvailable : Available before.native.machine.heap right) (rightClosed : right.free = [])
    (nextRanges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain result right)) after) :
    ∃ finalInventory fuel output final,
      SourceCurrentAllocatedNativeCoveredQuery.Receipt finalInventory.source formulas solver
        (Inventory.inputs finalInventory (SourceEqualityPCSGuard.holds formulas solver))
        fuel result right after output final ∧
      At formulas solver finalInventory final ∧ output.free = [] ∧
      (paths ≠ [] → ∀ ambient symbol terms part,
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
        (∀ path ∈ paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right part →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient output part) := by
  obtain ⟨next, _, receipt, included⟩ := SourceCurrentAllocatedSeededWorkerSound.seeded_receipt
    formulas solver inventory unconstrained anchor anchorSemantic anchorReady values paths before ranges good ready
    scopes idle admitted available growth supported nonroot p h n result after done
  obtain ⟨finalInventory, fuel, output, final, _, _, query, finalAt⟩ :=
    SourceCurrentAllocatedNativeInventoryState.query_complete next formulas solver after receipt.good
      receipt.admitted receipt.scopes receipt.effects.ready.semantic receipt.idle result right receipt.available
      (receipt.effects.keeps.available right rightAvailable) receipt.closed rightClosed nextRanges
  refine ⟨finalInventory, fuel, output, final, query, finalAt, query.closed, ?_⟩
  intro nonempty ambient symbol terms part accepted selected rightMeaning
  exact (query.meaning ambient part).mpr ⟨included nonempty ambient symbol terms part accepted selected, rightMeaning⟩

theorem three_paths_rotate_to_last_seed
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (seed first second : List Int) (before : Checked width)
    (ranges : SeededRanges values [seed, first, second] before) (good : Good before)
    (ready : Ready (physical before)) (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ [seed, first, second], PathSupport unconstrained anchor path values)
    (p h n : Nat) (result : Value Symbol Guard) (after : Checked width)
    (done : seeded p h n values [seed, first, second] before = .done result after) :
    Fold values [first, second, seed] before result after := by
  have actual := SourceCurrentAllocatedSeededWorkerSound.seeded_sound
    unconstrained anchor anchorSemantic anchorReady values [seed, first, second] before ranges good ready
    scopes idle available growth supported p h n result after done
  cases actual with
  | nonempty actual => exact actual

theorem empty_paths_return_entire_state (p h n : Nat) (values : List (Value Symbol Guard))
    (before : Checked width) : seeded p h n values [] before = .done .empty before := rfl

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
theorem failed_prefix_does_not_enter (fault : Fault width) (before : Checked width)
    (next : Value Symbol Guard → Checked width → Outcome width) :
    (Outcome.failed fault before).bind next = .failed fault before := rfl

end MicroCFTA.SeededWorkerSoundKernels

#print axioms MicroCFTA.SeededWorkerSoundKernels.successful_result_physical
#check @MicroCFTA.SeededWorkerSoundKernels.successful_result_physical
#print axioms MicroCFTA.SeededWorkerSoundKernels.successful_seeded_then_next_query
#check @MicroCFTA.SeededWorkerSoundKernels.successful_seeded_then_next_query
#print axioms MicroCFTA.SeededWorkerSoundKernels.three_paths_rotate_to_last_seed
#check @MicroCFTA.SeededWorkerSoundKernels.three_paths_rotate_to_last_seed
#print axioms MicroCFTA.SeededWorkerSoundKernels.empty_paths_return_entire_state
#check @MicroCFTA.SeededWorkerSoundKernels.empty_paths_return_entire_state
#print axioms MicroCFTA.SeededWorkerSoundKernels.failed_prefix_does_not_enter
#check @MicroCFTA.SeededWorkerSoundKernels.failed_prefix_does_not_enter
