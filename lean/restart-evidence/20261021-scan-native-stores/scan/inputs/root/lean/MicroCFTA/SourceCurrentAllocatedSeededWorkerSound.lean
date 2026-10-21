import MicroCFTA.SourceCurrentAllocatedSeededWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedSeededWorkerStability
import MicroCFTA.SourceCurrentAllocatedSeededLanguage

/-!
# Physical graphs for successful literal seeded workers

Initial supported paths and reached word ranges construct a finite graph.
Its stable literal execution agrees with a supplied successful return.
The agreement includes the full checked state and its equality operations.
No arbitrary successful native observation is treated as a physical trace.
The language endpoint also retains the explicit initial inventory.
-/
namespace MicroCFTA.SourceCurrentAllocatedSeededWorkerSound
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
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
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Supported inputs identify the same physical fold at a supplied literal return. -/
theorem fold_verified
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (seed : List Int) (rest : List (List Int))
    (before : Checked width) (ranges : FoldRanges values (rest ++ [seed]) before)
    (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ rest ++ [seed], PathSupport unconstrained anchor path values)
    (p h n : Nat) (result : Value Symbol Guard) (after : Checked width)
    (done : fold p h n values seed rest before = .done result after) :
    Fold values (rest ++ [seed]) before result after ∧ Good after ∧
      Effects (physical before) (physical after) ∧ Extension before.native.machine after.native.machine ∧
      Scoped after.native ∧ Idle after.native ∧ Available after.native.machine.heap result ∧ result.free = [] := by
  obtain ⟨chosen, reached, actual, effects⟩ := SourceCurrentAllocatedSeededQuery.fold_complete
    unconstrained anchor anchorSemantic anchorReady values (rest ++ [seed]) before ranges good ready
    scopes idle available growth supported
  obtain ⟨P, H, N, stable⟩ := SourceCurrentAllocatedSeededWorkerCompletion.fold_complete actual
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedSeededWorkerStability.fold_done_unique
    (stable P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)) done
  exact ⟨actual, effects⟩

/-- Literal fold success derives a graph under its initial physical completion domain. -/
theorem fold_sound
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (seed : List Int) (rest : List (List Int))
    (before : Checked width) (ranges : FoldRanges values (rest ++ [seed]) before)
    (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ rest ++ [seed], PathSupport unconstrained anchor path values)
    (p h n : Nat) (result : Value Symbol Guard) (after : Checked width)
    (done : fold p h n values seed rest before = .done result after) :
    Fold values (rest ++ [seed]) before result after :=
  (fold_verified unconstrained anchor anchorSemantic anchorReady values seed rest before ranges good ready
    scopes idle available growth supported p h n result after done).1

/-- A supplied seeded return derives its graph, closed result, and complete reached invariants. -/
theorem seeded_verified
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width)
    (ranges : SeededRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (p h n : Nat) (result : Value Symbol Guard) (after : Checked width)
    (done : seeded p h n values paths before = .done result after) :
    Seeded values paths before result after ∧ Good after ∧
      Effects (physical before) (physical after) ∧ Extension before.native.machine after.native.machine ∧
      Scoped after.native ∧ Idle after.native ∧ Available after.native.machine.heap result ∧ result.free = [] := by
  obtain ⟨chosen, reached, actual, effects⟩ := SourceCurrentAllocatedSeededQuery.seeded_complete
    unconstrained anchor anchorSemantic anchorReady values paths before ranges good ready scopes idle
    available growth supported
  obtain ⟨P, H, N, stable⟩ := SourceCurrentAllocatedSeededWorkerCompletion.seeded_complete actual
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedSeededWorkerStability.seeded_done_unique
    (stable P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)) done
  exact ⟨actual, effects⟩

/-- Literal seeded success derives the same actual graph without a final-state premise. -/
theorem seeded_sound
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width)
    (ranges : SeededRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (p h n : Nat) (result : Value Symbol Guard) (after : Checked width)
    (done : seeded p h n values paths before = .done result after) :
    Seeded values paths before result after :=
  (seeded_verified unconstrained anchor anchorSemantic anchorReady values paths before ranges good ready
    scopes idle available growth supported p h n result after done).1

/-- The same successful seeded return derives admission and common-subtree inclusion. -/
theorem seeded_receipt
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width)
    (ranges : SeededRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (nonroot : ∀ path ∈ paths, path ≠ [])
    (p h n : Nat) (result : Value Symbol Guard) (after : Checked width)
    (done : seeded p h n values paths before = .done result after) :
    ∃ next, Seeded values paths before result after ∧
      SourceCurrentAllocatedSeededLanguage.Receipt formulas solver next before result after ∧
      (paths ≠ [] → SourceCurrentAllocatedSeededLanguage.Includes formulas solver values paths result) := by
  have actual := seeded_sound unconstrained anchor anchorSemantic anchorReady values paths before ranges
    good ready scopes idle available growth supported p h n result after done
  obtain ⟨next, receipt, included⟩ := SourceCurrentAllocatedSeededLanguage.Seeded.receipt
    formulas solver inventory unconstrained anchor anchorSemantic anchorReady actual ranges good ready scopes idle
    admitted available growth supported nonroot
  exact ⟨next, actual, receipt, included⟩

end MicroCFTA.SourceCurrentAllocatedSeededWorkerSound
