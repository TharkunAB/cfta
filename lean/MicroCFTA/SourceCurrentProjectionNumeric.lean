import MicroCFTA.SourceCurrentProjectionInitialResources

/-!
# Complete selected projection at initial computed fuels

Initial path data, literal forest count, and current scalar resources
determine both proof fuels and the complete returned resource envelope.
The endpoint constructs its own graph and exact bounded worker return.
-/
namespace MicroCFTA.SourceCurrentProjectionNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionGraph (Forest)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentProjectionInitialResources (forestBound)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- The static worker bound depends only on signed path length. -/
def workFuel (path : List Int) : Nat := SourceCurrentProjectionNumericReplay.workFuel path

/-- The complete initial scalar envelope supplies every demanded recursive read. -/
def readFuel (path : List Int) (count resource : Nat) : Nat :=
  SourceCurrentProjectionUnionResources.readFuel (forestBound path count resource)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The same actual forest graph executes at the computed initial fuels and every larger pair. -/
theorem of_forest {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : Forest path values before result after) (resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (domain : ForestClosed path values) (fits : Fits resource before) :
    SourceEqualityProjectionWorker.forest (workFuel path) (readFuel path values.length resource)
      path values before = .done result after ∧
      Fits (forestBound path values.length resource) after ∧
      ∀ workExtra readExtra,
        SourceEqualityProjectionWorker.forest (workFuel path + workExtra)
          (readFuel path values.length resource + readExtra) path values before = .done result after := by
  have checked := SourceCurrentProjectionInitialResources.forest_bound path actual resource semantic costs available domain fits
  refine ⟨SourceCurrentProjectionNumericReplay.forest_replay checked.2 _ _ (Nat.le_refl _) (Nat.le_refl _), checked.1, ?_⟩
  intro workExtra readExtra
  exact SourceCurrentProjectionNumericReplay.forest_replay checked.2 _ _ (Nat.le_add_right _ _) (Nat.le_add_right _ _)

/-- Initial selected support constructs the complete actual forest projection at its own computed fuels. -/
theorem complete (path : List Int) (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (resource : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (domain : ForestClosed path values) (fits : Fits resource before) :
    ∃ result after,
      Forest path values before result after ∧
      SourceEqualityProjectionWorker.forest (workFuel path) (readFuel path values.length resource)
        path values before = .done result after ∧
      Keeps before after ∧ SemanticReady after ∧ CostHeap after ∧ Available after result ∧ result.free = [] ∧
      Fits (forestBound path values.length resource) after ∧
      InternedValueMass.value result ≤ forestBound path values.length resource ∧
      ∀ workExtra readExtra,
        SourceEqualityProjectionWorker.forest (workFuel path + workExtra)
          (readFuel path values.length resource + readExtra) path values before = .done result after := by
  obtain ⟨result, after, actual, kept, ready, resultAvailable, closed⟩ :=
    SourceEqualityProjectionPathComplete.forest_complete path values before semantic available domain
  have checked := of_forest actual resource semantic costs available domain fits
  have effects := SourceEqualityProjectionCosts.forest_effects actual semantic costs available
  exact ⟨result, after, actual, checked.1, kept, ready, effects.2.2.1, resultAvailable, closed, checked.2.1,
    InternedValueMassHeap.available after checked.2.1.stored result resultAvailable, checked.2.2⟩

end MicroCFTA.SourceCurrentProjectionNumeric
