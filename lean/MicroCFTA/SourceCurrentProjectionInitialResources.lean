import MicroCFTA.SourceCurrentProjectionNumericControl
import MicroCFTA.SourceCurrentProjectionNumericReplay
import MicroCFTA.SourceEqualityProjectionPathComplete
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Initial resources for complete selected projection

The path induction retains the selected closure domain. Ordered rows use
their original occurrence count at successive actual heaps. Recursive heads
use the complete initial reader bound before their ordinary projection.
-/
namespace MicroCFTA.SourceCurrentProjectionInitialResources
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache (Ordinary)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityProjectionGraph (Project ProjectRows Forest select select_member)
open SourceEqualityProjectionPathDomain (NodeClosed RowsClosed ForestClosed)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentProjectionNumericReplay (ProjectReady RowsReady ForestReady)
open SourceCurrentProjectionNumericControl (bound ordinary rowsStep rowsBound)
open SourceCurrentProjectionUnionResources (readFuel headGrowth unionGrowth)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

private theorem closed_domain (path : List Int) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) : NodeClosed path value := by
  induction path generalizing value with
  | nil => simpa only [NodeClosed] using closed
  | cons index path ih =>
      cases value with
      | empty => simp only [NodeClosed]
      | reference | union | mu => simpa only [NodeClosed] using closed
      | node entry edges depth free =>
          rw [NodeClosed]
          intro edge member child found
          have facts := semantic.ready.semantic.1.normal.facts
          have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
          have childAvailable := facts.cached.edges edge.entry.key edge (resident edge member) child (select_member found)
          have childrenClosed := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
          exact ih child childAvailable (childrenClosed edge member child (select_member found))

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem rows_bound (path : List Int) (index : Int) (child : Nat → Nat)
    (childBound : ∀ {value result : Value Symbol Guard} {before after : State Symbol Guard}
      (actual : Project path value before result after) (resource : Nat),
      SemanticReady before → CostHeap before → Available before value → NodeClosed path value → Fits resource before →
      Fits (child resource) after ∧ ProjectReady (readFuel (child resource)) actual)
    {edges : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard} {values : List (Value Symbol Guard)}
    (actual : ProjectRows path index edges before values after) (resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges)
    (domain : RowsClosed path index edges) (fits : Fits resource before) :
    Fits (rowsBound child edges.length resource) after ∧
      RowsReady (readFuel (rowsBound child edges.length resource)) actual ∧ values.length ≤ edges.length := by
  induction edges generalizing before after values resource with
  | nil => cases actual; exact ⟨fits, .nil path index before, Nat.le_refl _⟩
  | cons edge edges ih =>
      cases actual with
      | missing absent rest =>
          have tail := ih rest resource semantic costs
            (fun row member => resident row (List.mem_cons_of_mem _ member))
            (fun row member => domain row (List.mem_cons_of_mem _ member)) fits
          have increase := SourceCurrentProjectionNumericControl.rowsBound_count_mono child (Nat.le_succ edges.length) resource
          exact ⟨tail.1.mono increase, .missing absent (tail.2.1.mono (SourceCurrentProjectionUnionResources.readFuel_mono increase)),
            Nat.le_trans tail.2.2 (by simp only [List.length_cons]; omega)⟩
      | @selected index value path before result middle edges values after edge found first rest =>
          have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
            (resident edge List.mem_cons_self) _ (select_member found)
          have firstBound := childBound first resource semantic costs available (domain edge List.mem_cons_self _ found) fits
          have firstEffects := SourceEqualityProjectionCosts.project_effects first semantic costs available
          have tail := ih rest (rowsStep child resource) firstEffects.2.1 firstEffects.2.2.1
            (fun row member => InternedEdgeResidency.edge_grows before middle firstEffects.1.growth row
              (resident row (List.mem_cons_of_mem _ member)))
            (fun row member => domain row (List.mem_cons_of_mem _ member))
            (firstBound.1.mono (SourceCurrentProjectionNumericControl.rowsStep_child child resource))
          have increase : child resource ≤ rowsBound child (edge :: edges).length resource :=
            SourceCurrentProjectionNumericControl.child_le_rowsBound child (by simp only [List.length_cons]; omega)
          exact ⟨tail.1, .selected found
            (firstBound.2.mono (SourceCurrentProjectionUnionResources.readFuel_mono increase)) tail.2.1,
            by simp only [List.length_cons]; omega⟩

private theorem ordinary_bound (path : List Int) (index : Int)
    (childBound : ∀ {value result : Value Symbol Guard} {before after : State Symbol Guard}
      (actual : Project path value before result after) (resource : Nat),
      SemanticReady before → CostHeap before → Available before value → NodeClosed path value → Fits resource before →
      Fits (bound path.length resource) after ∧ ProjectReady (readFuel (bound path.length resource)) actual)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project (index :: path) value before result after) (resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (domain : NodeClosed (index :: path) value) (fits : Fits resource before) (isOrdinary : Ordinary value) :
    Fits (ordinary (bound path.length) resource) after ∧
      ProjectReady (readFuel (ordinary (bound path.length) resource)) actual := by
  cases actual with
  | empty =>
      exact ⟨fits.mono (SourceCurrentProjectionNumericControl.ordinary_ge _ resource), .empty index path before⟩
  | @ordinary path index edges before values middle result after entry depth free rows joined =>
      have facts := semantic.ready.semantic.1.normal.facts
      have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
      have localDomain : RowsClosed path index edges := by simpa only [NodeClosed, RowsClosed] using domain
      have first := rows_bound path index (bound path.length)
        childBound rows resource semantic costs resident localDomain fits
      have mass := InternedValueMassHeap.available before fits.stored (.node entry edges depth free) available
      have length : edges.length ≤ resource := Nat.le_trans (InternedStoredEncodingWidth.edges_length edges)
        (by simp only [InternedValueMass.value] at mass; omega)
      have padded := SourceCurrentProjectionNumericControl.rowsBound_count_mono (bound path.length) length resource
      have rowsPhysical := SourceEqualityProjectionCosts.rows_effects rows semantic costs resident
      have rowsClosed := SourceEqualityProjectionPathDomain.rows_effects rows semantic resident localDomain
      have last := SourceCurrentProjectionUnionResources.union joined resource (rowsBound (bound path.length) resource resource)
        rowsPhysical.2.1 rowsPhysical.2.2.1 rowsClosed.2.2.1 rowsClosed.2.2.2
        (first.1.mono padded) (Nat.le_trans first.2.2 length)
      have allRows := Nat.le_trans padded (SourceCurrentProjectionNumericControl.rowsBound_le_ordinary _ resource)
      exact ⟨last.2.1, .ordinary (first.2.1.mono (SourceCurrentProjectionUnionResources.readFuel_mono allRows)) last.2.2.2.2⟩
  | recursive recursive head body =>
      cases value with
      | empty | reference | node => cases recursive
      | union | mu => cases isOrdinary

/-- Initial selected support bounds the exact projection and every demanded shared read. -/
theorem node_bound (path : List Int) {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project path value before result after) (resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (domain : NodeClosed path value) (fits : Fits resource before) :
    Fits (bound path.length resource) after ∧ ProjectReady (readFuel (bound path.length resource)) actual := by
  induction path generalizing value result before after resource with
  | nil =>
      cases actual
      exact ⟨fits.mono (SourceCurrentProjectionNumericControl.bound_ge 0 resource), .root value before⟩
  | cons index path ih =>
      cases actual with
      | empty =>
          exact ⟨fits.mono (SourceCurrentProjectionNumericControl.bound_ge (path.length + 1) resource),
            .empty index path before⟩
      | ordinary rows joined =>
          have first := ordinary_bound path index (fun actual resource => ih actual resource)
            (.ordinary rows joined) resource semantic costs available domain fits trivial
          have increase := SourceCurrentProjectionNumericControl.ordinary_le_bound path.length resource
          exact ⟨first.1.mono increase, first.2.mono (SourceCurrentProjectionUnionResources.readFuel_mono increase)⟩
      | recursive recursive head body =>
          have closed := SourceEqualityProjectionPathDomain.recursive_closed recursive domain
          have first := SourceCurrentProjectionUnionResources.head head resource semantic costs available closed fits
          have physical := SourceEqualityProjectionCosts.head_effects head semantic costs available
          have ordinary := head.verified semantic.ready available closed
          have bodyDomain := closed_domain (index :: path) _ _ physical.2.1 physical.2.2.2 ordinary.2.2.1
          have last := ordinary_bound path index (fun actual resource => ih actual resource)
            body (headGrowth resource) physical.2.1 physical.2.2.1 physical.2.2.2 bodyDomain first.2.1 ordinary.2.2.2
          have increase := SourceCurrentProjectionNumericControl.headGrowth_le_bound path.length resource
          exact ⟨last.1, .recursive recursive
            (first.2.2.2.2.mono (SourceCurrentProjectionUnionResources.readFuel_mono increase)) last.2⟩

/-- A root forest pays its literal union count; a proper path follows one selected original value. -/
def forestBound (path : List Int) (count resource : Nat) : Nat :=
  match path with
  | [] => unionGrowth count resource
  | _ :: tail => bound tail.length resource

/-- The complete forest bound retains the original heap in every signed lookup branch. -/
theorem forestBound_ge (path : List Int) (count resource : Nat) : resource ≤ forestBound path count resource := by
  cases path with
  | nil => exact SourceCurrentProjectionUnionResources.unionGrowth_ge count resource
  | cons index path => exact SourceCurrentProjectionNumericControl.bound_ge path.length resource

/-- Initial selected support derives resources and shared read readiness for the same forest graph. -/
theorem forest_bound (path : List Int) {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard} (actual : Forest path values before result after) (resource : Nat)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (domain : ForestClosed path values) (fits : Fits resource before) :
    Fits (forestBound path values.length resource) after ∧
      ForestReady (readFuel (forestBound path values.length resource)) actual := by
  cases actual with
  | root joined =>
      have checked := SourceCurrentProjectionUnionResources.union joined values.length resource semantic costs available domain fits (Nat.le_refl _)
      exact ⟨checked.2.1, .root checked.2.2.2.2⟩
  | missing absent =>
      exact ⟨fits.mono (SourceCurrentProjectionNumericControl.bound_ge _ resource), .missing absent _ before⟩
  | selected found body =>
      have checked := node_bound _ body resource semantic costs (available _ (select_member found)) (domain _ found) fits
      exact ⟨checked.1, .selected found checked.2⟩

end MicroCFTA.SourceCurrentProjectionInitialResources
