import MicroCFTA.SourceEqualityProjectionOutcomeMemos
import MicroCFTA.SourcePruningEnumerationProbeExposureArity

/-!
# Arity through every actual projection outcome

Each ordered read retains arity at its actual returned heap. A stopped
child retains its completed prefix. Recursive heads and ordinary unions
use their actual exposures and node constructors. Current semantic heaps,
cost heaps, and resident inputs supply every intermediate premise.
This result does not require closed inputs or a successful projection.
-/
namespace MicroCFTA.SourcePruningEnumerationProjectionArityOutcome
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityRequiredWorker (Result work)
open SourceEqualityProjectionWorker (project rows forest readAll union)
open SourceEqualityProjectionGraph (select select_member)
open SourceEqualityProjectionOutcomePrimitives (reached)
variable {Symbol : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "CtorState" => State Symbol Guard
local notation "ArityHeap" => SourcePruningEnumerationArityOrigins.Heap
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private theorem bind_heap {A B : Type} {actual : Result Symbol Guard A}
    {next : A → CtorState → Result Symbol Guard B}
    (first : ArityHeap (reached actual))
    (continuation : ∀ value after, actual = .done value after → ArityHeap (reached (next value after))) :
    ArityHeap (reached (actual.bind next)) := by
  cases actual with
  | done value after => exact continuation value after rfl
  | pending key after => exact first
  | unresolved name after => exact first
  | exhausted limit after => exact first

private theorem map_reached {A B : Type} (actual : Result Symbol Guard A) (f : A → B) :
    reached (actual.bind fun value after => .done (f value) after) = reached actual := by
  cases actual <;> rfl

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every ordered exposure outcome retains arity at the exact stopped or completed heap. -/
theorem readAll_heap (h : Nat) (values : List Node) (before : CtorState)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (known : ArityHeap before) :
    ArityHeap (reached (readAll h values before)) := by
  induction values generalizing before with
  | nil => exact known
  | cons value values ih =>
      have first := SourcePruningEnumerationProbeExposureArity.nodeEdges_heap h value before
        semantic.ready.semantic.1.normal.facts known (available value List.mem_cons_self)
      cases actual : MergedFreshOrdinaryExposure.nodeEdges h value before with
      | done edges middle =>
          have current : ArityHeap middle := by
            simpa only [actual, MergedSourceExposure.Result.state] using first
          have effects := SourceEqualityProjectionCosts.read_effects (.done h actual) semantic costs
            (available value List.mem_cons_self)
          have last := ih middle effects.2.1 effects.2.2.1
            (fun child member => effects.1.available child (available child (List.mem_cons_of_mem _ member))) current
          simpa only [readAll, actual, map_reached] using last
      | pending key after =>
          simpa only [readAll, actual, reached, MergedSourceExposure.Result.state] using first
      | unresolved name after =>
          simpa only [readAll, actual, reached, MergedSourceExposure.Result.state] using first
      | exhausted after =>
          simpa only [readAll, actual, reached, MergedSourceExposure.Result.state] using first

/-- Head reconstruction retains arity after its actual exposure, including stopped reads. -/
theorem head_heap (h : Nat) (value : Node) (before : CtorState)
    (semantic : SemanticReady before) (available : Available before value) (known : ArityHeap before) :
    ArityHeap (reached (SourceEqualityRequiredWorker.head h value before)) := by
  have first := SourcePruningEnumerationProbeExposureArity.nodeEdges_heap h value before
    semantic.ready.semantic.1.normal.facts known available
  cases actual : MergedFreshOrdinaryExposure.nodeEdges h value before with
  | done edges middle =>
      have current : ArityHeap middle := by
        simpa only [actual, MergedSourceExposure.Result.state] using first
      simpa only [SourceEqualityRequiredWorker.head, actual, work, reached] using
        SourcePruningEnumerationArityOrigins.node_heap edges middle current
  | pending key after =>
      simpa only [SourceEqualityRequiredWorker.head, actual, reached, MergedSourceExposure.Result.state] using first
  | unresolved name after =>
      simpa only [SourceEqualityRequiredWorker.head, actual, reached, MergedSourceExposure.Result.state] using first
  | exhausted after =>
      simpa only [SourceEqualityRequiredWorker.head, actual, reached, MergedSourceExposure.Result.state] using first

/-- The actual union retains arity through all reads and its final node constructor. -/
theorem union_heap (h : Nat) (values : List Node) (before : CtorState)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (known : ArityHeap before) :
    ArityHeap (reached (union h values before)) := by
  have first := readAll_heap h values before semantic costs available known
  unfold union
  apply bind_heap first
  intro edges middle completed
  have current : ArityHeap middle := by simpa only [completed, reached] using first
  exact SourcePruningEnumerationArityOrigins.node_heap edges middle current

private theorem rows_from (p h : Nat) (path : List Int)
    (smaller : ∀ (value : Node) (before : CtorState), SemanticReady before → CostHeap before →
      Available before value → ArityHeap before → ArityHeap (reached (project p h path value before)))
    (index : Int) (edges : List Row) (before : CtorState) (semantic : SemanticReady before)
    (costs : CostHeap before) (resident : Edges before edges) (known : ArityHeap before) :
    ArityHeap (reached (rows (project p h path) index edges before)) := by
  induction edges generalizing before with
  | nil => exact known
  | cons row edges ih =>
      have tail := fun other member => resident other (List.mem_cons_of_mem _ member)
      cases found : select row.children index with
      | none => simpa only [rows, found] using ih before semantic costs tail known
      | some child =>
          have available := semantic.ready.semantic.1.normal.facts.cached.edges row.entry.key row
            (resident row List.mem_cons_self) child (select_member found)
          have first := smaller child before semantic costs available known
          rw [rows, found]
          apply bind_heap first
          intro value middle completed
          have current : ArityHeap middle := by simpa only [completed, reached] using first
          have effects := SourceEqualityProjectionOutcomeMemos.project_effects p h path child before semantic costs available
          have kept : Keeps before middle ∧ SemanticReady middle ∧ CostHeap middle := by
            simpa only [completed, reached] using And.intro effects.1 (And.intro effects.2.1 effects.2.2.1)
          have last := ih middle kept.2.1 kept.2.2
            (fun other member => InternedEdgeResidency.edge_grows before middle kept.1.growth other (tail other member)) current
          simpa only [map_reached] using last

/-- Every actual node projection outcome retains the complete arity heap. -/
theorem project_heap (p h : Nat) (path : List Int) (value : Node) (before : CtorState)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (known : ArityHeap before) :
    ArityHeap (reached (project p h path value before)) := by
  induction p generalizing path value before with
  | zero => exact known
  | succ p ih =>
      cases path with
      | nil => exact known
      | cons index path =>
          have expose (original : Node) (present : Available before original) :
              ArityHeap (reached ((SourceEqualityRequiredWorker.head h original before).bind fun exposed after =>
                project p h (index :: path) exposed after)) := by
            have first := head_heap h original before semantic present known
            apply bind_heap first
            intro exposed middle completed
            have current : ArityHeap middle := by simpa only [completed, reached] using first
            have effects := SourceEqualityProjectionOutcomePrimitives.head_effects h original before semantic costs present
            have kept : Keeps before middle ∧ SemanticReady middle ∧ CostHeap middle := by
              simpa only [completed, reached] using And.intro effects.1 (And.intro effects.2.1 effects.2.2.1)
            exact ih (index :: path) exposed middle kept.2.1 kept.2.2 (effects.2.2.2 exposed middle completed) current
          cases value with
          | empty => exact known
          | reference name => exact known
          | node entry edges depth free =>
              rw [project]
              have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked
                (.node entry edges depth free) available.resident
              have first := rows_from p h path
                (fun child middle sem cost present heap => ih path child middle sem cost present heap)
                index edges before semantic costs resident known
              apply bind_heap first
              intro values middle completed
              have current : ArityHeap middle := by simpa only [completed, reached] using first
              have effects := SourceEqualityProjectionOutcomeMemos.rows_effects p h path index edges before semantic costs resident
              have kept : Keeps before middle ∧ SemanticReady middle ∧ CostHeap middle := by
                simpa only [completed, reached] using And.intro effects.1 (And.intro effects.2.1 effects.2.2.1)
              exact union_heap h values middle kept.2.1 kept.2.2 (effects.2.2.2 values middle completed) current
          | mu entry body depth ordinary => exact expose (.mu entry body depth ordinary) available
          | union entry members depth free => exact expose (.union entry members depth free) available

/-- Ordered actual row projections preserve arity on success and every stopped prefix. -/
theorem rows_heap (p h : Nat) (path : List Int) (index : Int) (edges : List Row) (before : CtorState)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (known : ArityHeap before) :
    ArityHeap (reached (rows (project p h path) index edges before)) :=
  rows_from p h path (fun value current sem cost available heap => project_heap p h path value current sem cost available heap)
    index edges before semantic costs resident known

/-- Every literal forest outcome retains arity without a completed graph premise. -/
theorem forest_heap (p h : Nat) (path : List Int) (values : List Node) (before : CtorState)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (known : ArityHeap before) :
    ArityHeap (reached (forest p h path values before)) := by
  cases path with
  | nil => exact union_heap h values before semantic costs available known
  | cons index path =>
      cases found : select values index with
      | none => simpa only [forest, found, reached] using known
      | some value =>
          simpa only [forest, found] using project_heap p h path value before semantic costs
            (available value (select_member found)) known

end MicroCFTA.SourcePruningEnumerationProjectionArityOutcome
