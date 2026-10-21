import MicroCFTA.SourceCurrentRequiredRawCorridor
import MicroCFTA.SourceCurrentConstrainedCapOpenExposure
import MicroCFTA.SourceCurrentConstrainedCapProjectionGuard

/-!
# Actual projections of raw finite endpoint corridors

Each ordinary step follows its signed child position in every raw row.
Actual open reads and unions retain a finite cap for the returned value.
-/
namespace MicroCFTA.SourceCurrentRawCorridorProjectionCap
open InternedRecordCoherence
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityProjectionGraph SourceEqualityProjectionRead SourceEqualityProjectionUnion
open SourceCurrentRequiredRawCorridor (RawCorridor)
open SourceCurrentConstrainedCap (Cap Edge)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
private def Finite (value : Node) : Prop := ∃ depth, Cap Plain depth value

private theorem uniform (values : List Node) (all : ∀ value ∈ values, Finite value) :
    ∃ depth, ∀ value ∈ values, Cap Plain depth value := by
  induction values with
  | nil => exact ⟨0,by intro value member; cases member⟩
  | cons value values ih =>
    obtain ⟨first,bounded⟩ := all value List.mem_cons_self
    obtain ⟨rest,others⟩ := ih (fun child member => all child (List.mem_cons_of_mem _ member))
    refine ⟨max first rest,?_⟩
    intro child member
    rcases List.mem_cons.mp member with rfl | later
    · exact bounded.mono (Nat.le_max_left _ _)
    · exact (others child later).mono (Nat.le_max_right _ _)

private theorem child_finite {value : Node} (bounded : Finite value) (row : Row)
    (member : row ∈ nodeEdges value) (child : Node) (inside : child ∈ row.children) : Finite child := by
  obtain ⟨depth,bounded⟩ := bounded
  have localRow := SourceCurrentConstrainedCap.node_edge bounded row member
  cases depth with
  | zero => exact ⟨0,.plain 0 (localRow.2 child inside)⟩
  | succ depth => exact ⟨depth,localRow child inside⟩

section Actual
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem readAll_caps (depth : Nat) {values : List Node} {before after : Heap} {rows : List Row}
    (actual : ReadAll values before rows after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (guards : Guards before) (bounded : ∀ value ∈ values, Cap Plain depth value) :
    ∀ row ∈ rows, Edge Plain depth row := by
  induction actual with
  | nil => intro row member; cases member
  | @cons value before rows middle values more after first rest ih =>
    have firstCap : ∀ row ∈ rows, Edge Plain depth row := by
      cases first with
      | done fuel completed => exact (SourceCurrentConstrainedCapOpenExposure.nodeEdges Plain depth fuel value before
          semantic.ready.semantic semantic.ready.covered (available _ List.mem_cons_self)
          (bounded _ List.mem_cons_self) (SourceCurrentConstrainedCapGuardNative.stored Plain before guards) rows middle completed).2
    have effects := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
    have tail := ih effects.2.1 effects.2.2.1
      (fun child member => effects.1.available child (available child (List.mem_cons_of_mem _ member)))
      (SourceCurrentConstrainedCapProjectionGuard.read Plain first semantic costs (available _ List.mem_cons_self) guards)
      (fun child member => bounded child (List.mem_cons_of_mem _ member))
    intro row member
    rcases List.mem_append.mp member with own | later
    · exact firstCap row own
    · exact tail row later

private theorem union_finite {values : List Node} {before after : Heap} {result : Node}
    (actual : Union values before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (guards : Guards before) (bounded : ∀ value ∈ values, Finite value) : Finite result := by
  obtain ⟨depth,caps⟩ := uniform values bounded
  cases actual with
  | node rows built =>
    have boundedRows := readAll_caps depth rows semantic costs available guards caps
    have effects := SourceEqualityProjectionCosts.readAll_effects rows semantic costs available
    have facts := effects.2.1.ready.semantic.1.normal.facts
    refine ⟨depth, ?_⟩
    simpa only [built] using (SourceCurrentConstrainedCap.makeNode Plain depth _ _
      facts.coherent facts.linked effects.2.2.2 boundedRows)

private def NodePost (path : List Int) (value : Node) (before : Heap) (result : Node) : Prop :=
  SemanticReady before → CostHeap before → Available before value → Guards before → RawCorridor path value → Finite result
private def RowsPost (path : List Int) (index : Int) (rows : List Row) (before after : Heap) (results : List Node) : Prop :=
  SemanticReady before → CostHeap before → Edges before rows → Guards before →
    (∀ row ∈ rows, ∀ child, select row.children index = some child → RawCorridor path child) →
    Guards after ∧ ∀ value ∈ results, Finite value

private theorem project_corridor {path value before result after} (actual : Project path value before result after) :
    NodePost path value before result := by
  have rootCase : ∀ {value : Node} {state}, NodePost [] value state value := by
    intro value state _ _ _ _ safe
    cases safe with | full _ _ bounded => exact bounded
  have emptyCase : ∀ {index path state}, NodePost (index::path) (.empty : Node) state .empty := by
    intro index path state _ _ _ _ _; exact ⟨0,.plain 0 .empty⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows path index edges before values middle → Union values middle result after →
      RowsPost path index edges before middle values → NodePost (index::path) (.node entry edges depth free) before result := by
    intro path index edges before values middle result after entry depth free rows combined ih semantic costs available guards safe
    have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have selected : ∀ row ∈ edges, ∀ child, select row.children index = some child → RawCorridor path child := by
      cases safe with
      | node _ _ _ _ _ _ children => exact children
      | full _ _ bounded => exact fun row member child found => .full _ _ (child_finite bounded row member child (select_member found))
    have children := ih semantic costs resident guards selected
    have effects := SourceEqualityProjectionCosts.rows_effects rows semantic costs resident
    exact union_finite combined effects.2.1 effects.2.2.1 effects.2.2.2 children.1 children.2
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (index::path) exposed middle result after → NodePost (index::path) exposed middle result →
      NodePost (index::path) original before result := by
    intro original before exposed middle path index result after recursive head _ ih semantic costs available guards safe
    have finite : Finite original := by
      cases safe with
      | full _ _ bounded => exact bounded
      | node => cases recursive
    obtain ⟨depth,bounded⟩ := finite
    have exposedCap := SourceCurrentConstrainedCapOpenExposure.head Plain depth head semantic costs available bounded
      (SourceCurrentConstrainedCapGuardNative.stored Plain before guards)
    have effects := SourceEqualityProjectionCosts.head_effects head semantic costs available
    exact ih effects.2.1 effects.2.2.1 effects.2.2.2
      (SourceCurrentConstrainedCapProjectionGuard.head Plain head semantic costs available guards) (.full _ _ ⟨depth,exposedCap.2⟩)
  have nilCase : ∀ {path index state}, RowsPost path index ([] : List Row) state state [] := by
    intro path index state _ _ _ guards _; exact ⟨guards,by intro value member; cases member⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows path index edges before results after → RowsPost path index edges before after results →
      RowsPost path index (edge::edges) before after results := by
    intro edge path index edges before results after _ _ ih semantic costs resident guards safe
    exact ih semantic costs (fun row member => resident row (List.mem_cons_of_mem _ member)) guards
      (fun row member child found => safe row (List.mem_cons_of_mem _ member) child found)
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project path child before result middle →
      ProjectRows path index edges middle results after → NodePost path child before result →
      RowsPost path index edges middle after results → RowsPost path index (edge::edges) before after (result::results) := by
    intro edge index child path before result middle edges results after found first rest firstIH restIH semantic costs resident guards safe
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self) child (select_member found)
    have bounded := firstIH semantic costs available guards (safe edge List.mem_cons_self child found)
    have effects := SourceEqualityProjectionCosts.project_effects first semantic costs available
    have tail := restIH effects.2.1 effects.2.2.1
      (fun row member => edge_grows before middle effects.1.growth row (resident row (List.mem_cons_of_mem _ member)))
      (SourceCurrentConstrainedCapProjectionGuard.node Plain first semantic costs available guards)
      (fun row member child found => safe row (List.mem_cons_of_mem _ member) child found)
    refine ⟨tail.1,?_⟩
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact bounded
    · exact tail.2 value later
  exact Project.rec (motive_1 := fun path value before result _ _ => NodePost path value before result)
    (motive_2 := fun path index rows before results after _ => RowsPost path index rows before after results)
    rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase actual

/-- The actual signed projection derives a finite cap from the same raw corridor. -/
theorem project {path : List Int} {value result : Node} {before after : Heap}
    (actual : Project path value before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (guards : Guards before) (corridor : RawCorridor path value) :
    ∃ depth, Cap Plain depth result :=
  project_corridor actual semantic costs available guards corridor

/-- A proper forest projection needs a corridor only at its actual selected root. -/
theorem forest {index : Int} {path : List Int} {values : List Node} {result : Node} {before after : Heap}
    (actual : Forest (index::path) values before result after) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (guards : Guards before)
    (corridor : ∀ value, select values index = some value → RawCorridor path value) :
    ∃ depth, Cap Plain depth result := by
  cases actual with
  | missing => exact ⟨0,.plain 0 .empty⟩
  | selected found body => exact project body semantic costs (available _ (select_member found)) guards (corridor _ found)
end Actual
end MicroCFTA.SourceCurrentRawCorridorProjectionCap
