import MicroCFTA.SourceCurrentConjunctionProjectionWarmEffects
import MicroCFTA.SourceCurrentConjunctionExposureProbes

set_option autoImplicit false
open scoped Classical

/-! Probe and readiness preservation at actual conjunction endpoints. -/
namespace MicroCFTA.SourceCurrentConjunctionProjectionProbes
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityRequiredWorker (Result work head)
open SourceEqualityProjectionWorker
open SourceEqualityProjectionGraph (select select_member)
variable {Symbol Guard A B : Type}
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Heap" => InternedFreshOrdinaryProbeHeap.Heap

private def reached (actual : Result Symbol Guard A) : State Symbol Guard :=
  match actual with
  | .done _ after => after
  | .pending _ after => after
  | .unresolved _ after => after
  | .exhausted _ after => after

private structure Safe (before after : State Symbol Guard) : Prop where
  keeps : Keeps before after
  semantic : SemanticReady after
  costs : CostHeap after
  probes : Heap after

private theorem pure_safe (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (probes : Heap before) :
    Safe before before := ⟨pure_keeps _ semantic.ready, semantic, costs, probes⟩

private theorem Safe.trans {before middle after : State Symbol Guard}
    (first : Safe before middle) (last : Safe middle after) : Safe before after :=
  ⟨first.keeps.trans last.keeps, last.semantic, last.costs, last.probes⟩

private theorem bind_safe {before : State Symbol Guard}
    {actual : Result Symbol Guard A} {next : A → State Symbol Guard → Result Symbol Guard B}
    (first : Safe before (reached actual))
    (step : ∀ value after, actual = .done value after → Safe after (reached (next value after))) :
    Safe before (reached (actual.bind next)) := by
  cases actual with
  | done value after => exact first.trans (step value after rfl)
  | pending key after => exact first
  | unresolved name after => exact first
  | exhausted limit after => exact first

private theorem map_state (actual : Result Symbol Guard A) (f : A → B) :
    reached (actual.bind fun value after => .done (f value) after) = reached actual := by
  cases actual <;> rfl

private theorem read_safe (h : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (probes : Heap before) (available : Available before value) :
    Safe before (MergedFreshOrdinaryExposure.nodeEdges h value before).state := by
  have checked := SourceEqualityExposureCosts.nodeEdges_verified h value before semantic costs available
  exact ⟨checked.keeps, checked.semantic, checked.costs,
    SourceCurrentConjunctionExposureProbes.nodeEdges_heap h value before semantic probes available⟩

private theorem readAll_safe (h : Nat) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (probes : Heap before) (available : Values before values) :
    Safe before (reached (readAll h values before)) := by
  induction values generalizing before with
  | nil => exact pure_safe before semantic costs probes
  | cons value values ih =>
    have first := read_safe h value before semantic costs probes (available _ List.mem_cons_self)
    cases read : MergedFreshOrdinaryExposure.nodeEdges h value before with
    | done edges middle =>
      rw [read] at first
      have later := ih middle first.semantic first.costs first.probes
        (fun child member => first.keeps.available child (available child (List.mem_cons_of_mem _ member)))
      simpa only [readAll, read, map_state] using first.trans later
    | pending key after =>
      simpa only [readAll, read, reached, MergedSourceExposure.Result.state] using first
    | unresolved name after =>
      simpa only [readAll, read, reached, MergedSourceExposure.Result.state] using first
    | exhausted after =>
      simpa only [readAll, read, reached, MergedSourceExposure.Result.state] using first

private theorem node_safe (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (probes : Heap before) (resident : Edges before edges) :
    Safe before (reached (work (makeNode edges) before)) := by
  have checked := SourceEqualityOpenOrdinaryHead.node edges before semantic resident
  exact ⟨checked.1, checked.2.1,
    InternedFreshOrdinaryCostHeap.preserve before _ costs (InternedShallowHeap.makeNode_noNewMu edges before),
    InternedFreshOrdinaryProbeHeap.node edges before probes⟩

private theorem union_safe (h : Nat) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (probes : Heap before) (available : Values before values) :
    Safe before (reached (union h values before)) := by
  have first := readAll_safe h values before semantic costs probes available
  apply bind_safe first
  intro edges after completed
  have kept : Safe before after := by simpa only [completed, reached] using first
  have graph := SourceEqualityProjectionWorkerSound.readAll_graph h values before edges after completed
  have read := SourceEqualityProjectionCosts.readAll_effects graph semantic costs available
  exact node_safe edges after kept.semantic kept.costs kept.probes read.2.2.2

private theorem head_safe (h : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (probes : Heap before) (available : Available before value) :
    Safe before (reached (head h value before)) := by
  have first := read_safe h value before semantic costs probes available
  cases read : MergedFreshOrdinaryExposure.nodeEdges h value before with
  | done edges after =>
    rw [read] at first
    have observed := SourceEqualityProjectionCosts.read_effects (.done h read) semantic costs available
    simpa only [head, read] using first.trans
      (node_safe edges after first.semantic first.costs first.probes observed.2.2.2)
  | pending key after => simpa only [head, read, reached, MergedSourceExposure.Result.state] using first
  | unresolved name after => simpa only [head, read, reached, MergedSourceExposure.Result.state] using first
  | exhausted after => simpa only [head, read, reached, MergedSourceExposure.Result.state] using first

private theorem rows_safe (p h : Nat) (path : List Int)
    (smaller : ∀ (value : Value Symbol Guard) (before : State Symbol Guard), SemanticReady before → CostHeap before → Heap before →
      Available before value → Safe before (reached (project p h path value before)))
    (index : Int) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (probes : Heap before)
    (resident : Edges before edges) :
    Safe before (reached (rows (project p h path) index edges before)) := by
  induction edges generalizing before with
  | nil => exact pure_safe before semantic costs probes
  | cons edge edges ih =>
    have tail := fun row member => resident row (List.mem_cons_of_mem _ member)
    cases found : select edge.children index with
    | none => simpa only [rows, found] using ih before semantic costs probes tail
    | some child =>
      rw [rows, found]
      have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
        (resident edge List.mem_cons_self) child (select_member found)
      have first := smaller child before semantic costs probes available
      apply bind_safe first
      intro value middle completed
      have kept : Safe before middle := by simpa only [completed, reached] using first
      have later := ih middle kept.semantic kept.costs kept.probes
        (fun row member => InternedEdgeResidency.edge_grows before middle kept.keeps.growth row (tail row member))
      simpa only [map_state] using later

private theorem project_safe (p h : Nat) (path : List Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (probes : Heap before) (available : Available before value) :
    Safe before (reached (project p h path value before)) := by
  induction p generalizing path value before with
  | zero => exact pure_safe before semantic costs probes
  | succ p ih =>
    cases path with
    | nil => exact pure_safe before semantic costs probes
    | cons index path =>
      have expose (query : Value Symbol Guard) (present : Available before query) :
          Safe before (reached ((head h query before).bind fun exposed after => project p h (index :: path) exposed after)) := by
        have first := head_safe h query before semantic costs probes present
        apply bind_safe first
        intro exposed after completed
        have kept : Safe before after := by simpa only [completed, reached] using first
        have graph := SourceEqualityRequiredWorkerSound.head_graph h query before exposed after completed
        exact ih (index :: path) exposed after kept.semantic kept.costs kept.probes
          (SourceEqualityProjectionCosts.head_effects graph semantic costs present).2.2.2
      cases value with
      | empty => exact pure_safe before semantic costs probes
      | reference name => exact pure_safe before semantic costs probes
      | node entry edges depth free =>
        rw [project]
        have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked
          (.node entry edges depth free) available.resident
        have first := rows_safe p h path
          (fun child after sem cost childProbes present => ih path child after sem cost childProbes present)
          index edges before semantic costs probes resident
        apply bind_safe first
        intro values after completed
        have kept : Safe before after := by simpa only [completed, reached] using first
        have graph := SourceEqualityProjectionWorkerSound.rows_graph (project p h path) path
          (fun child heap result returned done => SourceEqualityProjectionWorkerSound.project_graph p h path child heap result returned done)
          index edges before values after completed
        exact union_safe h values after kept.semantic kept.costs kept.probes
          (SourceEqualityProjectionCosts.rows_effects graph semantic costs resident).2.2.2
      | mu entry body depth free => exact expose (.mu entry body depth free) available
      | union entry members depth free => exact expose (.union entry members depth free) available

/-- Every actual project outcome retains clean probes for completed Mu records. -/
theorem project_heap (p h : Nat) (path : List Int) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (probes : Heap before) (available : Available before value) :
    Heap (reached (project p h path value before)) :=
  (project_safe p h path value before semantic costs probes available).probes

/-- Every actual forest outcome retains clean probes at its literal returned heap. -/
theorem forest_heap (p h : Nat) (path : List Int) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (probes : Heap before) (available : Values before values) :
    Heap (reached (forest p h path values before)) := by
  have safe : Safe before (reached (forest p h path values before)) := by
    cases path with
    | nil => exact union_safe h values before semantic costs probes available
    | cons index path =>
      cases found : select values index with
      | none => simpa only [forest, found, reached] using pure_safe before semantic costs probes
      | some value =>
        simpa only [forest, found] using project_safe p h path value before
          semantic costs probes (available value (select_member found))
  exact safe.probes

end MicroCFTA.SourceCurrentConjunctionProjectionProbes
