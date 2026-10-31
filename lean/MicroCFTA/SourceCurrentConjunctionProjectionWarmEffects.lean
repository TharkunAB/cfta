import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceEqualityProjectionWorkerSound
import MicroCFTA.SourceEqualityProjectionWorkerPhysical
import MicroCFTA.SourceCurrentConjunctionRowsWorker

set_option autoImplicit false
open scoped Classical

/-! Warm effects at every actual projection endpoint. -/
namespace MicroCFTA.SourceCurrentConjunctionProjectionWarmEffects
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityRequiredWorker (Result work head)
open SourceEqualityProjectionWorker
open SourceEqualityProjectionGraph (select select_member)
variable {Symbol Guard A B : Type}
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Heap" => SourceEqualityAnnotationHeap.Heap

private def reached (actual : Result Symbol Guard A) : State Symbol Guard :=
  match actual with
  | .done _ after => after
  | .pending _ after => after
  | .unresolved _ after => after
  | .exhausted _ after => after

private structure Safe (annotation : Guard → Prop) (before after : State Symbol Guard) : Prop where
  keeps : Keeps before after
  semantic : SemanticReady after
  costs : CostHeap after
  fields : Heap annotation after

private theorem pure_safe (annotation : Guard → Prop) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (fields : Heap annotation before) :
    Safe annotation before before := ⟨pure_keeps _ semantic.ready, semantic, costs, fields⟩

private theorem Safe.trans {annotation : Guard → Prop} {before middle after : State Symbol Guard}
    (first : Safe annotation before middle) (last : Safe annotation middle after) : Safe annotation before after :=
  ⟨first.keeps.trans last.keeps, last.semantic, last.costs, last.fields⟩

private theorem bind_safe {annotation : Guard → Prop} {before : State Symbol Guard}
    {actual : Result Symbol Guard A} {next : A → State Symbol Guard → Result Symbol Guard B}
    (first : Safe annotation before (reached actual))
    (step : ∀ value after, actual = .done value after → Safe annotation after (reached (next value after))) :
    Safe annotation before (reached (actual.bind next)) := by
  cases actual with
  | done value after => exact first.trans (step value after rfl)
  | pending key after => exact first
  | unresolved name after => exact first
  | exhausted limit after => exact first

private theorem map_state (actual : Result Symbol Guard A) (f : A → B) :
    reached (actual.bind fun value after => .done (f value) after) = reached actual := by
  cases actual <;> rfl

private theorem read_safe (annotation : Guard → Prop) (h : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (fields : Heap annotation before) (available : Available before value) :
    Safe annotation before (MergedFreshOrdinaryExposure.nodeEdges h value before).state := by
  have checked := SourceEqualityExposureCosts.nodeEdges_verified h value before semantic costs available
  exact ⟨checked.keeps, checked.semantic, checked.costs,
    SourceCurrentOpenExposureFields.nodeEdges_heap annotation h value before semantic fields available⟩

private theorem readAll_safe (annotation : Guard → Prop) (h : Nat) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (fields : Heap annotation before) (available : Values before values) :
    Safe annotation before (reached (readAll h values before)) := by
  induction values generalizing before with
  | nil => exact pure_safe annotation before semantic costs fields
  | cons value values ih =>
    have first := read_safe annotation h value before semantic costs fields (available _ List.mem_cons_self)
    cases read : MergedFreshOrdinaryExposure.nodeEdges h value before with
    | done edges middle =>
      rw [read] at first
      have later := ih middle first.semantic first.costs first.fields
        (fun child member => first.keeps.available child (available child (List.mem_cons_of_mem _ member)))
      simpa only [readAll, read, map_state] using first.trans later
    | pending key after =>
      simpa only [readAll, read, reached, MergedSourceExposure.Result.state] using first
    | unresolved name after =>
      simpa only [readAll, read, reached, MergedSourceExposure.Result.state] using first
    | exhausted after =>
      simpa only [readAll, read, reached, MergedSourceExposure.Result.state] using first

private theorem node_safe (annotation : Guard → Prop) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (fields : Heap annotation before) (resident : Edges before edges) :
    Safe annotation before (reached (work (makeNode edges) before)) := by
  have checked := SourceCurrentRequiredHeapEffects.node_constructor annotation edges before semantic costs fields resident
  exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩

private theorem union_safe (annotation : Guard → Prop) (h : Nat) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (fields : Heap annotation before) (available : Values before values) :
    Safe annotation before (reached (union h values before)) := by
  have first := readAll_safe annotation h values before semantic costs fields available
  apply bind_safe first
  intro edges after completed
  have kept : Safe annotation before after := by simpa only [completed, reached] using first
  have graph := SourceEqualityProjectionWorkerSound.readAll_graph h values before edges after completed
  have read := SourceEqualityProjectionCosts.readAll_effects graph semantic costs available
  exact node_safe annotation edges after kept.semantic kept.costs kept.fields read.2.2.2

private theorem head_safe (annotation : Guard → Prop) (h : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (fields : Heap annotation before) (available : Available before value) :
    Safe annotation before (reached (head h value before)) := by
  have first := read_safe annotation h value before semantic costs fields available
  cases read : MergedFreshOrdinaryExposure.nodeEdges h value before with
  | done edges after =>
    rw [read] at first
    have observed := SourceEqualityProjectionCosts.read_effects (.done h read) semantic costs available
    simpa only [head, read] using first.trans
      (node_safe annotation edges after first.semantic first.costs first.fields observed.2.2.2)
  | pending key after => simpa only [head, read, reached, MergedSourceExposure.Result.state] using first
  | unresolved name after => simpa only [head, read, reached, MergedSourceExposure.Result.state] using first
  | exhausted after => simpa only [head, read, reached, MergedSourceExposure.Result.state] using first

private theorem rows_safe (annotation : Guard → Prop) (p h : Nat) (path : List Int)
    (smaller : ∀ (value : Value Symbol Guard) (before : State Symbol Guard), SemanticReady before → CostHeap before → Heap annotation before →
      Available before value → Safe annotation before (reached (project p h path value before)))
    (index : Int) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (fields : Heap annotation before)
    (resident : Edges before edges) :
    Safe annotation before (reached (rows (project p h path) index edges before)) := by
  induction edges generalizing before with
  | nil => exact pure_safe annotation before semantic costs fields
  | cons edge edges ih =>
    have tail := fun row member => resident row (List.mem_cons_of_mem _ member)
    cases found : select edge.children index with
    | none => simpa only [rows, found] using ih before semantic costs fields tail
    | some child =>
      rw [rows, found]
      have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
        (resident edge List.mem_cons_self) child (select_member found)
      have first := smaller child before semantic costs fields available
      apply bind_safe first
      intro value middle completed
      have kept : Safe annotation before middle := by simpa only [completed, reached] using first
      have later := ih middle kept.semantic kept.costs kept.fields
        (fun row member => InternedEdgeResidency.edge_grows before middle kept.keeps.growth row (tail row member))
      simpa only [map_state] using later

private theorem project_safe (annotation : Guard → Prop) (p h : Nat) (path : List Int)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (fields : Heap annotation before) (available : Available before value) :
    Safe annotation before (reached (project p h path value before)) := by
  induction p generalizing path value before with
  | zero => exact pure_safe annotation before semantic costs fields
  | succ p ih =>
    cases path with
    | nil => exact pure_safe annotation before semantic costs fields
    | cons index path =>
      have expose (query : Value Symbol Guard) (present : Available before query) :
          Safe annotation before (reached ((head h query before).bind fun exposed after => project p h (index :: path) exposed after)) := by
        have first := head_safe annotation h query before semantic costs fields present
        apply bind_safe first
        intro exposed after completed
        have kept : Safe annotation before after := by simpa only [completed, reached] using first
        have graph := SourceEqualityRequiredWorkerSound.head_graph h query before exposed after completed
        exact ih (index :: path) exposed after kept.semantic kept.costs kept.fields
          (SourceEqualityProjectionCosts.head_effects graph semantic costs present).2.2.2
      cases value with
      | empty => exact pure_safe annotation before semantic costs fields
      | reference name => exact pure_safe annotation before semantic costs fields
      | node entry edges depth free =>
        rw [project]
        have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked
          (.node entry edges depth free) available.resident
        have first := rows_safe annotation p h path
          (fun child after sem cost annotations present => ih path child after sem cost annotations present)
          index edges before semantic costs fields resident
        apply bind_safe first
        intro values after completed
        have kept : Safe annotation before after := by simpa only [completed, reached] using first
        have graph := SourceEqualityProjectionWorkerSound.rows_graph (project p h path) path
          (fun child heap result returned done => SourceEqualityProjectionWorkerSound.project_graph p h path child heap result returned done)
          index edges before values after completed
        exact union_safe annotation h values after kept.semantic kept.costs kept.fields
          (SourceEqualityProjectionCosts.rows_effects graph semantic costs resident).2.2.2
      | mu entry body depth free => exact expose (.mu entry body depth free) available
      | union entry members depth free => exact expose (.union entry members depth free) available

/-- Every actual forest outcome retains full current physical readiness. -/
theorem forest_effects {Formula : Type} (p h : Nat) (path : List Int)
    (values : List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))
    (before : SourceCurrentConjunctionRowsAllocation.State Symbol Formula)
    (ready : SourceCurrentConjunctionRowsAllocation.Ready before) (available : Values before.heap values) :
    let actual := forest p h path values before.heap
    SourceCurrentConjunctionRowsAllocation.Effects before ⟨reached actual, before.equality⟩ := by
  let annotation := SourceCurrentConjunctionEquality.FieldAvailable (Formula := Formula) before.equality
  have safe : Safe annotation before.heap (reached (forest p h path values before.heap)) := by
    cases path with
    | nil => exact union_safe annotation h values before.heap ready.semantic ready.costs ready.fields available
    | cons index path =>
      cases found : select values index with
      | none => simpa only [forest, found, reached] using pure_safe annotation before.heap ready.semantic ready.costs ready.fields
      | some value =>
        simpa only [forest, found] using project_safe annotation p h path value before.heap
          ready.semantic ready.costs ready.fields (available value (select_member found))
  exact ⟨safe.keeps, ⟨safe.semantic, safe.costs, ready.valid, safe.fields⟩,
    SourceEqualityConstraintMemoAllocation.grows_refl _⟩

end MicroCFTA.SourceCurrentConjunctionProjectionWarmEffects
