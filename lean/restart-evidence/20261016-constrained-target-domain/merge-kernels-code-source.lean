import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite
import MicroCFTA.SourceCurrentMemoMergeEffects
import MicroCFTA.SourceMergedGroups

/-!
# Local domain certificates for current memo-aware merge bodies

Actual recursive requests require finite ordinary inputs. Their continuations
use the returned domain certificate. Constructor work retains its exact
physical effect. Selection removes original values only. The domain excludes
the recursive-boundary branch. These local certificates do not assert a
completed merge call or substitute an uncached recursive worker.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A returned value retains its complete physical record and ordinary domain. -/
def ValuePost (heap : State Symbol Guard) (value : Value Symbol Guard) : Prop := Available heap value ∧ DNode value

/-- A returned row retains its complete physical record and ordered domain children. -/
def EdgePost (heap : State Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop := EdgeResident heap edge ∧ DEdge edge

/-- Local source instructions retain actual primitive effects and domain recursive requests. -/
def Certified (clear : Guard → Bool) (code : Code Symbol Guard Output) (before : State Symbol Guard)
    (post : State Symbol Guard → Output → Prop) : Prop :=
  match code with
  | .pure value => post before value
  | .work job => Effect before (run job before).2 ∧ post (run job before).2 (run job before).1
  | .select inputs => Values before inputs ∧ MergedColdReaderClosedInputs.ClosedValues inputs ∧ ∀ fuel values after,
      SourceMergedSelection.select clear fuel inputs before = .done values after → Effect before after → post after values
  | .request input => ValuePost before input ∧ ∀ output after, Effect before after → ValuePost after output → post after output
  | .bind first next => ∃ intermediate : State Symbol Guard → _ → Prop,
      Certified clear first before intermediate ∧ ∀ value middle,
        Effect before middle → intermediate middle value → Certified clear (next value) middle post

/-- Sequential source code checks each suffix at its actual returned heap. -/
theorem bind_certified (clear : Guard → Bool) (first : Code Symbol Guard First) (next : First → Code Symbol Guard Output)
    (before : State Symbol Guard) (intermediate : State Symbol Guard → First → Prop)
    (post : State Symbol Guard → Output → Prop) (checked : Certified clear first before intermediate)
    (later : ∀ value middle, Effect before middle → intermediate middle value → Certified clear (next value) middle post) :
    Certified clear (.bind first next) before post := ⟨intermediate, checked, later⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Actual heap growth preserves complete returned value records and their domain. -/
theorem value_grows {before after : State Symbol Guard} (effect : Effect before after)
    (value : Value Symbol Guard) (post : ValuePost before value) : ValuePost after value :=
  ⟨effect.keeps.available value post.1, post.2⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Actual heap growth preserves complete returned rows and their domain. -/
theorem edge_grows {before after : State Symbol Guard} (effect : Effect before after)
    (edge : EdgeValue Symbol Guard) (post : EdgePost before edge) : EdgePost after edge :=
  ⟨InternedEdgeResidency.edge_grows before after effect.keeps.growth edge post.1, post.2⟩

/-- Ordered maps retain each actual result through later physical effects. -/
theorem map_certified (clear : Guard → Bool) (call : Request → Code Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop) (post : State Symbol Guard → Output → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (postGrows : ∀ before after, Effect before after → ∀ value, post before value → post after value)
    (requests : List Request)
    (checked : ∀ request ∈ requests, ∀ before, SemanticReady before → CostHeap before → pre before request →
      Certified clear (call request) before post)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : ∀ request ∈ requests, pre before request) :
    Certified clear (map call requests) before (fun after values => ∀ value ∈ values, post after value) := by
  induction requests generalizing before with
  | nil => exact by simp [map, Certified]
  | cons first rest ih =>
      apply bind_certified clear _ _ before post _
        (checked first List.mem_cons_self before semantic costs (inputs first List.mem_cons_self))
      intro value middle effect valid
      apply bind_certified clear _ _ middle _ _
        (ih (fun request member => checked request (List.mem_cons_of_mem _ member)) middle effect.semantic effect.costs
          (fun request member => preGrows before middle effect request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after later ready output member
      rcases List.mem_cons.mp member with same | member
      · subst output
        exact postGrows middle after later value valid
      · exact ready output member

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem values_closed (before : State Symbol Guard) (semantic : SemanticReady before)
    (values : List (Value Symbol Guard)) (valid : ∀ value ∈ values, ValuePost before value) :
    MergedColdReaderClosedInputs.ClosedValues values :=
  fun value member => SourceCurrentAllocatedFiniteOrdinaryFinite.closed before
    semantic.ready.semantic.1.normal.facts.coherent value (valid value member).1 (valid value member).2

private theorem edge_certified (clear : Guard → Bool) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (valid : ∀ value ∈ values, ValuePost before value) :
    Certified clear (.work (makeEdge symbol guard values)) before EdgePost := by
  have available : Values before values := fun value member => (valid value member).1
  have checked := SourceCurrentMemoMergeEffects.edge_certified clear symbol guard values before semantic costs
    available (values_closed before semantic values valid)
  refine ⟨checked.1, checked.2.1, ?_⟩
  exact SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge symbol guard values before
    semantic.ready.semantic.1.normal.facts.coherent semantic.ready.semantic.1.normal.facts.cached available
    (.of_members values (fun value member => (valid value member).2))

private theorem node_certified (clear : Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (valid : ∀ edge ∈ edges, EdgePost before edge) : Certified clear (.work (makeNode edges)) before ValuePost := by
  have facts := semantic.ready.semantic.1.normal.facts
  have resident : Edges before edges := fun edge member => (valid edge member).1
  have closed : MergedColdReaderClosedInputs.ClosedEdges edges := fun edge member child included =>
    SourceCurrentAllocatedFiniteOrdinaryFinite.closed before facts.coherent child
      (facts.cached.edges edge.entry.key edge (resident edge member) child included) ((valid edge member).2.member child included)
  have checked := SourceCurrentMemoMergeEffects.node_certified clear edges before semantic costs resident closed
  exact ⟨checked.1, checked.2.1, SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode edges before
    facts.coherent facts.linked resident (.of_members edges (fun edge member => (valid edge member).2))⟩

private theorem request_certified (clear : Guard → Bool) (value : Value Symbol Guard) (before : State Symbol Guard)
    (valid : ValuePost before value) : Certified clear (.request value) before ValuePost :=
  ⟨valid, fun _ _ _ returned => returned⟩

private theorem retained_certified (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (valid : ∀ value ∈ inputs, ValuePost before value) : Certified clear (retainedColumn inputs) before ValuePost := by
  have branches (values : List (Value Symbol Guard)) (valid : ∀ value ∈ values, ValuePost before value) :
      Certified clear (if values.any MergedOrdinaryHeight.recursiveBoundary then .work (makeUnion values)
        else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) before ValuePost := by
    have boundary : values.any MergedOrdinaryHeight.recursiveBoundary = false := List.any_eq_false.mpr (by
      intro value member
      have domain := (valid value member).2
      cases domain <;> simp [MergedOrdinaryHeight.recursiveBoundary])
    simp only [boundary, Bool.false_eq_true, ite_false]
    have resident : ∀ edge ∈ values.flatMap InternedEdgeResidency.nodeEdges, EdgePost before edge := by
      intro edge member
      obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
      exact ⟨resident_edges before semantic.ready.semantic.1.normal.facts.linked value (valid value present).1.resident edge included,
        (valid value present).2.nodeEdges.member edge included⟩
    exact bind_certified clear _ _ before ValuePost ValuePost
      (node_certified clear _ before semantic costs resident)
      (fun value middle _ post => request_certified clear value middle post)
  cases inputs with
  | nil => exact branches [] valid
  | cons first rest =>
      cases rest with
      | nil => exact valid first List.mem_cons_self
      | cons second rest => exact branches (first :: second :: rest) valid

private theorem column_certified (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (_costs : CostHeap before)
    (valid : ∀ value ∈ inputs, ValuePost before value) : Certified clear (column inputs) before ValuePost := by
  apply bind_certified clear _ _ before (fun heap values => ∀ value ∈ values, ValuePost heap value) _
  · refine ⟨(fun value member => (valid value member).1), values_closed before semantic inputs valid, ?_⟩
    intro fuel values after done effect value member
    obtain ⟨retained, final, filtered, returned⟩ := (SourceMergedComparisonEffects.bind_done _ _ values after).mp done
    have parts := MergedSourceComparison.Result.done.inj returned
    cases parts.1
    cases parts.2
    have original := (SourceMergedSelection.retain_members clear fuel (inputs.filter MergedPhysicalGroupColumns.closedMu)
      inputs before retained after filtered).1 value (distinctNodes_member _ _ member)
    exact value_grows effect value (valid value original)
  · intro values middle effect post
    exact retained_certified clear values middle effect.semantic effect.costs post

private theorem small_certified (clear : Guard → Bool) (edge : EdgeValue Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (valid : EdgePost before edge) : Certified clear (small edge) before EdgePost := by
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge valid.1
  apply bind_certified clear _ _ before (fun heap values => ∀ value ∈ values, ValuePost heap value) _
    (map_certified clear Code.request ValuePost ValuePost
      (fun _ _ effect value ready => value_grows effect value ready)
      (fun _ _ effect value ready => value_grows effect value ready) edge.children
      (fun value _ heap _ _ ready => request_certified clear value heap ready) before semantic costs
      (fun value member => ⟨available value member, valid.2.member value member⟩))
  intro values middle effect post
  exact edge_certified clear edge.entry.key.symbol edge.entry.key.constraint values middle effect.semantic effect.costs post

private theorem large_certified (clear : Guard → Bool) (top : Guard)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (valid : ∀ edge ∈ first :: rest, EdgePost before edge) : Certified clear (large top first rest) before EdgePost := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  apply bind_certified clear _ _ before (fun heap values => ∀ value ∈ values, ValuePost heap value) _
    (map_certified clear column (fun heap values => ∀ value ∈ values, ValuePost heap value) ValuePost
      (fun _ _ effect _ post value member => value_grows effect value (post value member))
      (fun _ _ effect value post => value_grows effect value post) columns
      (fun values _ heap ready costs post => column_certified clear values heap ready costs post)
      before semantic costs (by
        intro values member value included
        obtain ⟨edge, present, inner⟩ := original values member value included
        exact ⟨semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (valid edge present).1 value inner,
          (valid edge present).2.member value inner⟩))
  intro values middle effect post
  exact edge_certified clear first.entry.key.symbol top values middle effect.semantic effect.costs post

private theorem group_certified (clear : Guard → Bool) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (valid : ∀ edge ∈ edges, EdgePost before edge) :
    Certified clear (group top edges) before (fun heap rows => ∀ edge ∈ rows, EdgePost heap edge) := by
  unfold group
  split
  · exact map_certified clear small EdgePost EdgePost
      (fun _ _ effect edge post => edge_grows effect edge post) (fun _ _ effect edge post => edge_grows effect edge post)
      edges (fun edge _ heap semantic costs post => small_certified clear edge heap semantic costs post)
      before semantic costs valid
  · cases edges with
    | nil => simp_all
    | cons first rest =>
        apply bind_certified clear _ _ before EdgePost _ (large_certified clear top first rest before semantic costs valid)
        intro edge middle _ post value member
        exact (List.mem_singleton.mp member) ▸ post

/-- Actual source grouping and raw node construction preserve the ordinary domain. -/
theorem root_certified (clear : Guard → Bool) (top : Guard) (groups : List (List (EdgeValue Symbol Guard)))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (valid : ∀ group ∈ groups, ∀ edge ∈ group, EdgePost before edge) :
    Certified clear (root top groups) before ValuePost := by
  apply bind_certified clear _ _ before (fun heap rows => ∀ row ∈ rows, ∀ edge ∈ row, EdgePost heap edge) _
    (map_certified clear (group top) (fun heap edges => ∀ edge ∈ edges, EdgePost heap edge)
      (fun heap rows => ∀ edge ∈ rows, EdgePost heap edge)
      (fun _ _ effect _ post edge member => edge_grows effect edge (post edge member))
      (fun _ _ effect _ post edge member => edge_grows effect edge (post edge member)) groups
      (fun edges _ heap semantic costs post => group_certified clear top edges heap semantic costs post)
      before semantic costs valid)
  intro rows middle effect post
  apply node_certified clear rows.flatten middle effect.semantic effect.costs
  intro edge member
  obtain ⟨row, present, included⟩ := List.mem_flatten.mp member
  exact post row present edge included

/-- Every reached finite ordinary body derives its domain-producing local request certificates. -/
theorem body_certified (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before input) (domain : DNode input) : Certified clear (body top input) before ValuePost := by
  cases domain with
  | empty => exact ⟨available, .empty⟩
  | @ordinary edges entry depth free rows =>
      by_cases closed : free = []
      · simp only [body, closed, ite_true]
        have facts := semantic.ready.semantic.1.normal.facts
        have resident := resident_edges before facts.linked _ available.resident
        have grouping := MergedSourceGrouping.groups_correct edges
        apply root_certified clear top _ before semantic costs
        intro group member edge included
        have original := grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
        exact ⟨resident edge original, rows.member edge original⟩
      · simp only [body, closed, ite_false, Certified]
        exact ⟨available, .ordinary rows⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeCode
