import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDomain
import MicroCFTA.SourceEqualityOpenOrdinaryHead
import MicroCFTA.SourceEqualityRequiredExecution

/-!
# Finite ordinary structure through actual required-path graphs

Selected children retain their original positions and do not grow in
height. Rejected rows disappear. Retained rows keep an ordered source
sublist and do not grow in height. Actual constructors use their current
resident records. Recursive head branches cannot occur for domain inputs.
Guards and equality classes have no restriction. These effects require
an actual completed graph and do not assert general completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequired
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityNeeded SourceEqualityRequiredGraph
open SourceEqualityRequiredCache (Keeps pure_keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "NodeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "ChildrenDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "RowsDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "EdgeDomain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
variable {Symbol Guard : Type}

/-- A result remains finite ordinary and has no greater constructor height. -/
def NodeNarrow (original result : Value Symbol Guard) : Prop :=
  NodeDomain result ∧ MergedOrdinaryHeight.height result ≤ MergedOrdinaryHeight.height original

/-- A retained row has finite ordinary children bounded by the original row height. -/
def EdgeNarrow (original result : EdgeValue Symbol Guard) : Prop :=
  EdgeDomain result ∧ MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgeHeight original

private theorem all₂_member {A B : Type} {relation : A → B → Prop} {originals : List A} {results : List B}
    (actual : All₂ relation originals results) (result : B) (member : result ∈ results) :
    ∃ original ∈ originals, relation original result := by
  induction actual with
  | nil => cases member
  | @cons original output originals outputs first rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst result
        exact ⟨original, List.mem_cons_self, first⟩
      · obtain ⟨value, present, related⟩ := ih later
        exact ⟨value, List.mem_cons_of_mem _ present, related⟩

private theorem children_structure {originals results : List (Value Symbol Guard)}
    (actual : All₂ NodeNarrow originals results) : ChildrenDomain results ∧
      MergedOrdinaryHeight.childrenHeight results ≤ MergedOrdinaryHeight.childrenHeight originals := by
  induction actual with
  | nil => exact ⟨.nil, Nat.le_refl _⟩
  | cons first rest ih =>
      exact ⟨.cons first.1 ih.1, Nat.max_le.mpr ⟨
        Nat.le_trans first.2 (Nat.le_max_left _ _),
        Nat.le_trans ih.2 (Nat.le_max_right _ _)⟩⟩

private theorem rows_height {originals selected results : List (EdgeValue Symbol Guard)}
    (subset : selected.Sublist originals) (actual : All₂ EdgeNarrow selected results) :
    ∀ result ∈ results, MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgesHeight originals := by
  intro result member
  obtain ⟨original, present, related⟩ := all₂_member actual result member
  exact Nat.le_trans related.2 ((MergedOrdinaryHeight.edgesHeight_le _ _).mp (Nat.le_refl _) original (subset.subset present))

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem make_node (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (resident : Edges before edges) (domain : RowsDomain edges)
    (bound : Nat) (bounded : ∀ edge ∈ edges, MergedOrdinaryHeight.edgeHeight edge + 1 ≤ bound) :
    Keeps before (run (makeNode edges) before).2 ∧ SemanticReady (run (makeNode edges) before).2 ∧
      Available (run (makeNode edges) before).2 (run (makeNode edges) before).1 ∧
      NodeDomain (run (makeNode edges) before).1 ∧ MergedOrdinaryHeight.height (run (makeNode edges) before).1 ≤ bound := by
  have checked := SourceEqualityOpenOrdinaryHead.node edges before semantic resident
  have facts := semantic.ready.semantic.1.normal.facts
  exact ⟨checked.1, checked.2.1, checked.2.2.1,
    SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode edges before facts.coherent facts.linked resident domain,
    SourceCurrentAllocatedFiniteOrdinaryDomain.makeNode_bound edges before facts.coherent facts.linked resident bound bounded⟩

/-- Actual finite ordinary head normalization retains its domain and original height bound. -/
theorem head {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (available : Available before value) (domain : NodeDomain value) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ NodeNarrow value result := by
  cases actual with
  | read fuel exposed middle read built =>
      cases domain with
      | empty =>
          have same := MergedSourceExposure.Result.done.inj (by
            simpa only [MergedFreshOrdinaryExposure.nodeEdges] using read)
          rcases same with ⟨rfl, rfl⟩
          have reduced : run (makeNode ([] : List (EdgeValue Symbol Guard))) before = (.empty, before) := by
            simp [makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds, run]
          rw [reduced] at built
          rcases Prod.mk.inj built with ⟨rfl, rfl⟩
          exact ⟨pure_keeps before semantic.ready, semantic, available, .empty, Nat.le_refl _⟩
      | @ordinary edges entry depth free rows =>
          have same := MergedSourceExposure.Result.done.inj (by
            simpa only [MergedFreshOrdinaryExposure.nodeEdges] using read)
          rcases same with ⟨rfl, rfl⟩
          have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
          have checked := make_node edges before semantic resident rows
            (MergedOrdinaryHeight.height (.node entry edges depth free))
            (fun edge member => Nat.succ_le_succ ((MergedOrdinaryHeight.edgesHeight_le edges _).mp (Nat.le_refl _) edge member))
          simpa only [built, NodeNarrow] using checked

private def NodeResult (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before value → NodeDomain value →
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ NodeNarrow value result

private def ChildrenResult (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (results : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Values before values → ChildrenDomain values →
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ChildrenDomain results ∧ All₂ NodeNarrow values results

private def RowsResult (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Edges before edges → RowsDomain edges →
    Keeps before after ∧ SemanticReady after ∧ Edges after results ∧ RowsDomain results ∧
      ∃ selected, selected.Sublist edges ∧ All₂ EdgeNarrow selected results

private theorem all_verified :
    (∀ needed (value : Value Symbol Guard) before result after,
      RequireNode needed value before result after → NodeResult value before result after) ∧
    (∀ entries index (values : List (Value Symbol Guard)) before results after,
      RequireChildren entries index values before results after → ChildrenResult values before results after) ∧
    (∀ entries (edges : List (EdgeValue Symbol Guard)) before results after,
      RequireRows entries edges before results after → RowsResult edges before results after) := by
  have identityCase : ∀ {value : Value Symbol Guard} {before}, NodeResult value before value before := by
    intro value before semantic available domain
    exact ⟨pure_keeps before semantic.ready, semantic, available, domain, Nat.le_refl _⟩
  have emptyCase : ∀ {entries : List (Int × Needed)} {before}, entries ≠ [] →
      NodeResult (.empty : Value Symbol Guard) before .empty before := by
    intro entries before _
    exact identityCase
  have ordinaryCase : ∀ {entries edges before rebuilt middle value after entry depth free},
      entries ≠ [] → RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before rebuilt middle →
      run (makeNode rebuilt) middle = (value, after) → RowsResult edges before rebuilt middle →
      NodeResult (.node entry edges depth free) before value after := by
    intro entries edges before rebuilt middle value after entry depth free _ _ built ih semantic available domain
    have resident := resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    obtain ⟨first, middleSemantic, rebuiltResident, rebuiltDomain, selected, subset, related⟩ :=
      ih semantic resident domain.rows
    have checked := make_node rebuilt middle middleSemantic rebuiltResident rebuiltDomain
      (MergedOrdinaryHeight.height (.node entry edges depth free))
      (fun edge member => Nat.succ_le_succ (rows_height subset related edge member))
    have final : Keeps middle after ∧ SemanticReady after ∧ Available after value ∧
        NodeNarrow (.node entry edges depth free) value := by simpa only [built, NodeNarrow] using checked
    exact ⟨first.trans final.1, final.2⟩
  have recursiveCase : ∀ {entries original before exposed middle value after}, entries ≠ [] →
      Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      RequireNode (Symbol := Symbol) (Guard := Guard) (.node entries) exposed middle value after →
      NodeResult exposed middle value after → NodeResult original before value after := by
    intro entries original before exposed middle value after _ recursive _ _ _ _ _ domain
    cases domain <;> cases recursive
  have nilChildren : ∀ {before}, ChildrenResult ([] : List (Value Symbol Guard)) before [] before := by
    intro before semantic _ _
    exact ⟨pure_keeps before semantic.ready, semantic, (fun _ absent => nomatch absent), .nil, .nil⟩
  have unselectedCase : ∀ {entries values before results after value} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = none →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values before results after →
      ChildrenResult values before results after → ChildrenResult (value :: values) before (value :: results) after := by
    intro entries values before results after value index _ _ ih semantic available domain
    cases domain with
    | cons firstDomain restDomain =>
        obtain ⟨kept, finalSemantic, resultsAvailable, resultsDomain, related⟩ :=
          ih semantic (fun child member => available child (List.mem_cons_of_mem _ member)) restDomain
        refine ⟨kept, finalSemantic, ?_, .cons firstDomain resultsDomain, .cons ⟨firstDomain, Nat.le_refl _⟩ related⟩
        intro child member
        rcases List.mem_cons.mp member with rfl | later
        · exact kept.available _ (available _ List.mem_cons_self)
        · exact resultsAvailable child later
  have selectedCase : ∀ {entries needed value before result middle values results after} (index : Nat),
      SourceEqualityNeededMap.lookup (index : Int) entries = some needed →
      RequireNode (Symbol := Symbol) (Guard := Guard) needed value before result middle →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries (index + 1) values middle results after →
      NodeResult value before result middle → ChildrenResult values middle results after →
      ChildrenResult (value :: values) before (result :: results) after := by
    intro entries needed value before result middle values results after index _ _ _ firstIH restIH semantic available domain
    cases domain with
    | cons firstDomain restDomain =>
        obtain ⟨first, middleSemantic, resultAvailable, resultNarrow⟩ :=
          firstIH semantic (available _ List.mem_cons_self) firstDomain
        obtain ⟨last, finalSemantic, resultsAvailable, resultsDomain, related⟩ := restIH middleSemantic
          (fun child member => first.available _ (available child (List.mem_cons_of_mem _ member))) restDomain
        refine ⟨first.trans last, finalSemantic, ?_, .cons resultNarrow.1 resultsDomain, .cons resultNarrow related⟩
        intro child member
        rcases List.mem_cons.mp member with rfl | later
        · exact last.available _ resultAvailable
        · exact resultsAvailable child later
  have nilRows : ∀ {before}, RowsResult ([] : List (EdgeValue Symbol Guard)) before [] before := by
    intro before semantic _ _
    exact ⟨pure_keeps before semantic.ready, semantic, (fun _ absent => nomatch absent), .nil, [], .refl [], .nil⟩
  have rejectedCase : ∀ {entries edges before results after edge}, fits (.node entries) edge.children.length = false →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges before results after → RowsResult edges before results after →
      RowsResult (edge :: edges) before results after := by
    intro entries edges before results after edge _ _ ih semantic resident domain
    cases domain with
    | cons _ restDomain =>
        obtain ⟨kept, finalSemantic, resultsResident, resultsDomain, selected, subset, related⟩ :=
          ih semantic (fun original member => resident original (List.mem_cons_of_mem _ member)) restDomain
        exact ⟨kept, finalSemantic, resultsResident, resultsDomain, selected, subset.cons edge, related⟩
  have keptCase : ∀ {entries before values middle result afterEdge edges results after edge},
      fits (.node entries) edge.children.length = true →
      RequireChildren (Symbol := Symbol) (Guard := Guard) entries 0 edge.children before values middle →
      run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle = (result, afterEdge) →
      RequireRows (Symbol := Symbol) (Guard := Guard) entries edges afterEdge results after →
      ChildrenResult edge.children before values middle → RowsResult edges afterEdge results after →
      RowsResult (edge :: edges) before (result :: results) after := by
    intro entries before values middle result afterEdge edges results after edge _ _ built _ firstIH restIH semantic resident domain
    cases domain with
    | cons firstDomain restDomain =>
        have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
          (resident edge List.mem_cons_self)
        obtain ⟨first, middleSemantic, valuesAvailable, valuesDomain, related⟩ := firstIH semantic available firstDomain
        have facts := middleSemantic.ready.semantic.1.normal.facts
        have bound : MergedOrdinaryHeight.childrenHeight values ≤ MergedOrdinaryHeight.edgeHeight edge :=
          by rw [SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children]; exact (children_structure related).2
        have narrowed : EdgeNarrow edge result := by
          have raw : EdgeNarrow edge (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).1 :=
            ⟨SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge _ _ _ middle facts.coherent facts.cached valuesAvailable valuesDomain,
              SourceCurrentAllocatedFiniteOrdinaryDomain.makeEdge_bound _ _ _ middle facts.coherent facts.cached valuesAvailable _
                ((MergedOrdinaryHeight.childrenHeight_le _ _).mp bound)⟩
          simpa only [built] using raw
        have constructor := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle
          middleSemantic.ready valuesAvailable
        have edgeKept : Keeps middle afterEdge := by simpa only [built] using constructor.1
        have edgeResident : EdgeResident afterEdge result := by simpa only [built] using constructor.2.1
        have edgeSemantic : SemanticReady afterEdge := by
          simpa only [built] using SourceEqualityRequiredSemanticCache.edge edge.entry.key.symbol edge.entry.key.constraint
            values middle middleSemantic valuesAvailable
        obtain ⟨last, finalSemantic, resultsResident, resultsDomain, selected, subset, tailRelated⟩ :=
          restIH edgeSemantic (fun original member => edge_grows before afterEdge (first.trans edgeKept).growth
            original (resident original (List.mem_cons_of_mem _ member))) restDomain
        refine ⟨(first.trans edgeKept).trans last, finalSemantic, ?_, .cons narrowed.1 resultsDomain,
          edge :: selected, subset.cons_cons edge, .cons narrowed tailRelated⟩
        intro original member
        rcases List.mem_cons.mp member with rfl | later
        · exact edge_grows afterEdge after last.growth original edgeResident
        · exact resultsResident original later
  refine ⟨?_, ?_, ?_⟩
  · intro needed value before result after actual
    exact RequireNode.rec
      (motive_1 := fun _ value before result after _ => NodeResult value before result after)
      (motive_2 := fun _ _ values before results after _ => ChildrenResult values before results after)
      (motive_3 := fun _ edges before results after _ => RowsResult edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries index values before results after actual
    exact RequireChildren.rec
      (motive_1 := fun _ value before result after _ => NodeResult value before result after)
      (motive_2 := fun _ _ values before results after _ => ChildrenResult values before results after)
      (motive_3 := fun _ edges before results after _ => RowsResult edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual
  · intro entries edges before results after actual
    exact RequireRows.rec
      (motive_1 := fun _ value before result after _ => NodeResult value before result after)
      (motive_2 := fun _ _ values before results after _ => ChildrenResult values before results after)
      (motive_3 := fun _ edges before results after _ => RowsResult edges before results after)
      identityCase emptyCase ordinaryCase recursiveCase (fun {_ _ _} => nilChildren) unselectedCase selectedCase
      (fun {_ _} => nilRows) rejectedCase keptCase actual

/-- Completed required-node calls preserve finite ordinary domain and do not increase height. -/
theorem node {needed : Needed} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : RequireNode needed value before result after) (semantic : SemanticReady before)
    (available : Available before value) (domain : NodeDomain value) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ NodeNarrow value result :=
  all_verified.1 _ _ _ _ _ actual semantic available domain

/-- Completed child calls retain every original position and its separate height bound. -/
theorem children {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (actual : RequireChildren entries index values before results after)
    (semantic : SemanticReady before) (available : Values before values) (domain : ChildrenDomain values) :
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ChildrenDomain results ∧ All₂ NodeNarrow values results :=
  all_verified.2.1 _ _ _ _ _ _ actual semantic available domain

/-- Completed rows retain an ordered source sublist with separate output-domain and height facts. -/
theorem rows {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    (actual : RequireRows entries edges before results after) (semantic : SemanticReady before)
    (resident : Edges before edges) (domain : RowsDomain edges) :
    Keeps before after ∧ SemanticReady after ∧ Edges after results ∧ RowsDomain results ∧
      ∃ selected, selected.Sublist edges ∧ All₂ EdgeNarrow selected results :=
  all_verified.2.2 _ _ _ _ _ actual semantic resident domain

/-- A literal completed requireAll return preserves domains and each original child-height bound. -/
theorem requireAll_done (fuel readFuel : Nat) (paths : List (List Int))
    (values results : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (done : SourceEqualityRequiredExecution.requireAll fuel readFuel paths values before = .done results after)
    (semantic : SemanticReady before) (available : Values before values) (domain : ChildrenDomain values) :
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ChildrenDomain results ∧ All₂ NodeNarrow values results := by
  have actual := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr
    ⟨fuel, readFuel, done⟩
  cases compiled : build paths with
  | node entries =>
      simp only [compiled] at actual
      exact children actual semantic available domain

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRequired
