import MicroCFTA.SourceEmptinessProjectionLocal

/-!
# Closed results along selected ordinary projection paths

The domain follows only selected children at ordinary path steps. Unrelated
ordinary siblings may remain open at every depth. A root result must be
closed. A nonempty path at a Mu or union head requires the whole original
value closed and uses the existing closed-head proofs. The domain does not
claim that the secondary gate makes an open recursive head safe. The proofs
retain actual reached graphs and heaps. They do not establish completion.
-/
namespace MicroCFTA.SourceEqualityProjectionPathDomain
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceEqualityRequiredGraph (Recursive)
open InternedGuardedLanguage (meaning)

/-- Follow selected ordinary children; recursive heads retain the whole-value closedness boundary. -/
def NodeClosed (path : List Int) (value : Value Symbol Guard) : Prop :=
  match path, value with
  | [], value => value.free = []
  | _ :: _, .empty => True
  | index :: path, .node _ edges _ _ =>
      ∀ edge ∈ edges, ∀ child, select edge.children index = some child → NodeClosed path child
  | _ :: _, value => value.free = []
termination_by path.length

/-- Every selected child of every original row satisfies the shorter path domain. -/
def RowsClosed (path : List Int) (index : Int) (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ edge ∈ edges, ∀ child, select edge.children index = some child → NodeClosed path child

/-- Root union reads all values; a proper forest path reads only its selected original value. -/
def ForestClosed (path : List Int) (values : List (Value Symbol Guard)) : Prop :=
  match path with
  | [] => ClosedValues values
  | index :: path => ∀ value, select values index = some value → NodeClosed path value

/-- A recursive head in the path domain meets the existing whole-value closedness premise. -/
theorem recursive_closed {index : Int} {path : List Int} {value : Value Symbol Guard}
    (recursive : Recursive value) (domain : NodeClosed (index :: path) value) : value.free = [] := by
  cases value <;> simp_all only [Recursive, NodeClosed]

private def NodeEffects (path : List Int) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before value → NodeClosed path value →
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = []

private def RowsEffects (path : List Int) (index : Int) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) (after : State Symbol Guard) : Prop :=
  SemanticReady before → Edges before edges → RowsClosed path index edges →
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ClosedValues results

private theorem effects [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after →
      NodeEffects path value before result after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsEffects path index edges before results after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeEffects [] value state value state := by
    intro value state semantic available domain
    exact ⟨pure_keeps state semantic.ready, semantic, available, by simpa only [NodeClosed] using domain⟩
  have emptyCase : ∀ {index path state}, NodeEffects (index :: path) (.empty : Value Symbol Guard) state .empty state := by
    intro index path state semantic _ _
    exact ⟨pure_keeps state semantic.ready, semantic, empty_available _, rfl⟩
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      SourceEqualityProjectionUnion.Union values middle result after → RowsEffects path index edges before values middle →
      NodeEffects (index :: path) (.node entry edges depth free) before result after := by
    intro path index edges before values middle result after entry depth free _ union ih semantic available domain
    have facts := semantic.ready.semantic.1.normal.facts
    have selected : RowsClosed path index edges := by simpa only [NodeClosed, RowsClosed] using domain
    have projected := ih semantic (InternedEdgeResidency.resident_edges before facts.linked _ available.resident) selected
    have final := union.verified projected.2.1 projected.2.2.1 projected.2.2.2
    exact ⟨projected.1.trans final.1, final.2.1, final.2.2.1, final.2.2.2.1⟩
  have recursiveCase : ∀ {original before exposed middle path index result after},
      Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeEffects (index :: path) exposed middle result after → NodeEffects (index :: path) original before result after := by
    intro original before exposed middle path index result after recursive head body _ semantic available domain
    exact SourceEqualityProjectionEffects.node (.recursive recursive head body) semantic available (recursive_closed recursive domain)
  have nilCase : ∀ {path index state}, RowsEffects path index ([] : List (EdgeValue Symbol Guard)) state [] state := by
    intro path index state semantic _ _
    exact ⟨pure_keeps state semantic.ready, semantic, by simp [Values], by simp [ClosedValues]⟩
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsEffects path index edges before results after → RowsEffects path index (edge :: edges) before results after := by
    intro edge path index edges before results after _ _ ih semantic resident domain
    exact ih semantic (fun value member => resident value (List.mem_cons_of_mem _ member))
      (fun original member => domain original (List.mem_cons_of_mem _ member))
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeEffects path child before result middle →
      RowsEffects path index edges middle results after → RowsEffects path index (edge :: edges) before (result :: results) after := by
    intro edge index child path before result middle edges results after found _ _ firstIH restIH semantic resident domain
    have first := firstIH semantic
      (semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
        child (select_member found)) (domain edge List.mem_cons_self child found)
    have rest := restIH first.2.1
      (fun original member => InternedEdgeResidency.edge_grows before middle first.1.growth original
        (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => domain original (List.mem_cons_of_mem _ member))
    refine ⟨first.1.trans rest.1, rest.2.1, ?_, ?_⟩
    · intro value member
      rcases List.mem_cons.mp member with rfl | tail
      · exact rest.1.available _ first.2.2.1
      · exact rest.2.2.1 value tail
    · intro value member
      rcases List.mem_cons.mp member with rfl | tail
      · exact first.2.2.2
      · exact rest.2.2.2 value tail
  constructor
  · intro path value before result after trace
    exact Project.rec (motive_1 := fun path value before result after _ => NodeEffects path value before result after)
      (motive_2 := fun path index edges before results after _ => RowsEffects path index edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace
  · intro path index edges before results after trace
    exact ProjectRows.rec (motive_1 := fun path value before result after _ => NodeEffects path value before result after)
      (motive_2 := fun path index edges before results after _ => RowsEffects path index edges before results after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace

/-- Every actual node projection in the selected path domain has closed resident output and exact heap effects. -/
theorem node_effects [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) (semantic : SemanticReady before)
    (available : Available before value) (domain : NodeClosed path value) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] :=
  effects.1 _ _ _ _ _ trace semantic available domain

/-- Actual selected row projections retain all closed results in the returned heap. -/
theorem rows_effects [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)} {results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : ProjectRows path index edges before results after)
    (semantic : SemanticReady before) (resident : Edges before edges) (domain : RowsClosed path index edges) :
    Keeps before after ∧ SemanticReady after ∧ Values after results ∧ ClosedValues results :=
  effects.2 _ _ _ _ _ _ trace semantic resident domain

/-- A forest path needs the domain of only its selected original value. -/
theorem forest_effects [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Forest path values before result after) (semantic : SemanticReady before)
    (available : Values before values) (domain : ForestClosed path values) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] := by
  cases trace with
  | root union =>
      have checked := union.verified semantic available domain
      exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩
  | missing => exact ⟨pure_keeps _ semantic.ready, semantic, empty_available _, rfl⟩
  | selected found body => exact node_effects body semantic (available _ (select_member found)) (domain _ found)

private def NodeIncluded (path : List Int) (value : Value Symbol Guard) (before : State Symbol Guard)
    (result : Value Symbol Guard) : Prop :=
  SemanticReady before → Available before value → NodeClosed path value →
    ∀ holds ambient term part, meaning holds ambient value term → SymbolicSignedPaths.lookup term path = some part →
      meaning holds ambient result part

private def RowsIncluded (path : List Int) (index : Int) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (results : List (Value Symbol Guard)) : Prop :=
  SemanticReady before → Edges before edges → RowsClosed path index edges →
    ∀ holds ambient edge, edge ∈ edges → ∀ child, select edge.children index = some child →
      ∀ term part, meaning holds ambient child term → SymbolicSignedPaths.lookup term path = some part →
        ∃ result ∈ results, meaning holds ambient result part

private theorem included [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after →
      NodeIncluded path value before result) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsIncluded path index edges before results) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeIncluded [] value state value := by
    intro value state _ _ _ holds ambient term part accepted selected
    cases Option.some.inj selected
    exact accepted
  have emptyCase : ∀ {index path state}, NodeIncluded (index :: path) (.empty : Value Symbol Guard) state .empty := by
    intro index path state _ _ _ holds ambient term part impossible
    exact False.elim ((InternedGuardedLanguage.laws holds ambient).empty term impossible)
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      SourceEqualityProjectionUnion.Union values middle result after → RowsIncluded path index edges before values →
      NodeIncluded (index :: path) (.node entry edges depth free) before result := by
    intro path index edges before values middle result after entry depth free rows union ih semantic available domain holds ambient term part accepted selected
    have facts := semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
    have localDomain : RowsClosed path index edges := by simpa only [NodeClosed, RowsClosed] using domain
    have projected := rows_effects rows semantic resident localDomain
    have unionExact := (union.verified projected.2.1 projected.2.2.1 projected.2.2.2).2.2.2.2 holds ambient part
    obtain ⟨edge, member, terms, rfl, children, _⟩ :=
      (InternedGuardedLanguage.laws holds ambient).node entry edges depth free term |>.mp accepted
    rw [SourceEqualityNeededMeaning.lookup_cons] at selected
    obtain ⟨subterm, atIndex, atPath⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨child, childFound, childAccepted⟩ :=
      SourceEqualityProjectionLanguage.all₂_signed children index subterm atIndex
    exact unionExact.mpr (ih semantic resident localDomain holds ambient edge member child childFound subterm part childAccepted atPath)
  have recursiveCase : ∀ {original before exposed middle path index result after},
      Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeIncluded (index :: path) exposed middle result → NodeIncluded (index :: path) original before result := by
    intro original before exposed middle path index result after recursive head body _ semantic available domain
    exact SourceEqualityProjectionLanguage.node (.recursive recursive head body) semantic available (recursive_closed recursive domain)
  have nilCase : ∀ {path index state}, RowsIncluded path index ([] : List (EdgeValue Symbol Guard)) state [] := by
    intro path index state _ _ _ holds ambient edge impossible
    cases impossible
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsIncluded path index edges before results → RowsIncluded path index (edge :: edges) before results := by
    intro edge path index edges before results after absent _ ih semantic resident domain holds ambient original member child found term part accepted selected
    rcases List.mem_cons.mp member with rfl | tail
    · rw [absent] at found; cases found
    · exact ih semantic (fun edge member => resident edge (List.mem_cons_of_mem _ member))
        (fun edge member => domain edge (List.mem_cons_of_mem _ member))
        holds ambient original tail child found term part accepted selected
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeIncluded path child before result →
      RowsIncluded path index edges middle results → RowsIncluded path index (edge :: edges) before (result :: results) := by
    intro edge index child path before result middle edges results after found first _ firstIH restIH semantic resident domain holds ambient original member selectedChild selectedAt term part accepted selected
    have childAvailable := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self) child (select_member found)
    have childDomain := domain edge List.mem_cons_self child found
    rcases List.mem_cons.mp member with rfl | tail
    · have same := Option.some.inj (found.symm.trans selectedAt)
      subst selectedChild
      exact ⟨result, List.mem_cons_self, firstIH semantic childAvailable childDomain holds ambient term part accepted selected⟩
    · have firstEffects := node_effects first semantic childAvailable childDomain
      obtain ⟨value, member, accepted⟩ := restIH firstEffects.2.1
        (fun edge member => InternedEdgeResidency.edge_grows before middle firstEffects.1.growth edge
          (resident edge (List.mem_cons_of_mem _ member)))
        (fun edge member => domain edge (List.mem_cons_of_mem _ member))
        holds ambient original tail selectedChild selectedAt term part accepted selected
      exact ⟨value, List.mem_cons_of_mem _ member, accepted⟩
  constructor
  · intro path value before result after trace
    exact Project.rec (motive_1 := fun path value before result _ _ => NodeIncluded path value before result)
      (motive_2 := fun path index edges before results _ _ => RowsIncluded path index edges before results)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace
  · intro path index edges before results after trace
    exact ProjectRows.rec (motive_1 := fun path value before result _ _ => NodeIncluded path value before result)
      (motive_2 := fun path index edges before results _ _ => RowsIncluded path index edges before results)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace

/-- Actual node projection includes the selected subtree under only its syntactic path domain. -/
theorem node_included [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) (semantic : SemanticReady before)
    (available : Available before value) (domain : NodeClosed path value)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (term part : Term Symbol) (accepted : meaning holds ambient value term)
    (selected : SymbolicSignedPaths.lookup term path = some part) : meaning holds ambient result part :=
  included.1 _ _ _ _ _ trace semantic available domain holds ambient term part accepted selected

/-- A selected accepted original row child has an accepting projection among the actual returned results. -/
theorem rows_included [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)} {results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : ProjectRows path index edges before results after)
    (semantic : SemanticReady before) (resident : Edges before edges) (domain : RowsClosed path index edges)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (child : Value Symbol Guard)
    (found : select edge.children index = some child) (term part : Term Symbol)
    (accepted : meaning holds ambient child term) (selected : SymbolicSignedPaths.lookup term path = some part) :
    ∃ result ∈ results, meaning holds ambient result part :=
  included.2 _ _ _ _ _ _ trace semantic resident domain holds ambient edge member child found term part accepted selected

/-- A proper forest path retains the selected accepted subtree through deeper ordinary open siblings. -/
theorem forest_included [DecidableEq (EdgeKey Symbol Guard)]
    {index : Int} {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard} (trace : Forest (index :: path) values before result after)
    (semantic : SemanticReady before) (available : Values before values) (domain : ForestClosed (index :: path) values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) (index :: path) = some part) :
    meaning holds ambient result part := by
  rw [SourceEqualityNeededMeaning.lookup_cons] at selected
  obtain ⟨term, termAt, partAt⟩ := Option.bind_eq_some_iff.mp selected
  obtain ⟨value, valueAt, valueAccepted⟩ := SourceEqualityProjectionLanguage.all₂_signed accepted index term termAt
  cases trace with
  | missing absent => rw [absent] at valueAt; cases valueAt
  | selected found body =>
      have same := Option.some.inj (found.symm.trans valueAt)
      subst value
      exact node_included body semantic (available _ (select_member found)) (domain _ found)
        holds ambient term part valueAccepted partAt

private def NodeHeap (annotation : Guard → Prop) (path : List Int) (value : Value Symbol Guard)
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Available before value → NodeClosed path value →
    SourceEqualityAnnotationHeap.Heap annotation before → SourceEqualityAnnotationHeap.Heap annotation after

private def RowsHeap (annotation : Guard → Prop) (path : List Int) (index : Int) (edges : List (EdgeValue Symbol Guard))
    (before after : State Symbol Guard) : Prop :=
  SemanticReady before → Edges before edges → RowsClosed path index edges →
    SourceEqualityAnnotationHeap.Heap annotation before → SourceEqualityAnnotationHeap.Heap annotation after

private theorem heap_effects (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after →
      NodeHeap annotation path value before after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsHeap annotation path index edges before after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeHeap annotation [] value state state := by
    intro value state _ _ _ heap; exact heap
  have emptyCase : ∀ {index path state}, NodeHeap annotation (index :: path) (.empty : Value Symbol Guard) state state := by
    intro index path state _ _ _ heap; exact heap
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      SourceEqualityProjectionUnion.Union values middle result after → RowsHeap annotation path index edges before middle →
      NodeHeap annotation (index :: path) (.node entry edges depth free) before after := by
    intro path index edges before values middle result after entry depth free rows union ih semantic available domain heap
    have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
    have localDomain : RowsClosed path index edges := by simpa only [NodeClosed, RowsClosed] using domain
    have checked := rows_effects rows semantic resident localDomain
    exact SourceEqualityAnnotationProjection.union annotation union checked.2.1 checked.2.2.1 checked.2.2.2
      (ih semantic resident localDomain heap)
  have recursiveCase : ∀ {original before exposed middle path index result after},
      Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeHeap annotation (index :: path) exposed middle after → NodeHeap annotation (index :: path) original before after := by
    intro original before exposed middle path index result after recursive head body _ semantic available domain heap
    exact SourceEqualityAnnotationProjection.node annotation (.recursive recursive head body) semantic available
      (recursive_closed recursive domain) heap
  have nilCase : ∀ {path index state}, RowsHeap annotation path index ([] : List (EdgeValue Symbol Guard)) state state := by
    intro path index state _ _ _ heap; exact heap
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsHeap annotation path index edges before after → RowsHeap annotation path index (edge :: edges) before after := by
    intro edge path index edges before results after _ _ ih semantic resident domain heap
    exact ih semantic (fun value member => resident value (List.mem_cons_of_mem _ member))
      (fun original member => domain original (List.mem_cons_of_mem _ member)) heap
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeHeap annotation path child before middle →
      RowsHeap annotation path index edges middle after → RowsHeap annotation path index (edge :: edges) before after := by
    intro edge index child path before result middle edges results after found first _ firstIH restIH semantic resident domain heap
    have childAvailable := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge
      (resident edge List.mem_cons_self) child (select_member found)
    have childDomain := domain edge List.mem_cons_self child found
    have firstEffects := node_effects first semantic childAvailable childDomain
    exact restIH firstEffects.2.1
      (fun original member => InternedEdgeResidency.edge_grows before middle firstEffects.1.growth original
        (resident original (List.mem_cons_of_mem _ member)))
      (fun original member => domain original (List.mem_cons_of_mem _ member))
      (firstIH semantic childAvailable childDomain heap)
  constructor
  · intro path value before result after trace
    exact Project.rec (motive_1 := fun path value before _ after _ => NodeHeap annotation path value before after)
      (motive_2 := fun path index edges before _ after _ => RowsHeap annotation path index edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace
  · intro path index edges before results after trace
    exact ProjectRows.rec (motive_1 := fun path value before _ after _ => NodeHeap annotation path value before after)
      (motive_2 := fun path index edges before _ after _ => RowsHeap annotation path index edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace

/-- Every actual node projection in the selected path domain preserves physical annotations. -/
theorem node_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) (semantic : SemanticReady before)
    (available : Available before value) (domain : NodeClosed path value)
    (heap : SourceEqualityAnnotationHeap.Heap annotation before) : SourceEqualityAnnotationHeap.Heap annotation after :=
  (heap_effects annotation).1 _ _ _ _ _ trace semantic available domain heap

/-- Every actual selected row projection preserves physical annotations at its returned heap. -/
theorem rows_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)} {results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : ProjectRows path index edges before results after)
    (semantic : SemanticReady before) (resident : Edges before edges) (domain : RowsClosed path index edges)
    (heap : SourceEqualityAnnotationHeap.Heap annotation before) : SourceEqualityAnnotationHeap.Heap annotation after :=
  (heap_effects annotation).2 _ _ _ _ _ _ trace semantic resident domain heap

/-- The forest path domain preserves annotations without closing unrelated ordinary siblings. -/
theorem forest_heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Forest path values before result after) (semantic : SemanticReady before)
    (available : Values before values) (domain : ForestClosed path values)
    (heap : SourceEqualityAnnotationHeap.Heap annotation before) : SourceEqualityAnnotationHeap.Heap annotation after := by
  cases trace with
  | root union => exact SourceEqualityAnnotationProjection.union annotation union semantic available domain heap
  | missing => exact heap
  | selected found body => exact node_heap annotation body semantic (available _ (select_member found)) (domain _ found) heap

/-- An actual operand in the deeper path domain preserves the same physical annotation heap. -/
theorem operand_path_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : SourceEmptinessProjection.Operand path values before result after)
    (ready : SourceEqualityNativeScoped.IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domain : ForestClosed path values)
    (heap : SourceEqualityAnnotationHeap.Heap annotation before.machine.heap) :
    SourceEqualityAnnotationHeap.Heap annotation after.machine.heap := by
  cases trace with
  | force projection => exact forest_heap annotation projection ready.semantic available domain heap

end MicroCFTA.SourceEqualityProjectionPathDomain

namespace MicroCFTA.SourceEmptinessProjection
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain
open InternedGuardedLanguage (meaning)

/-- A selected path domain retains actual operand effects without closing unrelated ordinary siblings. -/
theorem Operand.path_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domain : ForestClosed path values) :
    IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  cases trace with
  | force projection =>
      have checked := SourceEqualityProjectionPathDomain.forest_effects projection ready.semantic available domain
      exact ⟨ready.advance _ checked.1 checked.2.1, checked.1, checked.2.2.1, checked.2.2.2, rfl, rfl, rfl⟩

/-- A proper operand retains its accepted subtree under the deeper selected ordinary path domain. -/
theorem Operand.path_included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Operand path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (available : Values before.machine.heap values) (domain : ForestClosed path values) (nonroot : path ≠ [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) path = some part) : meaning holds ambient result part := by
  cases path with
  | nil => exact False.elim (nonroot rfl)
  | cons index path =>
      cases trace with
      | force projection =>
          exact SourceEqualityProjectionPathDomain.forest_included projection ready.semantic available domain
            holds ambient symbol terms part accepted selected

end MicroCFTA.SourceEmptinessProjection
