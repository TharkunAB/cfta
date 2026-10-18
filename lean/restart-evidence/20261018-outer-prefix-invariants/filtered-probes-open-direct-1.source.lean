import MicroCFTA.SourceEqualityProbeUnfold
import MicroCFTA.SourceCurrentOpenExposureFields
import MicroCFTA.SourceCurrentRequiredHeapEffects
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Physical Mu probe filters through completed open readers

Available worklist values supply every actual unfolding input. Completed
Head and projection graphs retain the same filters without closed inputs.
The statements preserve completed executions. They do not assert progress.
-/
namespace MicroCFTA.SourceCurrentOpenProbeHeap
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedNestedConstruction (Outcome)
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)
open SourceEqualityRequiredSemanticCache
open InternedFreshOrdinaryProbeHeap (Heap)
open SourceEqualityAnnotationExposure (prepend_state canonical_state)

/-- Bounded collection retains physical edge annotations with unrelated open inputs. -/
private theorem collectHeap [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (state : State Symbol Guard) (semantic : SemanticReady state)
    (heap : Heap state) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) : Heap (collect fuel state seen pending).state := by
  induction fuel generalizing state seen pending with
  | zero => cases pending <;> exact heap
  | succ fuel ih =>
      cases pending with
      | nil => exact heap
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state semantic heap seen rest restInputs
          | reference => exact heap
          | node entry edges depth free =>
              simpa only [collect, prepend_state] using ih state semantic heap seen rest restInputs
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic heap seen rest restInputs
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                simpa only [collect, ite_eq_right visited] using
                  ih state semantic heap (entry.identity :: seen) (members ++ rest) nextInputs
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state semantic heap seen rest restInputs
              · obtain ⟨result, after, done, kept, afterSemantic, resultAvailable, _⟩ :=
                  SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
                have retained := SourceEqualityProbeUnfold.unfold (.mu entry body depth ordinary) state
                  semantic.ready.semantic.1 heap available
                have afterHeap : Heap after := by
                  simpa only [done, Outcome.state] using retained
                have nextInputs : Values after (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact resultAvailable
                  · exact kept.available child (restInputs child member)
                simpa only [collect, ite_eq_right visited, done] using
                  ih after afterSemantic afterHeap (entry.identity :: seen) (result :: rest) nextInputs

/-- Actual direct and closure reads retain physical annotations without whole-value closedness. -/
private theorem nodeEdgesHeap [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (semantic : SemanticReady state) (heap : Heap state) (available : Available state value) :
    Heap (nodeEdges fuel value state).state := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticReady current)
      (currentHeap : Heap current) (root : Value Symbol Guard) (rootAvailable : Available current root) :
      Heap (collect fuel current [] [root]).canonical.state := by
    rw [canonical_state]
    exact collectHeap fuel current currentSemantic currentHeap [] [root]
      (by intro child member; simpa only [List.mem_singleton.mp member] using rootAvailable)
  cases value with
  | empty | reference | node => exact heap
  | union => exact fallback state semantic heap _ available
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done, kept, afterSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete (.mu entry body depth ordinary) state semantic available
      have retained := SourceEqualityProbeUnfold.unfold (.mu entry body depth ordinary) state
        semantic.ready.semantic.1 heap available
      have afterHeap : Heap after := by
        simpa only [done, Outcome.state] using retained
      have closure := fallback after afterSemantic afterHeap (.mu entry body depth ordinary)
        (kept.available _ available)
      cases result with
      | node => simpa only [nodeEdges, done, Result.state] using afterHeap
      | empty | reference | union | mu => simpa only [nodeEdges, done] using closure

/-- Every actual completed open Head retains both physical Mu probe filters. -/
theorem head [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (available : Available before value) (probes : Heap before) : Heap after := by
  cases trace with
  | read fuel edges middle exposed rebuilt =>
    have retained := nodeEdgesHeap fuel value before semantic probes available
    have middleHeap : Heap middle := by simpa only [exposed,Result.state] using retained
    simpa only [rebuilt] using InternedFreshOrdinaryProbeHeap.node edges middle middleHeap

open InternedNestedProvenance (Edges)
open SourceEqualityRequiredCache SourceEqualityProjectionGraph

/-- An actual row read preserves annotations in its returned cache. -/
private theorem read [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : SourceEqualityProjectionRead.Read value before edges after) (semantic : SemanticReady before)
    (available : Available before value) (heap : Heap before) : Heap after := by
  cases trace with
  | done fuel completed =>
      simpa only [completed, MergedSourceExposure.Result.state] using
        nodeEdgesHeap fuel value before semantic heap available

/-- Ordered union operands preserve annotations through all actual row reads. -/
private theorem readAll [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : SourceEqualityProjectionUnion.ReadAll values before edges after) (semantic : SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Values before values) (heap : Heap before) : Heap after := by
  induction trace with
  | nil => exact heap
  | cons first _ ih =>
      have checked := SourceEqualityProjectionCosts.read_effects first semantic costs (available _ List.mem_cons_self)
      have middleHeap := read first semantic (available _ List.mem_cons_self) heap
      exact ih checked.2.1 checked.2.2.1
        (fun child member => checked.1.available child (available child (List.mem_cons_of_mem _ member))) middleHeap

/-- The complete source union retains annotations after its row reads and node request. -/
private theorem union [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (trace : SourceEqualityProjectionUnion.Union values before result after) (semantic : SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Values before values) (heap : Heap before) : Heap after := by
  cases trace with
  | node rows built =>
      have middleHeap := readAll rows semantic costs available heap
      have final := congrArg Prod.snd built
      dsimp only at final
      rw [← final]
      exact InternedFreshOrdinaryProbeHeap.node _ _ middleHeap

private def NodeLaw (value : Value Symbol Guard) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → InternedFreshOrdinaryCostHeap.Heap before → Available before value → Heap before → Heap after

private def RowsLaw (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard) : Prop :=
  SemanticReady before → InternedFreshOrdinaryCostHeap.Heap before → Edges before edges → Heap before → Heap after

private theorem effects [DecidableEq (EdgeKey Symbol Guard)] :
    (∀ path (value : Value Symbol Guard) before result after, Project path value before result after → NodeLaw value before after) ∧
    (∀ path index (edges : List (EdgeValue Symbol Guard)) before results after,
      ProjectRows path index edges before results after → RowsLaw edges before after) := by
  have rootCase : ∀ {value : Value Symbol Guard} {state}, NodeLaw value state state := by
    intro value state _ _ _ heap; exact heap
  have emptyCase : ∀ {state}, NodeLaw (.empty : Value Symbol Guard) state state := by
    intro state _ _ _ heap; exact heap
  have ordinaryCase : ∀ {path index edges before values middle result after entry depth free},
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before values middle →
      SourceEqualityProjectionUnion.Union values middle result after → RowsLaw edges before middle →
      NodeLaw (.node entry edges depth free) before after := by
    intro path index edges before values middle result after entry depth free trace joined ih semantic costs available heap
    have facts := semantic.ready.semantic.1.normal.facts
    have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
    have rows := SourceEqualityProjectionCosts.rows_effects trace semantic costs resident
    exact union joined rows.2.1 rows.2.2.1 rows.2.2.2 (ih semantic costs resident heap)
  have recursiveCase : ∀ {original before exposed middle path index result after},
      SourceEqualityRequiredGraph.Recursive original → SourceEqualityRequiredHead.Head original before exposed middle →
      Project (Symbol := Symbol) (Guard := Guard) (index :: path) exposed middle result after →
      NodeLaw exposed middle after → NodeLaw original before after := by
    intro original before exposed middle path index result after _ head _ ih semantic costs available heap
    have first := SourceEqualityProjectionCosts.head_effects head semantic costs available
    exact ih first.2.1 first.2.2.1 first.2.2.2
      (SourceCurrentOpenProbeHeap.head head semantic available heap)
  have nilCase : ∀ {state}, RowsLaw ([] : List (EdgeValue Symbol Guard)) state state := by
    intro state _ _ _ heap; exact heap
  have missingCase : ∀ {edge path index edges before results after}, select edge.children index = none →
      ProjectRows (Symbol := Symbol) (Guard := Guard) path index edges before results after →
      RowsLaw edges before after → RowsLaw (edge :: edges) before after := by
    intro edge path index edges before results after _ _ ih semantic costs resident heap
    exact ih semantic costs (fun value member => resident value (List.mem_cons_of_mem _ member)) heap
  have selectedCase : ∀ {edge index child path before result middle edges results after},
      select edge.children index = some child → Project (Symbol := Symbol) (Guard := Guard) path child before result middle →
      ProjectRows path index edges middle results after → NodeLaw child before middle →
      RowsLaw edges middle after → RowsLaw (edge :: edges) before after := by
    intro edge index child path before result middle edges results after found firstTrace _ firstIH restIH semantic costs resident heap
    have member := select_member found
    have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self) child member
    have first := SourceEqualityProjectionCosts.project_effects firstTrace semantic costs available
    have middleHeap := firstIH semantic costs available heap
    exact restIH first.2.1 first.2.2.1
      (fun edge present => InternedEdgeResidency.edge_grows before middle first.1.growth edge (resident edge (List.mem_cons_of_mem _ present)))
      middleHeap
  constructor
  · intro path value before result after trace
    exact Project.rec (motive_1 := fun _ value before _ after _ => NodeLaw value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsLaw edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace
  · intro path index edges before results after trace
    exact ProjectRows.rec (motive_1 := fun _ value before _ after _ => NodeLaw value before after)
      (motive_2 := fun _ _ edges before _ after _ => RowsLaw edges before after)
      rootCase emptyCase ordinaryCase recursiveCase nilCase missingCase selectedCase trace

/-- Every completed general node projection preserves physical edge annotations. -/
private theorem node [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project path value before result after) (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Available before value)
    (heap : Heap before) : Heap after :=
  (effects).1 _ _ _ _ _ trace semantic costs available heap

/-- Every completed ordered row projection preserves the same physical annotation heap. -/
private theorem rows [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {index : Int} {edges : List (EdgeValue Symbol Guard)} {results : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (trace : ProjectRows path index edges before results after) (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before) (resident : Edges before edges)
    (heap : Heap before) : Heap after :=
  (effects).2 _ _ _ _ _ _ trace semantic costs resident heap

/-- Forest projection retains annotations in its root, missing, and selected branches. -/
theorem forest [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Forest path values before result after) (semantic : SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Values before values) (heap : Heap before) : Heap after := by
  cases trace with
  | root joined => exact union joined semantic costs available heap
  | missing => exact heap
  | selected found body => exact node body semantic costs (available _ (select_member found)) heap


end MicroCFTA.SourceCurrentOpenProbeHeap
