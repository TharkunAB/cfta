import MicroCFTA.MergedColdMerge
import MicroCFTA.MergedSourceGrouping

/-!
# Completion of cold ordered merging

Ordinary height bounds recursive merge calls. The actual stateful
comparison filter supplies a stable finite bound at every demanded cache.
Finite ordered traversal combines these into one comparison bound.
-/
namespace MicroCFTA.MergedColdMerge
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open InternedEdgeResidency InternedShallowHeap MergedPhysicalWarmup MergedSourceComparison
open MergedPhysicalGroupColumns MergedOrdinaryHeight

/-- Ordered requests combine exact completion bounds and retain each positional output invariant. -/
theorem map_complete (call : Nat → Request → Action Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop) (post : State Symbol Guard → Output → Prop)
    (preGrows : ∀ before after, Extension before after → ∀ request, pre before request → pre after request)
    (postGrows : ∀ before after, Extension before after → ∀ value, post before value → post after value)
    (requests : List Request)
    (complete : ∀ request ∈ requests, ∀ state, Facts state → Prepared state → pre state request →
      Complete (fun fuel => call fuel request) state post)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (inputs : ∀ request ∈ requests, pre state request) :
    Complete (fun fuel => map (call fuel) requests) state (fun after values => ∀ value ∈ values, post after value) := by
  induction requests generalizing state with
  | nil => exact pure_complete [] state facts prepared _ (by simp)
  | cons first rest ih =>
      apply bind_complete _ _ state post _ (complete first List.mem_cons_self state facts prepared (inputs first List.mem_cons_self))
      intro value middle firstExtension valid
      apply bind_complete _ _ middle _ _
        (ih (fun request member => complete request (List.mem_cons_of_mem _ member)) middle firstExtension.facts firstExtension.prepared
          (fun request member => preGrows state middle firstExtension request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after restExtension restValid
      apply pure_complete (value :: values) after restExtension.facts restExtension.prepared
      intro result member
      rcases List.mem_cons.mp member with rfl | member
      · exact postGrows middle after restExtension _ valid
      · exact restValid result member

/-- Actual cold selection has a stable bound and returns available original records. -/
theorem select_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Values state inputs) :
    Complete (fun fuel => MergedSourceSelection.select clear fuel inputs) state
      (fun after retained => Values after retained ∧ ∀ value ∈ retained, value ∈ inputs) := by
  obtain ⟨bound, retained, after, done, verified, afterPrepared⟩ :=
    MergedSourceSelection.select_complete clear inputs state facts prepared available
  have subset := MergedSourceSelection.select_subset clear bound inputs state retained after (done bound (Nat.le_refl _))
  exact ⟨bound, retained, after, done, ⟨verified.facts, afterPrepared, verified.growth, verified.history⟩,
    (fun value member => (available value (subset value member)).grows state after verified.growth verified.history), subset⟩

/-- Retained column construction requires recursive completion only at its smaller ordinary height. -/
theorem retained_complete [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Facts state → Prepared state → Available state value →
      Complete (fun fuel => recurse fuel value) state Available)
    (retained : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Values state retained) (bounded : ∀ value ∈ retained, height value ≤ limit) :
    Complete (fun fuel => retainedColumn (recurse fuel) retained) state Available := by
  have branches (values : List (Value Symbol Guard)) (available : Values state values)
      (bounded : ∀ value ∈ values, height value ≤ limit) :
      Complete (fun fuel => if values.any recursiveBoundary then work (makeUnion values)
        else bind (work (ordinaryUnion values)) (recurse fuel)) state Available := by
    by_cases boundary : values.any recursiveBoundary = true
    · simpa only [boundary, ↓reduceIte] using work_complete (makeUnion values) state prepared Available
        (union_verified values state facts available) (makeUnion_noNewMu values state)
    · simp only [boundary, Bool.false_eq_true, ↓reduceIte]
      have resident : Edges state (values.flatMap InternedEdgeResidency.nodeEdges) := by
        intro edge member
        obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
        exact resident_edges state facts.linked value (available value present).resident edge included
      have unionComplete := work_complete (ordinaryUnion values) state prepared Available
        (node_verified (values.flatMap InternedEdgeResidency.nodeEdges) state facts resident)
        (makeNode_noNewMu _ state)
      obtain ⟨bound, result, middle, done, extension, valid⟩ := unionComplete
      have actual : result = (run (ordinaryUnion values) state).1 ∧ middle = (run (ordinaryUnion values) state).2 := by
        exact Result.done.inj (done bound (Nat.le_refl _)).symm
      rcases actual with ⟨rfl, rfl⟩
      have boundHeight := ordinaryUnion_bound values state facts.coherent facts.linked
        (fun value member => (available value member).resident) limit bounded
      obtain ⟨later, output, after, nextDone, nextExtension, checked⟩ := smaller _ boundHeight _ extension.facts extension.prepared valid
      refine ⟨later, output, after, ?_, extension.trans nextExtension, checked⟩
      intro fuel enough
      simpa only [bind, work, Result.bind] using nextDone fuel enough
  cases retained with
  | nil => exact branches [] available bounded
  | cons first rest =>
      cases rest with
      | nil => exact pure_complete first state facts prepared Available (available first List.mem_cons_self)
      | cons second tail => exact branches (first :: second :: tail) available bounded

/-- Actual stateful filtering precedes the complete retained-column constructor sequence. -/
theorem column_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (clear : Guard → Bool)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Facts state → Prepared state → Available state value →
      Complete (fun fuel => recurse fuel value) state Available)
    (inputs : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Values state inputs) (bounded : ∀ value ∈ inputs, height value ≤ limit) :
    Complete (fun fuel => column (recurse fuel) clear fuel inputs) state Available := by
  apply bind_complete _ _ state _ _ (select_complete clear inputs state facts prepared available)
  intro retained after extension selected
  exact retained_complete recurse limit smaller retained after extension.facts extension.prepared selected.1
    (fun value member => bounded value (selected.2 value member))

/-- Small edges complete every child before the actual edge constructor. -/
theorem small_complete [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Facts state → Prepared state → Available state value →
      Complete (fun fuel => recurse fuel value) state Available)
    (edge : EdgeValue Symbol Guard) (bounded : ∀ value ∈ edge.children, height value ≤ limit)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (resident : EdgeResident state edge) :
    Complete (fun fuel => small (recurse fuel) edge) state EdgeResident := by
  have children := map_complete recurse Available Available
    (fun _ _ extension value available => extension.available value available)
    (fun _ _ extension value available => extension.available value available) edge.children
    (fun value member state facts prepared available => smaller value (bounded value member) state facts prepared available)
    state facts prepared (facts.cached.edges edge.entry.key edge resident)
  apply bind_complete _ _ state _ EdgeResident children
  intro values after extension available
  exact work_complete (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) after extension.prepared EdgeResident
    (edge_verified edge.entry.key.symbol edge.entry.key.constraint values after extension.facts available)
    (by intro key entry body depth ordinary stored; exact stored)

/-- Large groups complete the actual ordered cold columns before their Top-guard edge. -/
theorem large_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (clear : Guard → Bool) (top : Guard)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Facts state → Prepared state → Available state value →
      Complete (fun fuel => recurse fuel value) state Available)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (bounded : ∀ edge ∈ first :: rest, ∀ value ∈ edge.children, height value ≤ limit)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (resident : Edges state (first :: rest)) :
    Complete (fun fuel => large (recurse fuel) clear fuel top first rest) state EdgeResident := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  have children := map_complete (fun fuel => column (recurse fuel) clear fuel) Values Available
    (fun _ _ extension _ available value member => extension.available value (available value member))
    (fun _ _ extension value available => extension.available value available) columns
    (fun column member state facts prepared inputs => column_complete recurse limit clear smaller column state facts prepared inputs
      (fun value included => by obtain ⟨edge, outer, inner⟩ := original column member value included; exact bounded edge outer value inner))
    state facts prepared (fun column member value included => by
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact facts.cached.edges edge.entry.key edge (resident edge outer) value inner)
  apply bind_complete _ _ state _ EdgeResident children
  intro values after extension available
  exact work_complete (makeEdge first.entry.key.symbol top values) after extension.prepared EdgeResident
    (edge_verified first.entry.key.symbol top values after extension.facts available)
    (by intro key entry body depth ordinary stored; exact stored)

/-- Both source threshold branches derive a uniform comparison bound for the entire group. -/
theorem group_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (clear : Guard → Bool) (top : Guard)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Facts state → Prepared state → Available state value →
      Complete (fun fuel => recurse fuel value) state Available)
    (edges : List (EdgeValue Symbol Guard))
    (bounded : ∀ edge ∈ edges, ∀ value ∈ edge.children, height value ≤ limit)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (resident : Edges state edges) :
    Complete (fun fuel => group (recurse fuel) clear fuel top edges) state Edges := by
  by_cases smallGroup : edges.length ≤ 4
  · simp only [group, smallGroup, ↓reduceIte]
    exact map_complete (fun fuel => small (recurse fuel)) EdgeResident EdgeResident
      (fun before after extension edge resident => edge_grows before after extension.growth edge resident)
      (fun before after extension edge resident => edge_grows before after extension.growth edge resident) edges
      (fun edge member state facts prepared resident => small_complete recurse limit smaller edge (bounded edge member) state facts prepared resident)
      state facts prepared resident
  · cases edges with
    | nil => simp at smallGroup
    | cons first rest =>
        simp only [group, smallGroup, ↓reduceIte]
        apply bind_complete _ _ state EdgeResident Edges
          (large_complete recurse limit clear top smaller first rest bounded state facts prepared resident)
        intro value after extension available
        exact pure_complete [value] after extension.facts extension.prepared Edges
          (by intro edge member; simpa only [List.mem_singleton.mp member] using available)

/-- A structural source grouping completes all rows before actual parent construction. -/
theorem root_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (clear : Guard → Bool) (top : Guard)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Facts state → Prepared state → Available state value →
      Complete (fun fuel => recurse fuel value) state Available)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat)
    (groups : List (List (EdgeValue Symbol Guard))) (grouping : MergedPhysicalGroupRoot.Grouping edges groups)
    (heightBound : height (.node entry edges depth []) ≤ limit + 1)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Available state (.node entry edges depth [])) :
    Complete (fun fuel => root (recurse fuel) clear fuel top groups) state Available := by
  have original : ∀ group ∈ groups, ∀ edge ∈ group, edge ∈ edges := by
    intro group member edge included
    exact grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
  have rows := map_complete (fun fuel => group (recurse fuel) clear fuel top) Edges Edges
    (fun before after extension _ resident edge member => edge_grows before after extension.growth edge (resident edge member))
    (fun before after extension _ resident edge member => edge_grows before after extension.growth edge (resident edge member)) groups
    (fun group member state facts prepared resident => group_complete recurse limit clear top smaller group
      (fun edge included value inner => by
        have less := child_lt entry edges depth [] edge (original group member edge included) value inner
        omega) state facts prepared resident)
    state facts prepared (fun group member edge included =>
      resident_edges state facts.linked _ available.resident edge (original group member edge included))
  apply bind_complete _ _ state _ Available rows
  intro groups after extension resident
  have available : Edges after groups.flatten := by
    intro edge member
    obtain ⟨group, member, included⟩ := List.mem_flatten.mp member
    exact resident group member edge included
  exact work_complete (makeNode groups.flatten) after extension.prepared Available
    (node_verified groups.flatten after extension.facts available) (makeNode_noNewMu _ after)

/-- Ordinary height derives every recursive call and actual cold filtering derives its comparison bound. -/
theorem worker_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinaryFuel : Nat) (value : Value Symbol Guard)
    (enough : height value ≤ ordinaryFuel) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value) :
    Complete (fun comparisonFuel => worker grouping clear top ordinaryFuel comparisonFuel value) state Available := by
  induction ordinaryFuel generalizing value state with
  | zero =>
      cases value with
      | empty | reference | union | mu => exact pure_complete _ state facts prepared Available available
      | node => simp [height] at enough
  | succ ordinaryFuel ih =>
      cases value with
      | empty | reference | union | mu => exact pure_complete _ state facts prepared Available available
      | node entry edges depth free =>
          by_cases closed : free = []
          · subst free
            simpa only [worker, ↓reduceIte] using root_complete
              (fun comparisonFuel => worker grouping clear top ordinaryFuel comparisonFuel) ordinaryFuel clear top
              (fun value bound state facts prepared available => ih value bound state facts prepared available)
              entry edges depth (grouping edges) (groupsCorrect edges) enough state facts prepared available
          · simpa only [worker, closed, ↓reduceIte] using pure_complete (Value.node entry edges depth free) state facts prepared Available available

/-- The complete cold merge needs no initial warmup, global Ready cache, or recursive callback premise. -/
theorem execute_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value) :
    Complete (fun comparisonFuel => execute grouping clear top comparisonFuel value) state Available :=
  worker_complete grouping groupsCorrect clear top (height value) value (Nat.le_refl _) state facts prepared available

/-- Concrete full-key grouping supplies the cold worker's structural partition contract. -/
theorem source_execute_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value) :
    Complete (fun comparisonFuel => execute MergedSourceGrouping.groups clear top comparisonFuel value) state Available :=
  execute_complete MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear top value state facts prepared available

end MicroCFTA.MergedColdMerge
