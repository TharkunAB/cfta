import MicroCFTA.MergedColdMergeCompletion
import MicroCFTA.MergedColdMergeStability
import MicroCFTA.MergedColdMergeLanguage

/-!
# Finite-language coverage of actual cold merging

Each recursive result covers its inputs in every later common source
cache. Ordinary-height induction derives all recursive certificates.
No initial globally prepared observation cache is required.
-/
namespace MicroCFTA.MergedColdMergeSoundness
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency InternedShallowHeap
open MergedPhysicalWarmup MergedPhysicalLanguage MergedPhysicalUnion MergedPhysicalGroupCalls
open MergedPhysicalGroupEdges MergedPhysicalGroupColumns MergedOrdinaryHeight
open MergedColdMerge MergedColdMergeLanguage Language

/-- A value result retains availability and covers its operands in every later common cache. -/
structure ValuePost [DecidableEq (EdgeKey Symbol Guard)] (meaning : Guard → Term Symbol → Bool)
    (inputs : List (Value Symbol Guard)) (after : State Symbol Guard) (result : Value Symbol Guard) : Prop where
  available : Available after result
  covers : ∀ view, Extension after view → Covers view view meaning inputs result

/-- A returned edge covers all its original rows in every later common cache. -/
structure EdgePost [DecidableEq (EdgeKey Symbol Guard)] (meaning : Guard → Term Symbol → Bool)
    (inputs : List (EdgeValue Symbol Guard)) (after : State Symbol Guard) (result : EdgeValue Symbol Guard) : Prop where
  resident : EdgeResident after result
  covers : ∀ view, Extension after view → ∀ edge ∈ inputs, ∀ term,
    EdgeAccepts view meaning edge term → EdgeAccepts view meaning result term

/-- A returned row list covers every original row in every later common cache. -/
structure RowsPost [DecidableEq (EdgeKey Symbol Guard)] (meaning : Guard → Term Symbol → Bool)
    (inputs : List (EdgeValue Symbol Guard)) (after : State Symbol Guard) (results : List (EdgeValue Symbol Guard)) : Prop where
  resident : Edges after results
  covers : ∀ view, Extension after view → ∀ edge ∈ inputs, ∀ term,
    EdgeAccepts view meaning edge term → ∃ result ∈ results, EdgeAccepts view meaning result term

/-- Later effects preserve a value certificate by composing its observation extension. -/
theorem ValuePost.grows [DecidableEq (EdgeKey Symbol Guard)]
    (meaning : Guard → Term Symbol → Bool) (inputs : List (Value Symbol Guard))
    (before after : State Symbol Guard) (extension : Extension before after)
    (value : Value Symbol Guard) (post : ValuePost meaning inputs before value) : ValuePost meaning inputs after value :=
  ⟨extension.available value post.available, fun view later => post.covers view (extension.trans later)⟩

/-- Later effects preserve a row certificate and its exact resident payload. -/
theorem EdgePost.grows [DecidableEq (EdgeKey Symbol Guard)]
    (meaning : Guard → Term Symbol → Bool) (inputs : List (EdgeValue Symbol Guard))
    (before after : State Symbol Guard) (extension : Extension before after)
    (value : EdgeValue Symbol Guard) (post : EdgePost meaning inputs before value) : EdgePost meaning inputs after value :=
  ⟨edge_grows before after extension.growth value post.resident, fun view later => post.covers view (extension.trans later)⟩

/-- Later effects preserve a list of covered source rows. -/
theorem RowsPost.grows [DecidableEq (EdgeKey Symbol Guard)]
    (meaning : Guard → Term Symbol → Bool) (inputs : List (EdgeValue Symbol Guard))
    (before after : State Symbol Guard) (extension : Extension before after)
    (values : List (EdgeValue Symbol Guard)) (post : RowsPost meaning inputs before values) : RowsPost meaning inputs after values :=
  ⟨fun edge member => edge_grows before after extension.growth edge (post.resident edge member),
    fun view later => post.covers view (extension.trans later)⟩

/-- A completed exact action can retain a stronger proved result property. -/
theorem complete_mono (action : Nat → Action Symbol Guard Output) (state : State Symbol Guard)
    (pre post : State Symbol Guard → Output → Prop) (completed : Complete action state pre)
    (strengthen : ∀ value after, Extension state after → pre after value → post after value) : Complete action state post := by
  obtain ⟨bound, value, after, done, extension, valid⟩ := completed
  exact ⟨bound, value, after, done, extension, strengthen value after extension valid⟩

/-- An actual constructor keeps any property proved for its exact returned value and cache. -/
theorem work_post [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Output)
    (state : State Symbol Guard) (prepared : Prepared state)
    (property post : State Symbol Guard → Output → Prop)
    (verified : InternedNestedFacts.Verified state (InternedNestedConstruction.work computation state) property)
    (unchanged : NoNewMu state (run computation state).2) (valid : post (run computation state).2 (run computation state).1) :
    Complete (fun _ => MergedColdMerge.work computation) state post :=
  ⟨0, (run computation state).1, (run computation state).2, fun _ _ => rfl,
    ⟨verified.facts, prepared.preserve unchanged, verified.growth, verified.history⟩, valid⟩

/-- Ordered cold requests preserve the input position of each result certificate. -/
theorem map_related (call : Nat → Request → Action Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop) (post : State Symbol Guard → Request → Output → Prop)
    (preGrows : ∀ before after, Extension before after → ∀ request, pre before request → pre after request)
    (postGrows : ∀ before after, Extension before after → ∀ request value, post before request value → post after request value)
    (requests : List Request)
    (complete : ∀ request ∈ requests, ∀ state, Facts state → Prepared state → pre state request →
      Complete (fun fuel => call fuel request) state (fun after value => post after request value))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (inputs : ∀ request ∈ requests, pre state request) :
    Complete (fun fuel => MergedColdMerge.map (call fuel) requests) state
      (fun after values => All₂ (post after) requests values) := by
  induction requests generalizing state with
  | nil => exact pure_complete [] state facts prepared _ .nil
  | cons first rest ih =>
      apply bind_complete _ _ state _ _ (complete first List.mem_cons_self state facts prepared (inputs first List.mem_cons_self))
      intro value middle firstExtension valid
      apply bind_complete _ _ middle _ _
        (ih (fun request member => complete request (List.mem_cons_of_mem _ member)) middle firstExtension.facts firstExtension.prepared
          (fun request member => preGrows state middle firstExtension request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after restExtension restValid
      exact pure_complete (value :: values) after restExtension.facts restExtension.prepared _
        (.cons (postGrows middle after restExtension first value valid) restValid)

/-- Singleton-return boundaries cover their exact original input without effects. -/
theorem boundary_post [DecidableEq (EdgeKey Symbol Guard)] (meaning : Guard → Term Symbol → Bool)
    (state : State Symbol Guard) (value : Value Symbol Guard) (available : Available state value) :
    ValuePost meaning [value] state value := by
  refine ⟨available, ?_⟩
  intro view extension original member term accepted
  simpa only [List.mem_singleton.mp member] using accepted

/-- Retained-column branches derive common-cache coverage from smaller recursive results. -/
theorem retained_complete [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (meaning : Guard → Term Symbol → Bool)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Facts state → Prepared state → Available state value →
      Complete (fun fuel => recurse fuel value) state (ValuePost meaning [value]))
    (retained : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Values state retained) (closed : ∀ value ∈ retained, value.free = [])
    (bounded : ∀ value ∈ retained, height value ≤ limit) :
    Complete (fun fuel => retainedColumn (recurse fuel) retained) state (ValuePost meaning retained) := by
  have branches (values : List (Value Symbol Guard)) (available : Values state values)
      (closed : ∀ value ∈ values, value.free = []) (bounded : ∀ value ∈ values, height value ≤ limit) :
      Complete (fun fuel => if values.any recursiveBoundary then MergedColdMerge.work (makeUnion values)
        else MergedColdMerge.bind (MergedColdMerge.work (ordinaryUnion values)) (recurse fuel)) state (ValuePost meaning values) := by
    by_cases boundary : values.any recursiveBoundary = true
    · simp only [boundary, ↓reduceIte]
      have verified := union_verified values state facts available
      apply work_post (makeUnion values) state prepared Available _ verified (makeUnion_noNewMu values state)
      refine ⟨verified.result _ _ rfl, ?_⟩
      intro view extension value member term accepted
      exact (makeUnion_common state view facts values available meaning term).mpr ⟨value, member, accepted⟩
    · simp only [boundary, Bool.false_eq_true, ↓reduceIte]
      have ordinary := fun value member => ordinary_operand value (closed value member)
        (by simpa using (List.any_eq_false.mp (Bool.eq_false_iff.mpr boundary)) value member)
      have resident : Edges state (values.flatMap nodeEdges) := by
        intro edge member
        obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
        exact resident_edges state facts.linked value (available value present).resident edge included
      have verified := node_verified (values.flatMap nodeEdges) state facts resident
      let built := run (ordinaryUnion values) state
      have extension : Extension state built.2 :=
        ⟨verified.facts, prepared.preserve (makeNode_noNewMu _ state), verified.growth, verified.history⟩
      have boundHeight := ordinaryUnion_bound values state facts.coherent facts.linked
        (fun value member => (available value member).resident) limit bounded
      obtain ⟨bound, result, after, done, later, post⟩ :=
        smaller built.1 boundHeight built.2 extension.facts extension.prepared (verified.result _ _ rfl)
      refine ⟨bound, result, after, ?_, extension.trans later, post.available, ?_⟩
      · intro fuel enough
        simpa only [MergedColdMerge.bind, MergedColdMerge.work, MergedSourceComparison.Result.bind] using done fuel enough
      · intro view next
        exact ordinaryUnion_covers state view facts values available ordinary meaning result (post.covers view next)
  cases retained with
  | nil => exact branches [] available closed bounded
  | cons first rest =>
      cases rest with
      | nil => exact pure_complete first state facts prepared _ (boundary_post meaning state first (available first List.mem_cons_self))
      | cons second tail => exact branches (first :: second :: tail) available closed bounded

/-- Actual stateful selection and retained-column construction cover every original column operand. -/
theorem column_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Facts state → Prepared state → Available state value →
      Complete (fun fuel => recurse fuel value) state (ValuePost meaning [value]))
    (inputs : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Values state inputs) (closed : ∀ value ∈ inputs, value.free = [])
    (bounded : ∀ value ∈ inputs, height value ≤ limit) :
    Complete (fun fuel => column (recurse fuel) clear fuel inputs) state (ValuePost meaning inputs) := by
  obtain ⟨bound, retained, middle, selected, verified, middlePrepared⟩ :=
    MergedSourceSelection.select_complete clear inputs state facts prepared available
  have selectedDone := selected bound (Nat.le_refl _)
  have subset := MergedSourceSelection.select_subset clear bound inputs state retained middle selectedDone
  have firstExtension : Extension state middle := ⟨verified.facts, middlePrepared, verified.growth, verified.history⟩
  obtain ⟨later, result, after, done, nextExtension, post⟩ :=
    retained_complete recurse limit meaning smaller retained middle verified.facts middlePrepared
      (fun value member => firstExtension.available value (available value (subset value member)))
      (fun value member => closed value (subset value member)) (fun value member => bounded value (subset value member))
  refine ⟨max bound later, result, after, ?_, firstExtension.trans nextExtension, post.available, ?_⟩
  · intro fuel enough
    simp only [column, MergedColdMerge.bind, selected fuel (Nat.le_trans (Nat.le_max_left _ _) enough),
      MergedSourceComparison.Result.bind, done fuel (Nat.le_trans (Nat.le_max_right _ _) enough)]
  · intro view finalExtension
    have sourceExtension := firstExtension.trans (nextExtension.trans finalExtension)
    exact selected_covers clear bound inputs state facts prepared available retained middle view selectedDone
      (grows_trans nextExtension.growth finalExtension.growth) finalExtension.facts finalExtension.prepared
      (fun value member => sourceExtension.available value (available value member)) meaning clearTrue result
      (post.covers view finalExtension)

/-- Actual small-edge construction covers its original row after all ordered child effects. -/
theorem small_complete [DecidableEq (EdgeKey Symbol Guard)]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (meaning : Guard → Term Symbol → Bool)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Facts state → Prepared state → Available state value →
      Complete (fun fuel => recurse fuel value) state (ValuePost meaning [value]))
    (edge : EdgeValue Symbol Guard) (bounded : ∀ value ∈ edge.children, height value ≤ limit)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (resident : EdgeResident state edge) :
    Complete (fun fuel => small (recurse fuel) edge) state (EdgePost meaning [edge]) := by
  have children := map_related recurse Available (fun after value result => ValuePost meaning [value] after result)
    (fun _ _ extension value available => extension.available value available)
    (fun before after extension value result post => post.grows meaning [value] before after extension result)
    edge.children (fun value member state facts prepared available => smaller value (bounded value member) state facts prepared available)
    state facts prepared (facts.cached.edges edge.entry.key edge resident)
  apply bind_complete _ _ state _ _ children
  intro values middle firstExtension related
  have available : Values middle values := EnumerationSoundness.all₂_outputs (Available middle) _ _
    (related.imp (fun _ _ post => post.available))
  have verified := edge_verified edge.entry.key.symbol edge.entry.key.constraint values middle firstExtension.facts available
  have unchanged : NoNewMu middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 := by
    intro key entry body depth ordinary stored
    exact stored
  have constructed : Extension middle (run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle).2 :=
    ⟨verified.facts, firstExtension.prepared.preserve unchanged, verified.growth, verified.history⟩
  apply work_post _ middle firstExtension.prepared EdgeResident _ verified unchanged
  refine ⟨verified.result _ _ rfl, ?_⟩
  intro view next original member term accepted
  rw [List.mem_singleton.mp member] at accepted
  exact small_edge_covers middle view firstExtension.facts edge values available meaning
    (related.imp (fun _ _ post => post.covers view (constructed.trans next))) term accepted

/-- Actual large-edge construction covers each original row after cold column selection and recursive calls. -/
theorem large_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Facts state → Prepared state → Available state value →
      Complete (fun fuel => recurse fuel value) state (ValuePost meaning [value]))
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (closed : ∀ edge ∈ first :: rest, ∀ value ∈ edge.children, value.free = [])
    (bounded : ∀ edge ∈ first :: rest, ∀ value ∈ edge.children, height value ≤ limit)
    (keys : SameKey (first :: rest))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (resident : Edges state (first :: rest)) :
    Complete (fun fuel => large (recurse fuel) clear fuel top first rest) state (EdgePost meaning (first :: rest)) := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  have children := map_related (fun fuel => column (recurse fuel) clear fuel) Values
    (fun after column result => ValuePost meaning column after result)
    (fun _ _ extension _ available value member => extension.available value (available value member))
    (fun before after extension column result post => post.grows meaning column before after extension result) columns
    (fun column member state facts prepared available => column_complete recurse limit clear meaning clearTrue smaller column state facts prepared available
      (fun value included => by obtain ⟨edge, outer, inner⟩ := original column member value included; exact closed edge outer value inner)
      (fun value included => by obtain ⟨edge, outer, inner⟩ := original column member value included; exact bounded edge outer value inner))
    state facts prepared (fun column member value included => by
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact facts.cached.edges edge.entry.key edge (resident edge outer) value inner)
  apply bind_complete _ _ state _ _ children
  intro values middle firstExtension related
  have available : Values middle values := EnumerationSoundness.all₂_outputs (Available middle) _ _
    (related.imp (fun _ _ post => post.available))
  have verified := edge_verified first.entry.key.symbol top values middle firstExtension.facts available
  have unchanged : NoNewMu middle (run (makeEdge first.entry.key.symbol top values) middle).2 := by
    intro key entry body depth ordinary stored
    exact stored
  have constructed : Extension middle (run (makeEdge first.entry.key.symbol top values) middle).2 :=
    ⟨verified.facts, firstExtension.prepared.preserve unchanged, verified.growth, verified.history⟩
  apply work_post _ middle firstExtension.prepared EdgeResident _ verified unchanged
  refine ⟨verified.result _ _ rfl, ?_⟩
  intro view next edge member term accepted
  exact large_edge_covers middle view firstExtension.facts first rest keys values available meaning top topTrue
    (related.imp (fun _ _ post => post.covers view (constructed.trans next))) edge member term accepted

/-- Both actual threshold branches cover every original group row in every later common cache. -/
theorem group_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Facts state → Prepared state → Available state value →
      Complete (fun fuel => recurse fuel value) state (ValuePost meaning [value]))
    (edges : List (EdgeValue Symbol Guard))
    (closed : ∀ edge ∈ edges, ∀ value ∈ edge.children, value.free = [])
    (bounded : ∀ edge ∈ edges, ∀ value ∈ edge.children, height value ≤ limit) (keys : SameKey edges)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (resident : Edges state edges) :
    Complete (fun fuel => group (recurse fuel) clear fuel top edges) state (RowsPost meaning edges) := by
  by_cases smallGroup : edges.length ≤ 4
  · simp only [group, smallGroup, ↓reduceIte]
    have children := map_related (fun fuel => small (recurse fuel)) EdgeResident
      (fun after edge result => EdgePost meaning [edge] after result)
      (fun before after extension edge resident => edge_grows before after extension.growth edge resident)
      (fun before after extension edge result post => post.grows meaning [edge] before after extension result) edges
      (fun edge member state facts prepared resident => small_complete recurse limit meaning smaller edge (bounded edge member)
        state facts prepared resident) state facts prepared resident
    apply complete_mono _ state _ _ children
    intro values after extension related
    refine ⟨EnumerationSoundness.all₂_outputs (EdgeResident after) _ _ (related.imp (fun _ _ post => post.resident)), ?_⟩
    intro view next edge member term accepted
    obtain ⟨result, included, post⟩ := SymbolicSmartRows.all₂_child _ _ _ related edge member
    exact ⟨result, included, post.covers view next edge List.mem_cons_self term accepted⟩
  · cases edges with
    | nil => simp at smallGroup
    | cons first rest =>
        simp only [group, smallGroup, ↓reduceIte]
        apply bind_complete _ _ state _ _
          (large_complete recurse limit clear meaning clearTrue top topTrue smaller first rest closed bounded keys state facts prepared resident)
        intro edge after extension post
        apply pure_complete [edge] after extension.facts extension.prepared
        refine ⟨?_, ?_⟩
        · intro result member
          simpa only [List.mem_singleton.mp member] using post.resident
        · intro view next original member term accepted
          exact ⟨edge, List.mem_cons_self, post.covers view next original member term accepted⟩

/-- Actual grouping and parent construction cover the original closed ordinary root. -/
theorem root_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (limit : Nat)
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (smaller : ∀ value, height value ≤ limit → ∀ state, Facts state → Prepared state → Available state value →
      Complete (fun fuel => recurse fuel value) state (ValuePost meaning [value]))
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat)
    (groups : List (List (EdgeValue Symbol Guard))) (grouping : MergedPhysicalGroupRoot.Grouping edges groups)
    (heightBound : height (.node entry edges depth []) ≤ limit + 1)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Available state (.node entry edges depth [])) :
    Complete (fun fuel => root (recurse fuel) clear fuel top groups) state (ValuePost meaning [.node entry edges depth []]) := by
  have original : ∀ group ∈ groups, ∀ edge ∈ group, edge ∈ edges := by
    intro group member edge included
    exact grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
  have closedOriginal := fun edge included value inner =>
    closed_child state facts.coherent entry edges depth [] available.resident rfl edge included value inner
  have rows := map_related (fun fuel => group (recurse fuel) clear fuel top) Edges
    (fun after group result => RowsPost meaning group after result)
    (fun before after extension _ resident edge member => edge_grows before after extension.growth edge (resident edge member))
    (fun before after extension group result post => post.grows meaning group before after extension result) groups
    (fun group member state facts prepared resident => group_complete recurse limit clear meaning clearTrue top topTrue smaller group
      (fun edge included value inner => closedOriginal edge (original group member edge included) value inner)
      (fun edge included value inner => by
        have less := child_lt entry edges depth [] edge (original group member edge included) value inner
        omega)
      (grouping.keys edges groups group member) state facts prepared resident)
    state facts prepared (fun group member edge included =>
      resident_edges state facts.linked _ available.resident edge (original group member edge included))
  apply bind_complete _ _ state _ _ rows
  intro results middle firstExtension related
  have allResident : ∀ group ∈ results, Edges middle group := EnumerationSoundness.all₂_outputs (Edges middle) _ _
    (related.imp (fun _ _ post => post.resident))
  have resident : Edges middle results.flatten := by
    intro edge member
    obtain ⟨group, member, included⟩ := List.mem_flatten.mp member
    exact allResident group member edge included
  have verified := node_verified results.flatten middle firstExtension.facts resident
  have constructed : Extension middle (run (makeNode results.flatten) middle).2 :=
    ⟨verified.facts, firstExtension.prepared.preserve (makeNode_noNewMu _ middle), verified.growth, verified.history⟩
  apply work_post _ middle firstExtension.prepared Available _ verified (makeNode_noNewMu _ middle)
  refine ⟨verified.result _ _ rfl, ?_⟩
  intro view next
  apply node_covers middle view firstExtension.facts entry edges depth [] results.flatten resident meaning
  intro edge member term accepted
  obtain ⟨group, included, selected⟩ := List.mem_flatten.mp (grouping.partition.mem_iff.mpr member)
  obtain ⟨returned, output, post⟩ := SymbolicSmartRows.all₂_child _ _ _ related group included
  obtain ⟨result, resultIn, covered⟩ := post.covers view (constructed.trans next) edge selected term accepted
  exact ⟨result, List.mem_flatten.mpr ⟨returned, output, resultIn⟩, covered⟩

/-- Ordinary-height induction derives complete cold execution and all finite-language coverage certificates. -/
theorem worker_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (ordinaryFuel : Nat) (value : Value Symbol Guard) (enough : height value ≤ ordinaryFuel)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Available state value) :
    Complete (fun comparisonFuel => worker grouping clear top ordinaryFuel comparisonFuel value) state (ValuePost meaning [value]) := by
  induction ordinaryFuel generalizing value state with
  | zero =>
      cases value with
      | empty | reference | union | mu => exact pure_complete _ state facts prepared _ (boundary_post meaning state _ available)
      | node => simp [height] at enough
  | succ ordinaryFuel ih =>
      cases value with
      | empty | reference | union | mu => exact pure_complete _ state facts prepared _ (boundary_post meaning state _ available)
      | node entry edges depth free =>
          by_cases closed : free = []
          · subst free
            simpa only [worker, ↓reduceIte] using root_complete
              (fun comparisonFuel => worker grouping clear top ordinaryFuel comparisonFuel) ordinaryFuel clear meaning clearTrue top topTrue
              (fun value bound state facts prepared available => ih value bound state facts prepared available)
              entry edges depth (grouping edges) (groupsCorrect edges) enough state facts prepared available
          · simpa only [worker, closed, ↓reduceIte] using pure_complete (Value.node entry edges depth free) state facts prepared _
              (boundary_post meaning state _ available)

/-- Complete actual cold merging covers the input in its returned cache and every later common cache. -/
theorem execute_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value) :
    ∃ bound result after, (∀ comparisonFuel, bound ≤ comparisonFuel →
      execute grouping clear top comparisonFuel value state = .done result after) ∧
      Extension state after ∧ Available after result ∧
      (∀ term, EpsilonUnion.Accepts (graph after meaning) value term → EpsilonUnion.Accepts (graph after meaning) result term) ∧
      ∀ view, Extension after view → ∀ term,
        EpsilonUnion.Accepts (graph view meaning) value term → EpsilonUnion.Accepts (graph view meaning) result term := by
  obtain ⟨bound, result, after, done, extension, post⟩ := worker_complete grouping groupsCorrect clear meaning clearTrue top topTrue
    (height value) value (Nat.le_refl _) state facts prepared available
  exact ⟨bound, result, after, done, extension, post.available,
    post.covers after (.refl after extension.facts extension.prepared) value List.mem_cons_self,
    fun view later => post.covers view later value List.mem_cons_self⟩

/-- Concrete full-key source grouping discharges the grouping premise of cold merge language inclusion. -/
theorem source_execute_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value) :
    ∃ bound result after, (∀ comparisonFuel, bound ≤ comparisonFuel →
      execute MergedSourceGrouping.groups clear top comparisonFuel value state = .done result after) ∧
      Extension state after ∧ Available after result ∧
      (∀ term, EpsilonUnion.Accepts (graph after meaning) value term → EpsilonUnion.Accepts (graph after meaning) result term) ∧
      ∀ view, Extension after view → ∀ term,
        EpsilonUnion.Accepts (graph view meaning) value term → EpsilonUnion.Accepts (graph view meaning) result term :=
  execute_complete MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear meaning clearTrue top topTrue
    value state facts prepared available

/-- Every successful pair of fuel bounds has the derived common-cache language guarantee. -/
theorem successful_sound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupsCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value)
    (ordinary comparison : Nat) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : worker grouping clear top ordinary comparison value state = .done result after) :
    Extension state after ∧ Available after result ∧
      (∀ term, EpsilonUnion.Accepts (graph after meaning) value term → EpsilonUnion.Accepts (graph after meaning) result term) ∧
      ∀ view, Extension after view → ∀ term,
        EpsilonUnion.Accepts (graph view meaning) value term → EpsilonUnion.Accepts (graph view meaning) result term := by
  obtain ⟨bound, output, final, completed, extension, resident, covered, later⟩ :=
    execute_complete grouping groupsCorrect clear meaning clearTrue top topTrue value state facts prepared available
  have same := MergedColdMergeStability.successful_results_eq grouping clear top ordinary (height value) comparison bound value state
    result output after final done (completed bound (Nat.le_refl _))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨extension, resident, covered, later⟩

/-- Every successful concrete source-grouped cold run includes its original finite-term language. -/
theorem source_successful_sound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value)
    (ordinary comparison : Nat) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : worker MergedSourceGrouping.groups clear top ordinary comparison value state = .done result after) :
    Extension state after ∧ Available after result ∧
      (∀ term, EpsilonUnion.Accepts (graph after meaning) value term → EpsilonUnion.Accepts (graph after meaning) result term) ∧
      ∀ view, Extension after view → ∀ term,
        EpsilonUnion.Accepts (graph view meaning) value term → EpsilonUnion.Accepts (graph view meaning) result term :=
  successful_sound MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear meaning clearTrue top topTrue
    value state facts prepared available ordinary comparison result after done

end MicroCFTA.MergedColdMergeSoundness
