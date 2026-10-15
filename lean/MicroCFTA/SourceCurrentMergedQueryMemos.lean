import MicroCFTA.SourceCurrentSubsumesQueryMemos
import MicroCFTA.SourceCurrentMergedHeapEffects

/-!
# Global unfolding receipts through actual merging

Each completed merge records its ordered comparison reads and literal
constructor work. The three returned tables retain their coherence. Only
the unfolding table can change. This graph does not model the separate
merge-result memo or runtime publication.
-/
namespace MicroCFTA.SourceCurrentMergedQueryMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open MergedSourceComparison (Result)
open SourceMergedComparisonEffects (bind_done)
open MergedColdMerge (Action bind work map retainedColumn small)
open SourceMergedContracts
open SourceCurrentSubsumesQueryMemos (Reads Effect)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private theorem effect_trans [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {memos saved final : Memos}
    (first : Effect before middle memos saved) (second : Effect middle after saved final) :
    Effect before after memos final :=
  ⟨first.keeps.trans second.keeps, second.semantic, second.costs, second.valid,
    extends_trans first.retained second.retained, second.query.trans first.query⟩

private def Post [DecidableEq (EdgeKey Symbol Guard)]
    (action : Action Symbol Guard Output) (before : State Symbol Guard)
    (result : Output) (after : State Symbol Guard) (memos : Memos) : Prop :=
  ∃ saved, Reads action before result after memos saved ∧ Effect before after memos saved

private theorem pure_memos [DecidableEq (EdgeKey Symbol Guard)]
    (value result : Output) (before after : State Symbol Guard)
    (done : Result.done value before = Result.done result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (memos : Memos) (valid : Valid before memos) :
    Post (MergedColdMerge.pure value) before result after memos := by
  cases done
  exact ⟨memos, .pure value before memos,
    ⟨pure_keeps _ semantic.ready, semantic, costs, valid, extends_refl _, rfl⟩⟩

private theorem work_memos [DecidableEq (EdgeKey Symbol Guard)]
    (job : Work Symbol Guard Output) (before : State Symbol Guard) (semantic : SemanticReady before)
    (checked : SourceMergedComparisonEffects.Effect before (run job before).2)
    (costs : CostHeap (run job before).2) (memos : Memos) (valid : Valid before memos) :
    Post (work job) before (run job before).1 (run job before).2 memos :=
  ⟨memos, .work job before memos,
    ⟨checked.1, checked.2, costs, SourceQueryUnfoldMemo.valid_grows before _ semantic checked.1 memos valid,
      extends_refl _, rfl⟩⟩

private def RecurseMemos [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ value before, SemanticReady before → CostHeap before → Available before value → value.free = [] →
    ∀ result after, call value before = .done result after → ∀ memos, Valid before memos →
      Post (call value) before result after memos

private theorem map_memos [DecidableEq (EdgeKey Symbol Guard)]
    (call : Request → Action Symbol Guard Output) (pre : State Symbol Guard → Request → Prop)
    (preGrows : ∀ before after, Keeps before after → ∀ request, pre before request → pre after request)
    (requests : List Request)
    (callback : ∀ request ∈ requests, ∀ before, SemanticReady before → CostHeap before → pre before request →
      ∀ result after, call request before = .done result after → ∀ memos, Valid before memos →
        Post (call request) before result after memos)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : ∀ request ∈ requests, pre before request)
    (results : List Output) (after : State Symbol Guard) (done : map call requests before = .done results after)
    (memos : Memos) (valid : Valid before memos) : Post (map call requests) before results after memos := by
  induction requests generalizing before results after memos with
  | nil => exact pure_memos [] results before after done semantic costs memos valid
  | cons request requests ih =>
      obtain ⟨first, middle, called, later⟩ := (bind_done _ _ results after).mp done
      obtain ⟨saved, own, checked⟩ := callback request List.mem_cons_self before semantic costs
        (inputs request List.mem_cons_self) first middle called memos valid
      obtain ⟨rest, finalHeap, mapped, returned⟩ := (bind_done _ _ results after).mp later
      obtain ⟨next, tail, tailEffects⟩ := ih (fun request member => callback request (List.mem_cons_of_mem _ member))
        middle checked.semantic checked.costs
        (fun request member => preGrows before middle checked.keeps request (inputs request (List.mem_cons_of_mem _ member)))
        rest finalHeap mapped saved checked.valid
      obtain ⟨final, resultReads, resultEffects⟩ := pure_memos (first :: rest) results finalHeap after returned
        tailEffects.semantic tailEffects.costs next tailEffects.valid
      exact ⟨final, .bind own (.bind tail resultReads), effect_trans checked (effect_trans tailEffects resultEffects)⟩

private theorem retained_memos [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (callback : RecurseMemos call)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before inputs) (closed : ClosedValues inputs)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : retainedColumn call inputs before = .done result after) (memos : Memos) (valid : Valid before memos) :
    Post (retainedColumn call inputs) before result after memos := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values) (closed : ClosedValues values)
      (done : (if values.any MergedOrdinaryHeight.recursiveBoundary then work (makeUnion values)
        else bind (work (MergedOrdinaryHeight.ordinaryUnion values)) call) before = .done result after) :
      Post (if values.any MergedOrdinaryHeight.recursiveBoundary then work (makeUnion values)
        else bind (work (MergedOrdinaryHeight.ordinaryUnion values)) call) before result after memos := by
    by_cases boundary : values.any MergedOrdinaryHeight.recursiveBoundary = true
    · simp only [boundary, ite_true] at done ⊢
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      exact work_memos (makeUnion values) before semantic (SourceMergedCache.union values before semantic available closed).1
        (InternedFreshOrdinaryCostHeap.preserve before _ costs (InternedShallowHeap.makeUnion_noNewMu values before)) memos valid
    · simp only [boundary, Bool.false_eq_true, ite_false] at done ⊢
      obtain ⟨united, middle, constructed, called⟩ := (bind_done _ _ result after).mp done
      have parts := Result.done.inj constructed
      cases parts.1; cases parts.2
      have checked := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
        values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      obtain ⟨saved, own, effects⟩ := work_memos (MergedOrdinaryHeight.ordinaryUnion values) before semantic checked.1
        (InternedFreshOrdinaryCostHeap.preserve before _ costs (InternedShallowHeap.makeNode_noNewMu _ before)) memos valid
      obtain ⟨final, later, finalEffects⟩ := callback _ _ effects.semantic effects.costs checked.2.1 checked.2.2.1
        result after called saved effects.valid
      exact ⟨final, .bind own later, effect_trans effects finalEffects⟩
  cases inputs with
  | nil => exact branches [] available closed done
  | cons first rest =>
      cases rest with
      | nil => exact pure_memos first result before after done semantic costs memos valid
      | cons second rest => exact branches (first :: second :: rest) available closed done

private theorem column_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)) (callback : RecurseMemos call)
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before inputs) (closed : ClosedValues inputs)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.column call clear fuel inputs before = .done result after) (memos : Memos) (valid : Valid before memos) :
    Post (SourceMergedWorker.column call clear fuel inputs) before result after memos := by
  obtain ⟨selected, middle, filtered, called⟩ := (bind_done _ _ result after).mp done
  have checked := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
    (fun _ _ _ => rfl) inputs before semantic available closed selected middle filtered
  obtain ⟨saved, own, effects⟩ := SourceCurrentSubsumesQueryMemos.select_memos clear fuel inputs before semantic costs
    available closed selected middle filtered memos valid
  obtain ⟨final, later, finalEffects⟩ := retained_memos call callback selected middle effects.semantic effects.costs
    checked.2.1 checked.2.2.1 result after called saved effects.valid
  exact ⟨final, .bind own later, effect_trans effects finalEffects⟩

private theorem small_memos [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (callback : RecurseMemos call)
    (edge : EdgeValue Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (resident : EdgeResident before edge) (closed : ClosedValues edge.children)
    (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : small call edge before = .done result after) (memos : Memos) (valid : Valid before memos) :
    Post (small call edge) before result after memos := by
  obtain ⟨values, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  obtain ⟨saved, own, effects⟩ := map_memos call (fun state value => Available state value ∧ value.free = [])
    (fun _ _ keeps value input => ⟨keeps.available value input.1, input.2⟩) edge.children
    (fun value _ state ready heap input result final actual => callback value state ready heap input.1 input.2 result final actual)
    before semantic costs (fun value member => ⟨available value member, closed value member⟩) values middle mapped memos valid
  have checked := SourceMergedContracts.children_done call (fun _ _ => true) (fun _ _ => False) law
    edge.children before semantic available closed values middle mapped
  have valuesAvailable : Values middle values := EnumerationSoundness.all₂_outputs _ _ _ (checked.2.imp (fun _ _ post => post.available))
  have constructed := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values middle effects.semantic.ready valuesAvailable
  have parts := Result.done.inj made
  cases parts.1; cases parts.2
  obtain ⟨final, later, finalEffects⟩ := work_memos (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle effects.semantic
    ⟨constructed.1, SourceEqualityRequiredSemanticCache.edge _ _ _ middle effects.semantic valuesAvailable⟩ effects.costs saved effects.valid
  exact ⟨final, .bind own later, effect_trans effects finalEffects⟩

private theorem large_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (callback : RecurseMemos call)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before (first :: rest)) (closed : ClosedEdges (first :: rest))
    (result : EdgeValue Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.large call clear fuel top first rest before = .done result after)
    (memos : Memos) (valid : Valid before memos) :
    Post (SourceMergedWorker.large call clear fuel top first rest) before result after memos := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  have inputs : ∀ column ∈ columns, Values before column ∧ ClosedValues column := by
    intro column member
    constructor
    · intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner
    · intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact closed edge outer value inner
  obtain ⟨values, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  obtain ⟨saved, own, effects⟩ := map_memos (SourceMergedWorker.column call clear fuel)
    (fun state values => Values state values ∧ ClosedValues values)
    (fun _ _ keeps _ input => ⟨(fun value member => keeps.available value (input.1 value member)), input.2⟩) columns
    (fun values _ state ready heap input result final actual => column_memos call callback clear fuel values state ready heap
      input.1 input.2 result final actual) before semantic costs inputs values middle mapped memos valid
  have checked := SourceMergedContracts.map_done (SourceMergedWorker.column call clear fuel)
    (fun state inputs => Values state inputs ∧ ClosedValues inputs)
    (fun state inputs result => ValuePost (fun _ _ => true) (fun _ _ => False) inputs state result)
    (fun _ _ effects _ inputs => ⟨(fun value member => effects.1.available value (inputs.1 value member)), inputs.2⟩)
    (fun _ _ effects _ _ post => post.grows effects) columns
    (fun inputs _ state ready input result final actual => SourceMergedColumns.column_done call clear fuel
      (fun _ _ => true) (fun _ _ => False) (fun _ _ _ => rfl) law inputs state ready input.1 input.2 result final actual)
    before semantic inputs values middle mapped
  have valuesAvailable : Values middle values := EnumerationSoundness.all₂_outputs _ _ _ (checked.2.imp (fun _ _ post => post.available))
  have constructed := SourceEqualityRequiredCache.edge first.entry.key.symbol top values middle effects.semantic.ready valuesAvailable
  have parts := Result.done.inj made
  cases parts.1; cases parts.2
  obtain ⟨final, later, finalEffects⟩ := work_memos (makeEdge first.entry.key.symbol top values) middle effects.semantic
    ⟨constructed.1, SourceEqualityRequiredSemanticCache.edge _ _ _ middle effects.semantic valuesAvailable⟩ effects.costs saved effects.valid
  exact ⟨final, .bind own later, effect_trans effects finalEffects⟩

private theorem group_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (callback : RecurseMemos call)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges) (closed : ClosedEdges edges)
    (results : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedWorker.group call clear fuel top edges before = .done results after)
    (memos : Memos) (valid : Valid before memos) :
    Post (SourceMergedWorker.group call clear fuel top edges) before results after memos := by
  unfold SourceMergedWorker.group at done ⊢
  split at done
  · rename_i short
    simp only [ite_eq_left short]
    exact map_memos (small call) (fun state edge => EdgeResident state edge ∧ ClosedValues edge.children)
      (fun _ _ keeps edge input => ⟨InternedEdgeResidency.edge_grows _ _ keeps.growth edge input.1, input.2⟩) edges
      (fun edge _ state ready heap input result final actual => small_memos call law callback edge state ready heap input.1 input.2 result final actual)
      before semantic costs (fun edge member => ⟨resident edge member, closed edge member⟩) results after done memos valid
  · rename_i long
    simp only [ite_eq_right long]
    cases edges with
    | nil => simp at long
    | cons first rest =>
        obtain ⟨result, finalHeap, made, returned⟩ := (bind_done _ _ results after).mp done
        obtain ⟨saved, own, effects⟩ := large_memos call law callback clear fuel top first rest before semantic costs resident closed result finalHeap made memos valid
        obtain ⟨final, later, finalEffects⟩ := pure_memos [result] results finalHeap after returned effects.semantic effects.costs saved effects.valid
        exact ⟨final, .bind own later, effect_trans effects finalEffects⟩

private theorem root_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (law : RecurseLaw call (fun _ _ => true) (fun _ _ => False)) (callback : RecurseMemos call)
    (clear : Guard → Bool) (fuel : Nat) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) (groups : List (List (EdgeValue Symbol Guard)))
    (grouping : MergedPhysicalGroupRoot.Grouping edges groups) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges) (closed : ClosedEdges edges)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.root call clear fuel top groups before = .done result after)
    (memos : Memos) (valid : Valid before memos) :
    Post (SourceMergedWorker.root call clear fuel top groups) before result after memos := by
  have original (group : List (EdgeValue Symbol Guard)) (member : group ∈ groups) (edge : EdgeValue Symbol Guard) (included : edge ∈ group) : edge ∈ edges :=
    grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
  have inputs : ∀ group ∈ groups, Edges before group ∧ ClosedEdges group :=
    fun group member => ⟨(fun edge included => resident edge (original group member edge included)),
      (fun edge included => closed edge (original group member edge included))⟩
  obtain ⟨rows, middle, mapped, made⟩ := (bind_done _ _ result after).mp done
  obtain ⟨saved, own, effects⟩ := map_memos (SourceMergedWorker.group call clear fuel top)
    (fun state edges => Edges state edges ∧ ClosedEdges edges)
    (fun _ _ keeps _ input => ⟨(fun edge member => InternedEdgeResidency.edge_grows _ _ keeps.growth edge (input.1 edge member)), input.2⟩) groups
    (fun group _ state ready heap input result final actual => group_memos call law callback clear fuel top group state ready heap input.1 input.2 result final actual)
    before semantic costs inputs rows middle mapped memos valid
  have checked := SourceMergedContracts.map_done (SourceMergedWorker.group call clear fuel top)
    (fun state edges => Edges state edges ∧ ClosedEdges edges)
    (fun state edges results => RowsPost (fun _ _ => true) (fun _ _ => False) edges state results)
    (fun _ _ effects _ input => ⟨(fun edge member => InternedEdgeResidency.edge_grows _ _ effects.1.growth edge (input.1 edge member)), input.2⟩)
    (fun _ _ effects _ _ post => post.grows effects) groups
    (fun group member state ready input result final actual => SourceMergedGroups.group_done call clear fuel
      (fun _ _ => true) (fun _ _ => False) (fun _ _ _ => rfl) law top (fun _ => rfl)
      group (grouping.keys edges groups group member) state ready input.1 input.2 result final actual)
    before semantic inputs rows middle mapped
  have rowsResident : ∀ own ∈ rows, Edges middle own := EnumerationSoundness.all₂_outputs _ _ _ (checked.2.imp (fun _ _ post => post.resident))
  have rowsClosed : ∀ own ∈ rows, ClosedEdges own := EnumerationSoundness.all₂_outputs _ _ _ (checked.2.imp (fun _ _ post => post.closed))
  have flatResident : Edges middle rows.flatten := by
    intro edge member
    obtain ⟨own, member, included⟩ := List.mem_flatten.mp member
    exact rowsResident own member edge included
  have flatClosed : ClosedEdges rows.flatten := by
    intro edge member
    obtain ⟨own, member, included⟩ := List.mem_flatten.mp member
    exact rowsClosed own member edge included
  have constructed := SourceEqualityRequiredCache.node rows.flatten middle effects.semantic.ready flatResident flatClosed
  have parts := Result.done.inj made
  cases parts.1; cases parts.2
  obtain ⟨final, later, finalEffects⟩ := work_memos (makeNode rows.flatten) middle effects.semantic
    ⟨constructed.1, SourceEqualityRequiredSemanticCache.node _ middle effects.semantic flatResident flatClosed⟩
    (InternedFreshOrdinaryCostHeap.preserve middle _ effects.costs (InternedShallowHeap.makeNode_noNewMu rows.flatten middle)) saved effects.valid
  exact ⟨final, .bind own later, effect_trans effects finalEffects⟩

private theorem worker_closed_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupingCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinaryFuel comparisonFuel : Nat) :
    RecurseMemos (SourceMergedWorker.worker grouping clear top ordinaryFuel comparisonFuel) := by
  induction ordinaryFuel with
  | zero =>
      intro value before semantic costs available closed result after done memos valid
      cases value with
      | node entry edges depth free =>
          simp only [Value.free] at closed
          simp only [SourceMergedWorker.worker, closed, ite_true] at done
          cases done
      | empty | reference | mu | union => exact pure_memos _ result before after done semantic costs memos valid
  | succ remaining ih =>
      intro value before semantic costs available closed result after done memos valid
      cases value with
      | node entry edges depth free =>
          have facts := semantic.ready.semantic.1.normal.facts
          have resident : Edges before edges := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
          have rowsClosed : ClosedEdges edges := fun edge member child included =>
            MergedOrdinaryHeight.closed_child before facts.coherent entry edges depth free available.resident closed edge member child included
          have law := SourceMergedSoundness.worker_done grouping groupingCorrect clear top (fun _ _ => true) (fun _ _ => False)
            (fun _ _ _ => rfl) (fun _ => rfl) remaining comparisonFuel
          have completed := root_memos _ law ih clear comparisonFuel top edges (grouping edges) (groupingCorrect edges)
            before semantic costs resident rowsClosed result after
            (by simpa only [SourceMergedWorker.worker, show free = [] from closed, ite_true] using done) memos valid
          simpa only [SourceMergedWorker.worker, show free = [] from closed, ite_true] using completed
      | empty | reference | mu | union => exact pure_memos _ result before after done semantic costs memos valid

/-- Completed actual workers derive ordered global receipts and coherent final tables. -/
theorem worker_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupingCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (ordinaryFuel comparisonFuel : Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before value) (result : Value Symbol Guard)
    (after : State Symbol Guard)
    (done : SourceMergedWorker.worker grouping clear top ordinaryFuel comparisonFuel value before = .done result after)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, Reads (SourceMergedWorker.worker grouping clear top ordinaryFuel comparisonFuel value)
      before result after memos saved ∧ Effect before after memos saved := by
  by_cases closed : value.free = []
  · exact worker_closed_memos grouping groupingCorrect clear top ordinaryFuel comparisonFuel
      value before semantic costs available closed result after done memos valid
  · have same : SourceMergedWorker.worker grouping clear top ordinaryFuel comparisonFuel value = MergedColdMerge.pure value := by
      funext state
      exact SourceCurrentMergedHeapEffects.worker_open grouping clear top ordinaryFuel comparisonFuel value state closed
    rw [same] at done ⊢
    exact pure_memos value result before after done semantic costs memos valid

/-- Executable source grouping retains its exact completed global unfolding calls. -/
theorem execute_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.execute clear top fuel value before = .done result after)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, Reads (SourceMergedWorker.execute clear top fuel value) before result after memos saved ∧
      Effect before after memos saved :=
  worker_memos MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear top
    (MergedOrdinaryHeight.height value) fuel value before semantic costs available result after done memos valid

/-- A native merge retains the exact bounded execution receipt that produced its heap. -/
inductive MergeReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} :
    {clear : Guard → Bool} → {top : Guard} → {value result : Value Symbol Guard} →
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard} →
    SourceEqualityNativeMerge.Merge clear top value before result after → Memos → Memos → Prop where
  | done {clear : Guard → Bool} {top : Guard} {value result : Value Symbol Guard}
      {before : SourceRecursiveIntersectionThunks.State width Symbol Guard} {heap : State Symbol Guard}
      {fuel : Nat} {memos saved : Memos}
      (actual : SourceMergedWorker.execute clear top fuel value before.machine.heap = .done result heap)
      (receipt : Reads (SourceMergedWorker.execute clear top fuel value) before.machine.heap result heap memos saved) :
      MergeReads (.done fuel actual) memos saved

/-- Native merge receipts retain both query tables in their actual returned memo bundle. -/
theorem MergeReads.query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {value result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {trace : SourceEqualityNativeMerge.Merge clear top value before result after} {memos saved : Memos}
    (receipt : MergeReads trace memos saved) : saved.query = memos.query := by
  cases receipt with
  | done _ actual => exact actual.query

/-- Actual native merge graphs derive global reads, final coherence, and exact native table retention. -/
theorem merge_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {value result : Value Symbol Guard} {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : SourceEqualityNativeMerge.Merge clear top value before result after)
    (ready : SourceEqualityNativeScoped.IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (available : Available before.machine.heap value)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, MergeReads trace memos saved ∧ Effect before.machine.heap after.machine.heap memos saved ∧
      SourceEqualityNativeScoped.IdleReady emptyGuard conjoin after ∧ Available after.machine.heap result ∧
      after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  cases trace with
  | done fuel actual =>
      obtain ⟨saved, receipt, effects⟩ := execute_memos clear top fuel value before.machine.heap
        ready.semantic costs available result _ actual memos valid
      have checked := SourceCurrentMergedHeapEffects.execute_effect (fun _ => True) clear top trivial fuel value before.machine.heap
        ready.semantic costs available result _ actual
      exact ⟨saved, .done actual receipt, effects, ready.advance _ effects.keeps effects.semantic, checked.2, rfl, rfl, rfl⟩

end MicroCFTA.SourceCurrentMergedQueryMemos
