import MicroCFTA.SourceCurrentMemoMergeEffects
import MicroCFTA.SourceMergedSelectionCompletion

/-!
# Finite completed memo-aware merge calls

Recursive requests use the actual result table. Ordinary child requests and
retained ordinary unions decrease ordinary height. Each selection uses its
own finite comparison receipt. Warm entries satisfy the stored-record
invariant. This result concerns completed sequential calls. It does not
supply a bound for one global-fuel worker or model pending lazy publication.
-/
namespace MicroCFTA.SourceCurrentMemoMergeCompletion
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open MergedOrdinaryHeight
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private def ValueReady (state : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  Available state value ∧ value.free = []

private def EdgeReady (state : State Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop :=
  InternedEdgeResidency.EdgeResident state edge ∧ ClosedValues edge.children

private def Complete (clear : Guard → Bool) (top : Guard) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (post : State Symbol Guard → Output → Prop) : Prop :=
  ∃ result after saved, Run clear top code before memo result after saved ∧
    Effect before after ∧ Stored after saved ∧ post after result

private theorem pure_complete (clear : Guard → Bool) (top : Guard) (value : Output)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (post : State Symbol Guard → Output → Prop) (checked : post before value) :
    Complete clear top (.pure value) before memo post :=
  ⟨value, before, memo, .pure _ _ _, ⟨pure_keeps _ semantic.ready, semantic, costs⟩, stored, checked⟩

private theorem bind_complete (clear : Guard → Bool) (top : Guard)
    (first : Code Symbol Guard First) (next : First → Code Symbol Guard Output)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (pre : State Symbol Guard → First → Prop) (post : State Symbol Guard → Output → Prop)
    (complete : Complete clear top first before memo pre)
    (continues : ∀ value middle current, Effect before middle → Stored middle current → pre middle value →
      Complete clear top (next value) middle current post) :
    Complete clear top (.bind first next) before memo post := by
  obtain ⟨value, middle, current, first, effect, stored, checked⟩ := complete
  obtain ⟨result, after, saved, later, final, valid, output⟩ := continues value middle current effect stored checked
  exact ⟨result, after, saved, .bind first later,
    ⟨effect.keeps.trans final.keeps, final.semantic, final.costs⟩, valid, output⟩

private theorem work_complete (clear : Guard → Bool) (top : Guard) (job : Work Symbol Guard Output)
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (stored : Stored before memo)
    (post : State Symbol Guard → Output → Prop)
    (effect : Effect before (run job before).2) (checked : post (run job before).2 (run job before).1) :
    Complete clear top (.work job) before memo post :=
  ⟨_, _, memo, .work _ _ _, effect, stored.grows effect.keeps, checked⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem value_grows (before after : State Symbol Guard) (effect : Effect before after)
    (value : Value Symbol Guard) (ready : ValueReady before value) : ValueReady after value :=
  ⟨effect.keeps.available value ready.1, ready.2⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem edge_grows (before after : State Symbol Guard) (effect : Effect before after)
    (edge : EdgeValue Symbol Guard) (ready : EdgeReady before edge) : EdgeReady after edge :=
  ⟨InternedEdgeResidency.edge_grows before after effect.keeps.growth edge ready.1, ready.2⟩

private theorem map_complete (clear : Guard → Bool) (top : Guard)
    (call : Input → Code Symbol Guard Output)
    (pre : State Symbol Guard → Input → Prop) (post : State Symbol Guard → Output → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ input, pre before input → pre after input)
    (postGrows : ∀ before after, Effect before after → ∀ output, post before output → post after output)
    (inputs : List Input)
    (complete : ∀ input ∈ inputs, ∀ before memo, SemanticReady before → CostHeap before → Stored before memo →
      pre before input → Complete clear top (call input) before memo post)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (ready : ∀ input ∈ inputs, pre before input) :
    Complete clear top (map call inputs) before memo (fun state outputs => ∀ output ∈ outputs, post state output) := by
  induction inputs generalizing before memo with
  | nil => exact pure_complete clear top [] before memo semantic costs stored _ (by simp)
  | cons input inputs ih =>
      apply bind_complete clear top _ _ before memo post _
        (complete input List.mem_cons_self before memo semantic costs stored (ready input List.mem_cons_self))
      intro value middle current effect valid checked
      apply bind_complete clear top _ _ middle current _ _
        (ih (fun input member => complete input (List.mem_cons_of_mem _ member)) middle current effect.semantic effect.costs valid
          (fun input member => preGrows before middle effect input (ready input (List.mem_cons_of_mem _ member))))
      intro values after saved later final outputs
      apply pure_complete clear top (value :: values) after saved later.semantic later.costs final
      intro output member
      rcases List.mem_cons.mp member with rfl | member
      · exact postGrows middle after later output checked
      · exact outputs output member

private theorem edge_complete (clear : Guard → Bool) (top : Guard) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (ready : ∀ value ∈ values, ValueReady before value) :
    Complete clear top (.work (makeEdge symbol guard values)) before memo EdgeReady := by
  have available : Values before values := fun value member => (ready value member).1
  have checked := SourceEqualityRequiredCache.edge symbol guard values before semantic.ready available
  apply work_complete clear top _ before memo stored EdgeReady
    ⟨checked.1, SourceEqualityRequiredSemanticCache.edge symbol guard values before semantic available, costs⟩
  refine ⟨checked.2.1, ?_⟩
  rw [checked.2.2]
  exact fun value member => (ready value member).2

private theorem node_complete (clear : Guard → Bool) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (ready : ∀ edge ∈ edges, EdgeReady before edge) :
    Complete clear top (.work (makeNode edges)) before memo ValueReady := by
  have resident : Edges before edges := fun edge member => (ready edge member).1
  have closed : ClosedEdges edges := fun edge member => (ready edge member).2
  have checked := SourceEqualityRequiredCache.node edges before semantic.ready resident closed
  exact work_complete clear top _ before memo stored ValueReady
    ⟨checked.1, SourceEqualityRequiredSemanticCache.node edges before semantic resident closed,
      InternedFreshOrdinaryCostHeap.preserve before _ costs (InternedShallowHeap.makeNode_noNewMu edges before)⟩
    ⟨checked.2.1, checked.2.2.1⟩

private def Smaller (Symbol : Type) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (top : Guard) (limit : Nat) : Prop :=
  ∀ (value : Value Symbol Guard), height value ≤ limit → ∀ before memo, SemanticReady before → CostHeap before → Stored before memo →
    Available before value → value.free = [] →
    ∃ result after saved, Call clear top value before memo result after saved

private theorem request_complete (clear : Guard → Bool) (top : Guard) (limit : Nat)
    (smaller : Smaller Symbol clear top limit) (input : Value Symbol Guard) (bounded : height input ≤ limit)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (available : Available before input) (closed : input.free = []) :
    Complete clear top (.request input) before memo ValueReady := by
  obtain ⟨output, after, saved, actual⟩ := smaller input bounded before memo semantic costs stored available closed
  have checked := call_effects actual semantic costs stored available
  exact ⟨output, after, saved, .request actual, checked.1, checked.2.1, checked.2.2.1, checked.2.2.2 closed⟩

private theorem retained_complete (clear : Guard → Bool) (top : Guard) (limit : Nat)
    (smaller : Smaller Symbol clear top limit) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (available : Values before values) (closed : ClosedValues values) (bounded : ∀ value ∈ values, height value ≤ limit) :
    Complete clear top (retainedColumn values) before memo ValueReady := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values)
      (closed : ClosedValues values) (bounded : ∀ value ∈ values, height value ≤ limit) :
      Complete clear top (if values.any recursiveBoundary then .work (makeUnion values)
        else .bind (.work (ordinaryUnion values)) Code.request) before memo ValueReady := by
    by_cases boundary : values.any recursiveBoundary = true
    · simp only [boundary, ite_true]
      have checked := SourceMergedCache.union values before semantic available closed
      exact work_complete clear top _ before memo stored ValueReady
        ⟨checked.1.1, checked.1.2,
          InternedFreshOrdinaryCostHeap.preserve before _ costs (InternedShallowHeap.makeUnion_noNewMu values before)⟩
        ⟨checked.2.1, checked.2.2⟩
    · simp only [boundary, Bool.false_eq_true, ite_false]
      have rows := SourceMergedCache.ordinary_rows values before semantic available closed
      have checked := SourceEqualityRequiredCache.node _ before semantic.ready rows.1 rows.2
      have effect : Effect before (run (ordinaryUnion values) before).2 :=
        ⟨checked.1, SourceEqualityRequiredSemanticCache.node _ before semantic rows.1 rows.2,
          InternedFreshOrdinaryCostHeap.preserve before _ costs (InternedShallowHeap.makeNode_noNewMu _ before)⟩
      have heightBound := ordinaryUnion_bound values before semantic.ready.semantic.1.normal.facts.coherent
        semantic.ready.semantic.1.normal.facts.linked (fun value member => (available value member).resident) limit bounded
      apply bind_complete clear top _ _ before memo (fun state value => ValueReady state value ∧ height value ≤ limit) ValueReady
        (work_complete clear top _ before memo stored _ effect ⟨⟨checked.2.1, checked.2.2.1⟩, heightBound⟩)
      intro value after saved effects valid ready
      exact request_complete clear top limit smaller value ready.2 after saved effects.semantic effects.costs valid ready.1.1 ready.1.2
  cases values with
  | nil => exact branches [] available closed bounded
  | cons first rest =>
      cases rest with
      | nil =>
          exact pure_complete clear top first before memo semantic costs stored ValueReady
            ⟨available _ List.mem_cons_self, closed _ List.mem_cons_self⟩
      | cons second rest => exact branches (first :: second :: rest) available closed bounded

private theorem column_complete (clear : Guard → Bool) (top : Guard) (limit : Nat)
    (smaller : Smaller Symbol clear top limit) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (available : Values before inputs) (closed : ClosedValues inputs) (bounded : ∀ value ∈ inputs, height value ≤ limit) :
    Complete clear top (column inputs) before memo ValueReady := by
  obtain ⟨fuel, retained, middle, done⟩ := SourceMergedSelectionCompletion.select_eventually clear inputs before semantic available closed
  have actual := done fuel (Nat.le_refl _)
  have checked := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
    (fun _ _ _ => rfl) inputs before semantic available closed retained middle actual
  have cost := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) clear fuel inputs before semantic costs available retained middle actual
  apply bind_complete clear top _ _ before memo
    (fun state values => Values state values ∧ ClosedValues values ∧ ∀ value ∈ values, value ∈ inputs) ValueReady
    ⟨retained, middle, memo, .select fuel actual,
      ⟨checked.1.1, checked.1.2, cost.costs⟩, stored.grows checked.1.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩
  intro values after saved effect valid ready
  exact retained_complete clear top limit smaller values after saved effect.semantic effect.costs valid ready.1 ready.2.1
    (fun value member => bounded value (ready.2.2 value member))

private theorem small_complete (clear : Guard → Bool) (top : Guard) (limit : Nat)
    (smaller : Smaller Symbol clear top limit) (edge : EdgeValue Symbol Guard)
    (bounded : ∀ value ∈ edge.children, height value ≤ limit)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo) (ready : EdgeReady before edge) :
    Complete clear top (small edge) before memo EdgeReady := by
  have children := map_complete clear top Code.request ValueReady ValueReady value_grows value_grows edge.children
    (fun value member state memo semantic costs stored input =>
      request_complete clear top limit smaller value (bounded value member) state memo semantic costs stored input.1 input.2)
    before memo semantic costs stored (fun value member =>
      ⟨semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge ready.1 value member, ready.2 value member⟩)
  apply bind_complete clear top _ _ before memo _ EdgeReady children
  intro values after saved effect valid available
  exact edge_complete clear top edge.entry.key.symbol edge.entry.key.constraint values after saved effect.semantic effect.costs valid available

private theorem large_complete (clear : Guard → Bool) (top : Guard) (limit : Nat)
    (smaller : Smaller Symbol clear top limit) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (bounded : ∀ edge ∈ first :: rest, ∀ value ∈ edge.children, height value ≤ limit)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (ready : ∀ edge ∈ first :: rest, EdgeReady before edge) :
    Complete clear top (large top first rest) before memo EdgeReady := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  have children := map_complete clear top column
    (fun state values => Values state values ∧ ClosedValues values) ValueReady
    (fun _ _ effect _ inputs => ⟨(fun value member => effect.keeps.available value (inputs.1 value member)), inputs.2⟩)
    value_grows columns
    (fun values member state memo semantic costs stored inputs => column_complete clear top limit smaller values state memo semantic costs stored inputs.1 inputs.2
      (fun value included => by obtain ⟨edge, outer, inner⟩ := original values member value included; exact bounded edge outer value inner))
    before memo semantic costs stored (fun values member => ⟨(by
      intro value included
      obtain ⟨edge, outer, inner⟩ := original values member value included
      exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (ready edge outer).1 value inner), (by
      intro value included
      obtain ⟨edge, outer, inner⟩ := original values member value included
      exact (ready edge outer).2 value inner)⟩)
  apply bind_complete clear top _ _ before memo _ EdgeReady children
  intro values after saved effect valid available
  exact edge_complete clear top first.entry.key.symbol top values after saved effect.semantic effect.costs valid available

private theorem group_complete (clear : Guard → Bool) (top : Guard) (limit : Nat)
    (smaller : Smaller Symbol clear top limit) (edges : List (EdgeValue Symbol Guard))
    (bounded : ∀ edge ∈ edges, ∀ value ∈ edge.children, height value ≤ limit)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (ready : ∀ edge ∈ edges, EdgeReady before edge) :
    Complete clear top (group top edges) before memo (fun state results => ∀ edge ∈ results, EdgeReady state edge) := by
  unfold group
  split
  · exact map_complete clear top small EdgeReady EdgeReady edge_grows edge_grows edges
      (fun edge member state memo semantic costs stored ready =>
        small_complete clear top limit smaller edge (bounded edge member) state memo semantic costs stored ready)
      before memo semantic costs stored ready
  · cases edges with
    | nil => exact pure_complete clear top [] before memo semantic costs stored _ (by simp)
    | cons first rest =>
        apply bind_complete clear top _ _ before memo EdgeReady _
          (large_complete clear top limit smaller first rest bounded before memo semantic costs stored ready)
        intro edge after saved effect valid checked
        exact pure_complete clear top [edge] after saved effect.semantic effect.costs valid _
          (fun other member => by simpa only [List.mem_singleton.mp member] using checked)

private theorem root_complete (clear : Guard → Bool) (top : Guard) (limit : Nat)
    (smaller : Smaller Symbol clear top limit)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat)
    (heightBound : height (.node entry edges depth []) ≤ limit + 1)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo)
    (available : Available before (.node entry edges depth [])) :
    Complete clear top (root top (MergedSourceGrouping.groups edges)) before memo ValueReady := by
  let groups := MergedSourceGrouping.groups edges
  have grouping := MergedSourceGrouping.groups_correct edges
  have facts := semantic.ready.semantic.1.normal.facts
  have original (group : List (EdgeValue Symbol Guard)) (member : group ∈ groups) (edge : EdgeValue Symbol Guard) (included : edge ∈ group) : edge ∈ edges :=
    grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, included⟩)
  have bounded (group : List (EdgeValue Symbol Guard)) (member : group ∈ groups) (edge : EdgeValue Symbol Guard) (included : edge ∈ group)
      (value : Value Symbol Guard) (selected : value ∈ edge.children) : height value ≤ limit := by
    have less := child_lt entry edges depth [] edge (original group member edge included) value selected
    omega
  have rows := map_complete clear top (group top)
    (fun state edges => ∀ edge ∈ edges, EdgeReady state edge)
    (fun state edges => ∀ edge ∈ edges, EdgeReady state edge)
    (fun before after effect edges ready edge member => edge_grows before after effect edge (ready edge member))
    (fun before after effect edges ready edge member => edge_grows before after effect edge (ready edge member)) groups
    (fun group member state memo semantic costs stored ready =>
      group_complete clear top limit smaller group (bounded group member) state memo semantic costs stored ready)
    before memo semantic costs stored (by
      intro group member edge included
      have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident edge (original group member edge included)
      exact ⟨resident, fun child selected => closed_child before facts.coherent entry edges depth [] available.resident rfl
        edge (original group member edge included) child selected⟩)
  apply bind_complete clear top _ _ before memo _ ValueReady rows
  intro groups after saved effect valid ready
  exact node_complete clear top groups.flatten after saved effect.semantic effect.costs valid (by
    intro edge member
    obtain ⟨edges, outer, inner⟩ := List.mem_flatten.mp member
    exact ready edges outer edge inner)

private theorem body_complete_of_smaller (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (smaller : ∀ (value : Value Symbol Guard), height value < height input → ∀ before memo, SemanticReady before → CostHeap before → Stored before memo →
      Available before value → value.free = [] → ∃ result after saved, Call clear top value before memo result after saved)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo) (available : Available before input) :
    Complete clear top (body top input) before memo
      (fun state result => Available state result ∧ (input.free = [] → result.free = [])) := by
  cases input with
  | node entry edges depth free =>
      by_cases closed : free = []
      · subst free
        have calls : Smaller Symbol clear top (edgesHeight edges) := by
          intro value bounded state memo semantic costs stored available closed
          exact smaller value (by simp only [height]; omega) state memo semantic costs stored available closed
        obtain ⟨result, after, saved, actual, effects, valid, ready⟩ :=
          root_complete clear top (edgesHeight edges) calls entry edges depth (Nat.le_refl _) before memo semantic costs stored available
        exact ⟨result, after, saved, by simpa only [body, ite_true] using actual, effects, valid, ready.1, fun _ => ready.2⟩
      · simpa only [body, closed, ite_false] using pure_complete clear top (.node entry edges depth free) before memo semantic costs stored
          (fun state result => Available state result ∧ (Value.free (.node entry edges depth free) = [] → result.free = [])) ⟨available, fun same => same⟩
  | empty | reference | mu | union =>
      exact pure_complete clear top _ before memo semantic costs stored _ ⟨available, fun same => same⟩

/-- Every available input has a finite actual completed call through the current result table. -/
theorem call_complete (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo) (available : Available before input) :
    ∃ result after saved, Call clear top input before memo result after saved ∧
      Effect before after ∧ Stored after saved ∧ Available after result ∧ (input.free = [] → result.free = []) := by
  have complete : ∀ bound, ∀ input : Value Symbol Guard, height input = bound →
      ∀ before memo, SemanticReady before → CostHeap before → Stored before memo → Available before input →
        ∃ result after saved, Call clear top input before memo result after saved := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
        intro input equal before memo semantic costs stored available
        cases found : memo input.referenceOf with
        | some entry => exact ⟨entry.result, before, memo, .hit found⟩
        | none =>
            have smaller : ∀ (value : Value Symbol Guard), height value < height input → ∀ state current, SemanticReady state → CostHeap state → Stored state current →
                Available state value → value.free = [] → ∃ result after saved, Call clear top value state current result after saved := by
              intro value less state current semantic costs stored available _
              exact ih (height value) (equal ▸ less) value rfl state current semantic costs stored available
            obtain ⟨candidate, after, current, actual, _⟩ :=
              body_complete_of_smaller clear top input smaller before memo semantic costs stored available
            exact ⟨_, after, _, .miss found actual⟩
  obtain ⟨result, after, saved, actual⟩ := complete (height input) input rfl before memo semantic costs stored available
  have checked := call_effects actual semantic costs stored available
  exact ⟨result, after, saved, actual, checked⟩

/-- The actual source body has a finite completed run with recursively discharged memo calls. -/
theorem body_complete (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : Stored before memo) (available : Available before input) :
    ∃ result after saved, Run clear top (body top input) before memo result after saved ∧
      Effect before after ∧ Stored after saved ∧ Available after result ∧ (input.free = [] → result.free = []) := by
  apply body_complete_of_smaller clear top input _ before memo semantic costs stored available
  intro value _ state current semantic costs stored available _
  obtain ⟨result, after, saved, actual, _⟩ := call_complete clear top value state current semantic costs stored available
  exact ⟨result, after, saved, actual⟩

/-- An empty result table derives its entry invariant without a warm-cache premise. -/
theorem cold_complete (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before input) :
    ∃ result after saved, Call clear top input before SourceCurrentMemoMergeGraph.empty result after saved ∧
      Effect before after ∧ Stored after saved ∧ Available after result ∧ (input.free = [] → result.free = []) :=
  call_complete clear top input before SourceCurrentMemoMergeGraph.empty semantic costs (stored_empty before) available

end MicroCFTA.SourceCurrentMemoMergeCompletion
