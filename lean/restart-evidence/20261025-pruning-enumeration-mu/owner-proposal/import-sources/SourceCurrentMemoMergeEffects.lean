import MicroCFTA.SourceCurrentMemoMergeGraph
import MicroCFTA.SourceCurrentMergedHeapEffects

/-!
# Physical effects of completed recursive merge requests

The completed table retains available originals and results. Its closedness
condition applies only to closed original arguments. Each miss checks its
actual recursive body before it records and rereads the winning entry.
-/
namespace MicroCFTA.SourceCurrentMemoMergeEffects
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Completed entries retain physical originals and conditionally closed results. -/
def Stored (heap : State Symbol Guard) (memo : Memo Symbol Guard) : Prop :=
  ∀ key entry, memo key = some entry → entry.original.referenceOf = key ∧
    Available heap entry.original ∧ Available heap entry.result ∧
      (entry.original.free = [] → entry.result.free = [])

/-- An empty completed table needs no physical entry premise. -/
theorem stored_empty (heap : State Symbol Guard) : Stored heap empty := by
  intro key entry found
  cases found

/-- Actual heap growth retains every original and completed result. -/
theorem Stored.grows {before after : State Symbol Guard} {memo : Memo Symbol Guard}
    (stored : Stored before memo) (keeps : Keeps before after) : Stored after memo := by
  intro key entry found
  obtain ⟨identity, original, result, closed⟩ := stored key entry found
  exact ⟨identity, keeps.available _ original, keeps.available _ result, closed⟩

/-- Completion preserves an earlier winner and checks a newly stored pair. -/
theorem stored_remember {heap : State Symbol Guard} {memo : Memo Symbol Guard}
    (stored : Stored heap memo) (input output : Value Symbol Guard)
    (original : Available heap input) (result : Available heap output)
    (closed : input.free = [] → output.free = []) : Stored heap (remember memo input output) := by
  intro key entry found
  rcases InternedRecordCoherence.record_cases memo input.referenceOf key ⟨input, output⟩ entry found with old | ⟨same, entrySame⟩
  · exact stored key entry old
  · subst entry
    exact ⟨same.symm, original, result, closed⟩

/-- Resident physical identities recover the exact original argument of a hit. -/
theorem hit_original [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {heap : State Symbol Guard} {memo : Memo Symbol Guard} {input : Value Symbol Guard} {entry : Entry Symbol Guard}
    (semantic : SemanticReady heap) (available : Available heap input) (stored : Stored heap memo)
    (found : memo input.referenceOf = some entry) :
    entry.original = input ∧ Available heap entry.result ∧ (input.free = [] → entry.result.free = []) := by
  obtain ⟨identity, original, result, closed⟩ := stored _ _ found
  have same := InternedFreshProbeKeys.resident_reference_injective heap semantic.ready.semantic.1.normal.facts.coherent
    entry.original input original.resident available.resident identity
  exact ⟨same, result, same ▸ closed⟩

/-- Actual completed work retains the heap, semantic facts, and stored costs. -/
structure Effect (before after : State Symbol Guard) : Prop where
  keeps : Keeps before after
  semantic : SemanticReady after
  costs : CostHeap after

theorem Effect.trans {before middle after : State Symbol Guard}
    (first : Effect before middle) (later : Effect middle after) : Effect before after :=
  ⟨first.keeps.trans later.keeps, later.semantic, later.costs⟩

theorem effect_refl (heap : State Symbol Guard) (semantic : SemanticReady heap) (costs : CostHeap heap) : Effect heap heap :=
  ⟨pure_keeps heap semantic.ready, semantic, costs⟩

/-- A request contract can add semantic obligations to the physical output facts. -/
def Contract (input : Value Symbol Guard) (_before : State Symbol Guard)
    (output : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  Available after output ∧ (input.free = [] → output.free = [])

/-- Instructions check their actual constructor effects and returned continuations. -/
def Certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (contract : Value Symbol Guard → State Symbol Guard → Value Symbol Guard → State Symbol Guard → Prop)
    (clear : Guard → Bool) (code : Code Symbol Guard Output) (before : State Symbol Guard)
    (post : State Symbol Guard → Output → Prop) : Prop :=
  match code with
  | .pure value => post before value
  | .work job => Effect before (run job before).2 ∧ post (run job before).2 (run job before).1
  | .select inputs => Values before inputs ∧ ClosedValues inputs ∧ ∀ fuel values after,
      SourceMergedSelection.select clear fuel inputs before = .done values after → Effect before after → post after values
  | .request input => Available before input ∧ ∀ output after,
      Effect before after → contract input before output after → post after output
  | .bind first next => ∃ intermediate : State Symbol Guard → _ → Prop,
      Certified contract clear first before intermediate ∧ ∀ value middle,
        Effect before middle → intermediate middle value → Certified contract clear (next value) middle post

/-- Sequencing checks the continuation at the exact returned heap. -/
theorem bind_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (contract : Value Symbol Guard → State Symbol Guard → Value Symbol Guard → State Symbol Guard → Prop)
    (clear : Guard → Bool) (first : Code Symbol Guard First) (next : First → Code Symbol Guard Output)
    (before : State Symbol Guard) (intermediate : State Symbol Guard → First → Prop)
    (post : State Symbol Guard → Output → Prop)
    (checked : Certified contract clear first before intermediate)
    (later : ∀ value middle, Effect before middle → intermediate middle value → Certified contract clear (next value) middle post) :
    Certified contract clear (.bind first next) before post := ⟨intermediate, checked, later⟩

/-- A proved local result property can discharge a weaker returned property. -/
theorem Certified.mono [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {contract : Value Symbol Guard → State Symbol Guard → Value Symbol Guard → State Symbol Guard → Prop}
    {clear : Guard → Bool} {code : Code Symbol Guard Output} {before : State Symbol Guard}
    {post nextPost : State Symbol Guard → Output → Prop} (checked : Certified contract clear code before post)
    (implies : ∀ after output, post after output → nextPost after output) : Certified contract clear code before nextPost := by
  induction code generalizing before with
  | pure value => exact implies _ _ checked
  | work job => exact ⟨checked.1, implies _ _ checked.2⟩
  | select inputs => exact ⟨checked.1, checked.2.1, fun fuel values after done effect => implies _ _ (checked.2.2 fuel values after done effect)⟩
  | request input => exact ⟨checked.1, fun output after effect returned => implies _ _ (checked.2 output after effect returned)⟩
  | bind first next ihFirst ihNext =>
      obtain ⟨intermediate, firstChecked, later⟩ := checked
      exact ⟨intermediate, firstChecked, fun value middle effect valid => ihNext value (later value middle effect valid) implies⟩

def ValueReady (heap : State Symbol Guard) (value : Value Symbol Guard) : Prop := Available heap value ∧ value.free = []
def EdgeReady (heap : State Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop := EdgeResident heap edge ∧ ClosedValues edge.children

theorem value_grows {before after : State Symbol Guard} (effect : Effect before after)
    (value : Value Symbol Guard) (ready : ValueReady before value) : ValueReady after value :=
  ⟨effect.keeps.available _ ready.1, ready.2⟩

theorem edge_grows {before after : State Symbol Guard} (effect : Effect before after)
    (edge : EdgeValue Symbol Guard) (ready : EdgeReady before edge) : EdgeReady after edge :=
  ⟨InternedEdgeResidency.edge_grows before after effect.keeps.growth edge ready.1, ready.2⟩

/-- Ordered maps retain local input and output facts through every earlier effect. -/
theorem map_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (contract : Value Symbol Guard → State Symbol Guard → Value Symbol Guard → State Symbol Guard → Prop)
    (clear : Guard → Bool) (call : Request → Code Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop) (post : State Symbol Guard → Output → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (postGrows : ∀ before after, Effect before after → ∀ value, post before value → post after value)
    (requests : List Request)
    (checked : ∀ request ∈ requests, ∀ before, SemanticReady before → CostHeap before → pre before request →
      Certified contract clear (call request) before post)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : ∀ request ∈ requests, pre before request) :
    Certified contract clear (SourceCurrentMemoMergeGraph.map call requests) before (fun after values => ∀ value ∈ values, post after value) := by
  induction requests generalizing before with
  | nil => exact by simp [SourceCurrentMemoMergeGraph.map, Certified]
  | cons first rest ih =>
      apply bind_certified contract clear _ _ before post _
        (checked first List.mem_cons_self before semantic costs (inputs first List.mem_cons_self))
      intro value middle effect valid
      apply bind_certified contract clear _ _ middle _ _
        (ih (fun request member => checked request (List.mem_cons_of_mem _ member)) middle effect.semantic effect.costs
          (fun request member => preGrows before middle effect request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after later ready
      intro output member
      rcases List.mem_cons.mp member with rfl | member
      · exact postGrows middle after later _ valid
      · exact ready output member

/-- Literal edge work retains the exact child records and stored costs. -/
theorem edge_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) :
    Certified Contract clear (.work (makeEdge symbol guard values)) before EdgeReady := by
  have checked := SourceEqualityRequiredCache.edge symbol guard values before semantic.ready available
  exact ⟨⟨checked.1, SourceEqualityRequiredSemanticCache.edge _ _ _ before semantic available, costs⟩,
    checked.2.1, by rw [checked.2.2]; exact closed⟩

/-- Literal node work derives available closed output from the actual rows. -/
theorem node_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges)
    (closed : ClosedEdges edges) : Certified Contract clear (.work (makeNode edges)) before ValueReady := by
  have checked := SourceEqualityRequiredCache.node edges before semantic.ready resident closed
  exact ⟨⟨checked.1, SourceEqualityRequiredSemanticCache.node edges before semantic resident closed,
    InternedFreshOrdinaryCostHeap.preserve before _ costs (InternedShallowHeap.makeNode_noNewMu edges before)⟩,
    checked.2.1, checked.2.2.1⟩

/-- Recursive requests use their actual returned physical result. -/
theorem request_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (value : Value Symbol Guard) (before : State Symbol Guard)
    (ready : ValueReady before value) : Certified Contract clear (.request value) before ValueReady :=
  ⟨ready.1, fun _ _ _ returned => ⟨returned.1, returned.2 ready.2⟩⟩

/-- Retained columns derive all constructor and recursive request obligations. -/
theorem retained_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before inputs)
    (closed : ClosedValues inputs) : Certified Contract clear (retainedColumn inputs) before ValueReady := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values) (closed : ClosedValues values) :
      Certified Contract clear
        (if values.any MergedOrdinaryHeight.recursiveBoundary then .work (makeUnion values)
          else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) before ValueReady := by
    by_cases boundary : values.any MergedOrdinaryHeight.recursiveBoundary = true
    · simp only [boundary, ite_true]
      have checked := SourceMergedCache.union values before semantic available closed
      exact ⟨⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
        (InternedShallowHeap.makeUnion_noNewMu values before)⟩, checked.2⟩
    · simp only [boundary, Bool.false_eq_true, ite_false]
      have checked := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
        values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      apply bind_certified Contract clear (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request before ValueReady _
        ⟨⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
          (InternedShallowHeap.makeNode_noNewMu _ before)⟩, checked.2.1, checked.2.2.1⟩
      exact fun value middle _ ready => request_certified clear value middle ready
  cases inputs with
  | nil => exact branches [] available closed
  | cons first rest =>
      cases rest with
      | nil => exact ⟨available first List.mem_cons_self, closed first List.mem_cons_self⟩
      | cons second rest => exact branches (first :: second :: rest) available closed

/-- Selection retains actual original values before retained-column normalization. -/
theorem column_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (_costs : CostHeap before) (available : Values before inputs)
    (closed : ClosedValues inputs) : Certified Contract clear (column inputs) before ValueReady := by
  apply bind_certified Contract clear _ _ before (fun heap values => Values heap values ∧ ClosedValues values) _
  · refine ⟨available, closed, ?_⟩
    intro fuel values after done effect
    have checked := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
      (fun _ _ _ => rfl) inputs before semantic available closed values after done
    exact ⟨checked.2.1, checked.2.2.1⟩
  · intro values middle effect ready
    exact retained_certified clear values middle effect.semantic effect.costs ready.1 ready.2

/-- Small rows check each actual child request before construction. -/
theorem small_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (edge : EdgeValue Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (ready : EdgeReady before edge) :
    Certified Contract clear (small edge) before EdgeReady := by
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge ready.1
  apply bind_certified Contract clear _ _ before (fun heap values => ∀ value ∈ values, ValueReady heap value) _
    (map_certified Contract clear Code.request ValueReady ValueReady
      (fun _ _ effect value ready => value_grows effect value ready)
      (fun _ _ effect value ready => value_grows effect value ready) edge.children
      (fun value _ heap _ _ ready => request_certified clear value heap ready) before semantic costs
      (fun value member => ⟨available value member, ready.2 value member⟩))
  intro values middle effect valid
  exact edge_certified clear _ _ values middle effect.semantic effect.costs
    (fun value member => (valid value member).1) (fun value member => (valid value member).2)

/-- Large groups check actual column inputs derived from their original rows. -/
theorem large_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before (first :: rest)) (closed : ClosedEdges (first :: rest)) :
    Certified Contract clear (large top first rest) before EdgeReady := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  apply bind_certified Contract clear _ _ before (fun heap values => ∀ value ∈ values, ValueReady heap value) _
    (map_certified Contract clear column (fun heap values => Values heap values ∧ ClosedValues values) ValueReady
      (fun _ _ effect _ ready => ⟨(fun value member => effect.keeps.available _ (ready.1 value member)), ready.2⟩)
      (fun _ _ effect value ready => value_grows effect value ready) columns
      (fun values _ heap semantic costs ready => column_certified clear values heap semantic costs ready.1 ready.2)
      before semantic costs (fun column member => ⟨(by
        intro value included
        obtain ⟨edge, outer, inner⟩ := original column member value included
        exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner), (by
        intro value included
        obtain ⟨edge, outer, inner⟩ := original column member value included
        exact closed edge outer value inner)⟩))
  intro values middle effect valid
  exact edge_certified clear _ _ values middle effect.semantic effect.costs
    (fun value member => (valid value member).1) (fun value member => (valid value member).2)

/-- Both source row-count branches check only their actual original rows. -/
theorem group_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges)
    (closed : ClosedEdges edges) : Certified Contract clear (group top edges) before (fun heap rows => ∀ edge ∈ rows, EdgeReady heap edge) := by
  unfold group
  split
  · exact map_certified Contract clear small EdgeReady EdgeReady
      (fun _ _ effect edge ready => edge_grows effect edge ready) (fun _ _ effect edge ready => edge_grows effect edge ready)
      edges (fun edge _ heap semantic costs ready => small_certified clear edge heap semantic costs ready)
      before semantic costs (fun edge member => ⟨resident edge member, closed edge member⟩)
  · cases edges with
    | nil => simp_all
    | cons first rest =>
        apply bind_certified Contract clear _ _ before EdgeReady _
          (large_certified clear top first rest before semantic costs resident closed)
        intro edge middle _ ready
        intro value member
        have same := List.mem_singleton.mp member
        exact same ▸ ready

/-- Every actual source group finishes before the final node constructor. -/
theorem root_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (groups : List (List (EdgeValue Symbol Guard))) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : ∀ group ∈ groups, Edges before group) (closed : ∀ group ∈ groups, ClosedEdges group) :
    Certified Contract clear (root top groups) before ValueReady := by
  apply bind_certified Contract clear _ _ before (fun heap rows => ∀ row ∈ rows, ∀ edge ∈ row, EdgeReady heap edge) _
    (map_certified Contract clear (group top) (fun heap edges => Edges heap edges ∧ ClosedEdges edges)
      (fun heap rows => ∀ edge ∈ rows, EdgeReady heap edge)
      (fun _ _ effect _ ready => ⟨(fun edge member => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge (ready.1 edge member)), ready.2⟩)
      (fun _ _ effect _ ready edge member => edge_grows effect edge (ready edge member)) groups
      (fun edges _ heap semantic costs ready => group_certified clear top edges heap semantic costs ready.1 ready.2)
      before semantic costs (fun edges member => ⟨resident edges member, closed edges member⟩))
  intro rows middle effect valid
  apply node_certified clear rows.flatten middle effect.semantic effect.costs
  · intro edge member
    obtain ⟨row, outer, inner⟩ := List.mem_flatten.mp member
    exact (valid row outer edge inner).1
  · intro edge member
    obtain ⟨row, outer, inner⟩ := List.mem_flatten.mp member
    exact (valid row outer edge inner).2

/-- The actual body checks closed ordinary children and returns other inputs directly. -/
theorem body_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input) :
    Certified Contract clear (body top input) before (fun after output => Contract input before output after) := by
  cases input with
  | node entry edges depth free =>
      by_cases closed : free = []
      · simp only [body, closed, ite_true]
        have facts := semantic.ready.semantic.1.normal.facts
        have resident := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
        have rowsClosed : ClosedEdges edges := fun edge member child inner =>
          MergedOrdinaryHeight.closed_child before facts.coherent entry edges depth free available.resident closed edge member child inner
        have grouping := MergedSourceGrouping.groups_correct edges
        have original (group : List (EdgeValue Symbol Guard)) (member : group ∈ MergedSourceGrouping.groups edges)
            (edge : EdgeValue Symbol Guard) (inner : edge ∈ group) : edge ∈ edges :=
          grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, inner⟩)
        have checked := root_certified clear top _ before semantic costs
          (fun group member edge inner => resident edge (original group member edge inner))
          (fun group member edge inner => rowsClosed edge (original group member edge inner))
        exact checked.mono (fun _ _ ready => ⟨ready.1, fun _ => ready.2⟩)
      · simp only [body, closed, ite_false, Certified]
        exact ⟨available, id⟩
  | empty | reference | mu | union => exact ⟨available, id⟩

/-- Actual instruction induction discharges every recursive request contract. -/
theorem run_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before → Stored before memo →
      Certified Contract clear code before post → Effect before after ∧ Stored after saved ∧ post after output := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ => SemanticReady before → CostHeap before →
        Stored before memo → Available before input → Effect before after ∧ Stored after saved ∧ Contract input before output after) with
  | pure value state memo =>
      intro post semantic costs stored checked
      exact ⟨effect_refl _ semantic costs, stored, checked⟩
  | work job state memo =>
      intro post semantic costs stored checked
      exact ⟨checked.1, stored.grows checked.1.keeps, checked.2⟩
  | select fuel done =>
      intro post semantic costs stored checked
      have original := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _ semantic costs checked.1 _ _ done
      have effect : Effect _ _ := ⟨original.keeps, original.semantic, original.costs⟩
      exact ⟨effect, stored.grows effect.keeps, checked.2.2 fuel _ _ done effect⟩
  | request actual ih =>
      intro post semantic costs stored checked
      obtain ⟨effect, retained, returned⟩ := ih semantic costs stored checked.1
      exact ⟨effect, retained, checked.2 _ _ effect returned⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs stored checked
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstStored, valid⟩ := ihFirst intermediate semantic costs stored firstChecked
      obtain ⟨laterEffect, laterStored, returned⟩ := ihLater post firstEffect.semantic firstEffect.costs firstStored
        (nextChecked _ _ firstEffect valid)
      exact ⟨firstEffect.trans laterEffect, laterStored, returned⟩
  | hit found =>
      rename_i semantic costs stored available
      obtain ⟨same, result, closed⟩ := hit_original semantic available stored found
      exact ⟨effect_refl _ semantic costs, stored, result, closed⟩
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs stored available
      obtain ⟨effect, retained, result, closed⟩ := ih _ semantic costs stored (body_certified _ _ input before semantic costs available)
      have inputAvailable := effect.keeps.available input available
      have completed := stored_remember retained input candidate inputAvailable result closed
      obtain ⟨same, winnerAvailable, winnerClosed⟩ := hit_original effect.semantic inputAvailable completed (winner_found current input candidate)
      exact ⟨effect, completed, winnerAvailable, winnerClosed⟩

/-- Completed hits and memo-aware misses derive the actual returned heap and winner. -/
theorem call_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (stored : Stored before memo) (available : Available before input) :
    Effect before after ∧ Stored after saved ∧ Available after output ∧ (input.free = [] → output.free = []) :=
  run_effects (.request actual) (fun after output => Contract input before output after) semantic costs stored
    ⟨available, fun _ _ _ returned => returned⟩

/-- Empty initial result tables discharge every physical memo-entry obligation. -/
theorem cold_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {saved : Memo Symbol Guard}
    (actual : Call clear top input before empty output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before input) :
    Effect before after ∧ Stored after saved ∧ Available after output ∧ (input.free = [] → output.free = []) :=
  call_effects actual semantic costs (stored_empty before) available

end MicroCFTA.SourceCurrentMemoMergeEffects
