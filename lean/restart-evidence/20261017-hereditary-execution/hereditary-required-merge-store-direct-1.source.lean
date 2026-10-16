import MicroCFTA.SourceCurrentHereditaryMerge
import MicroCFTA.SourceCurrentHereditarySelection

/-!
# Causal Mu stores through actual current Merge calls

Local instruction checks cover constructor work, compared operands, and
recursive request operands. The actual mutual graph discharges the request
checks. Existing captured-owner result laws remain unchanged.
-/
namespace MicroCFTA.SourceCurrentHereditaryMergeStore
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect ValueReady EdgeReady)
open SourceEqualityAnnotationLanguage SourceCurrentHereditaryConstruction
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- Local instructions emit no unchecked Mu and use annotated comparison and request operands. -/
def Certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (post : State Symbol Guard → Output → Prop) : Prop :=
  match code with
  | .pure value => post before value
  | .work job => InternedShallowHeap.NoNewMu before (run job before).2 ∧
      Effect before (run job before).2 ∧ post (run job before).2 (run job before).1
  | .select inputs => Values before inputs ∧ ClosedValues inputs ∧
      (∀ value ∈ inputs, Annotated valid value) ∧ ∀ fuel values after,
      SourceMergedSelection.select clear fuel inputs before = .done values after → Effect before after → post after values
  | .request input => Available before input ∧ Annotated valid input ∧ ∀ output after,
      Effect before after → SourceCurrentHereditaryMerge.Contract valid input before output after → post after output
  | .bind first next => ∃ intermediate : State Symbol Guard → _ → Prop,
      Certified valid clear first before intermediate ∧ ∀ value middle,
        Effect before middle → intermediate middle value → Certified valid clear (next value) middle post

private theorem Certified.mono [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {valid : Guard → Prop} {clear : Guard → Bool} {code : Code Symbol Guard Output} {before : State Symbol Guard}
    {post nextPost : State Symbol Guard → Output → Prop} (checked : Certified valid clear code before post)
    (implies : ∀ after output, post after output → nextPost after output) : Certified valid clear code before nextPost := by
  induction code generalizing before with
  | pure value => exact implies _ _ checked
  | work job => exact ⟨checked.1, checked.2.1, implies _ _ checked.2.2⟩
  | select inputs => exact ⟨checked.1, checked.2.1, checked.2.2.1, fun fuel values after done effect => implies _ _ (checked.2.2.2 fuel values after done effect)⟩
  | request input => exact ⟨checked.1, checked.2.1, fun output after effect returned => implies _ _ (checked.2.2 output after effect returned)⟩
  | bind first next ihFirst ihNext =>
      obtain ⟨intermediate, firstChecked, later⟩ := checked
      exact ⟨intermediate, firstChecked, fun value middle effect valid => ihNext value (later value middle effect valid) implies⟩

private theorem bind_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (first : Code Symbol Guard First)
    (next : First → Code Symbol Guard Output) (before : State Symbol Guard)
    (intermediate : State Symbol Guard → First → Prop) (post : State Symbol Guard → Output → Prop)
    (checked : Certified valid clear first before intermediate)
    (later : ∀ value middle, Effect before middle → intermediate middle value → Certified valid clear (next value) middle post) :
    Certified valid clear (.bind first next) before post := ⟨intermediate, checked, later⟩

private theorem map_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (call : Request → Code Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop) (post : State Symbol Guard → Output → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (postGrows : ∀ before after, Effect before after → ∀ value, post before value → post after value)
    (requests : List Request)
    (checked : ∀ request ∈ requests, ∀ before, SemanticReady before → CostHeap before → pre before request →
      Certified valid clear (call request) before post)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : ∀ request ∈ requests, pre before request) :
    Certified valid clear (map call requests) before (fun after values => ∀ value ∈ values, post after value) := by
  induction requests generalizing before with
  | nil => intro value member; cases member
  | cons first rest ih =>
      apply bind_certified valid clear _ _ before post _
        (checked first List.mem_cons_self before semantic costs (inputs first List.mem_cons_self))
      intro value middle effect returned
      apply bind_certified valid clear _ _ middle _ _
        (ih (fun request member => checked request (List.mem_cons_of_mem _ member)) middle effect.semantic effect.costs
          (fun request member => preGrows before middle effect request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after later ready output member
      rcases List.mem_cons.mp member with rfl | member
      · exact postGrows middle after later _ returned
      · exact ready output member

private abbrev ValuePost (valid : Guard → Prop) (heap : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ValueReady heap value ∧ Annotated valid value
private abbrev EdgePost (valid : Guard → Prop) (heap : State Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop :=
  EdgeReady heap edge ∧ SourceCurrentHereditaryConstructors.Edge valid edge

private theorem value_grows {valid : Guard → Prop} {before after : State Symbol Guard}
    (effect : Effect before after) (value : Value Symbol Guard) (ready : ValuePost valid before value) :
    ValuePost valid after value := ⟨SourceCurrentMemoMergeEffects.value_grows effect value ready.1, ready.2⟩
private theorem edge_grows {valid : Guard → Prop} {before after : State Symbol Guard}
    (effect : Effect before after) (edge : EdgeValue Symbol Guard) (ready : EdgePost valid before edge) :
    EdgePost valid after edge := ⟨SourceCurrentMemoMergeEffects.edge_grows effect edge ready.1, ready.2⟩

private theorem edge_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (closed : ClosedValues values) (annotation : valid guard)
    (annotated : ∀ value ∈ values, Annotated valid value) :
    Certified valid clear (.work (makeEdge symbol guard values)) before (EdgePost valid) := by
  have checked := SourceCurrentMemoMergeEffects.edge_certified clear symbol guard values before semantic costs available closed
  exact ⟨(by intro key entry body depth ordinary found; exact found), checked.1, checked.2, SourceCurrentHereditaryConstructors.makeEdge valid symbol guard values before
    semantic.ready.semantic.1.normal.facts.coherent semantic.ready.semantic.1.normal.facts.cached available annotation annotated⟩

private theorem node_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : ClosedEdges edges)
    (annotated : ∀ edge ∈ edges, SourceCurrentHereditaryConstructors.Edge valid edge) :
    Certified valid clear (.work (makeNode edges)) before (ValuePost valid) := by
  have checked := SourceCurrentMemoMergeEffects.node_certified clear edges before semantic costs resident closed
  exact ⟨InternedShallowHeap.makeNode_noNewMu edges before, checked.1, checked.2, SourceCurrentHereditaryConstructors.makeNode valid edges before
    semantic.ready.semantic.1.normal.facts.coherent semantic.ready.semantic.1.normal.facts.linked resident annotated⟩

private theorem request_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (input : Value Symbol Guard) (before : State Symbol Guard)
    (ready : ValuePost valid before input) : Certified valid clear (.request input) before (ValuePost valid) :=
  ⟨ready.1.1, ready.2, fun _ _ _ returned => ⟨⟨returned.1.1, returned.1.2 ready.1.2⟩, returned.2 ready.2⟩⟩

private theorem retained_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before inputs) (closed : ClosedValues inputs)
    (annotated : ∀ value ∈ inputs, Annotated valid value) :
    Certified valid clear (retainedColumn inputs) before (ValuePost valid) := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values)
      (closed : ClosedValues values) (annotated : ∀ value ∈ values, Annotated valid value) :
      Certified valid clear
        (if values.any MergedOrdinaryHeight.recursiveBoundary then .work (makeUnion values)
          else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) before (ValuePost valid) := by
    by_cases boundary : values.any MergedOrdinaryHeight.recursiveBoundary = true
    · simp only [boundary, ite_true]
      have checked := SourceMergedCache.union values before semantic available closed
      exact ⟨InternedShallowHeap.makeUnion_noNewMu values before, ⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
        (InternedShallowHeap.makeUnion_noNewMu values before)⟩, checked.2,
        SourceCurrentHereditaryConstructors.makeUnion valid values before semantic.ready.semantic.1.normal.facts available annotated⟩
    · simp only [boundary, Bool.false_eq_true, ite_false]
      have checked := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
        values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      apply bind_certified valid clear _ _ before (ValuePost valid) _
      · exact ⟨InternedShallowHeap.makeNode_noNewMu _ before, ⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
          (InternedShallowHeap.makeNode_noNewMu _ before)⟩, ⟨checked.2.1, checked.2.2.1⟩,
          SourceCurrentHereditaryConstructors.ordinaryUnion valid values before semantic.ready.semantic.1.normal.facts.coherent
            semantic.ready.semantic.1.normal.facts.linked available annotated⟩
      · exact fun value middle _ ready => request_certified valid clear value middle ready
  cases inputs with
  | nil => exact branches [] available closed annotated
  | cons first rest =>
      cases rest with
      | nil => exact ⟨⟨available first List.mem_cons_self, closed first List.mem_cons_self⟩, annotated first List.mem_cons_self⟩
      | cons second rest => exact branches _ available closed annotated

private theorem column_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (_costs : CostHeap before)
    (available : Values before inputs) (closed : ClosedValues inputs)
    (annotated : ∀ value ∈ inputs, Annotated valid value) :
    Certified valid clear (column inputs) before (ValuePost valid) := by
  apply bind_certified valid clear _ _ before
    (fun heap values => Values heap values ∧ ClosedValues values ∧ ∀ value ∈ values, Annotated valid value) _
  · refine ⟨available, closed, annotated, ?_⟩
    intro fuel values after done _
    have checked := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
      (fun _ _ _ => rfl) inputs before semantic available closed values after done
    exact ⟨checked.2.1, checked.2.2.1, fun value member => annotated value (checked.2.2.2.1 value member)⟩
  · intro values middle effect ready
    exact retained_certified valid clear values middle effect.semantic effect.costs ready.1 ready.2.1 ready.2.2

private theorem small_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (edge : EdgeValue Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (ready : EdgePost valid before edge) :
    Certified valid clear (small edge) before (EdgePost valid) := by
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge ready.1.1
  apply bind_certified valid clear _ _ before
    (fun heap values => ∀ value ∈ values, ValuePost valid heap value) _
  · exact map_certified valid clear Code.request (ValuePost valid) (ValuePost valid)
      (fun _ _ effect value ready => value_grows effect value ready)
      (fun _ _ effect value ready => value_grows effect value ready) edge.children
      (fun value _ heap _ _ ready => request_certified valid clear value heap ready) before semantic costs
      (fun value member => ⟨⟨available value member, ready.1.2 value member⟩, ready.2.2 value member⟩)
  · intro values middle effect readyValues
    exact edge_certified valid clear _ _ values middle effect.semantic effect.costs
      (fun value member => (readyValues value member).1.1) (fun value member => (readyValues value member).1.2)
      ready.2.1 (fun value member => (readyValues value member).2)

private theorem large_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before (first :: rest)) (closed : ClosedEdges (first :: rest))
    (annotated : ∀ edge ∈ first :: rest, SourceCurrentHereditaryConstructors.Edge valid edge) :
    Certified valid clear (large top first rest) before (EdgePost valid) := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard)
      (included : value ∈ column) : ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  apply bind_certified valid clear _ _ before
    (fun heap values => ∀ value ∈ values, ValuePost valid heap value) _
  · apply map_certified valid clear column
      (fun heap values => Values heap values ∧ ClosedValues values ∧ ∀ value ∈ values, Annotated valid value) (ValuePost valid)
      (fun _ _ effect _ ready => ⟨fun value member => effect.keeps.available _ (ready.1 value member), ready.2⟩)
      (fun _ _ effect value ready => value_grows effect value ready) columns
      (fun values _ heap semantic costs ready => column_certified valid clear values heap semantic costs ready.1 ready.2.1 ready.2.2)
      before semantic costs
    intro column member
    refine ⟨?_, ?_, ?_⟩
    · intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner
    · intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact closed edge outer value inner
    · intro value included
      obtain ⟨edge, outer, inner⟩ := original column member value included
      exact (annotated edge outer).2 value inner
  · intro values middle effect ready
    exact edge_certified valid clear _ _ values middle effect.semantic effect.costs
      (fun value member => (ready value member).1.1) (fun value member => (ready value member).1.2)
      topValid (fun value member => (ready value member).2)

private theorem group_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges)
    (closed : ClosedEdges edges) (annotated : ∀ edge ∈ edges, SourceCurrentHereditaryConstructors.Edge valid edge) :
    Certified valid clear (group top edges) before (fun heap rows => ∀ edge ∈ rows, EdgePost valid heap edge) := by
  unfold group
  split
  · exact map_certified valid clear small (EdgePost valid) (EdgePost valid)
      (fun _ _ effect edge ready => edge_grows effect edge ready) (fun _ _ effect edge ready => edge_grows effect edge ready)
      edges (fun edge _ heap semantic costs ready => small_certified valid clear edge heap semantic costs ready)
      before semantic costs (fun edge member => ⟨⟨resident edge member, closed edge member⟩, annotated edge member⟩)
  · cases edges with
    | nil => simp_all
    | cons first rest =>
        apply bind_certified valid clear _ _ before (EdgePost valid) _
          (large_certified valid clear top topValid first rest before semantic costs resident closed annotated)
        intro edge _ _ ready value member
        exact (List.mem_singleton.mp member) ▸ ready

private theorem root_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (groups : List (List (EdgeValue Symbol Guard))) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : ∀ group ∈ groups, Edges before group) (closed : ∀ group ∈ groups, ClosedEdges group)
    (annotated : ∀ group ∈ groups, ∀ edge ∈ group, SourceCurrentHereditaryConstructors.Edge valid edge) :
    Certified valid clear (root top groups) before (ValuePost valid) := by
  apply bind_certified valid clear _ _ before
    (fun heap rows => ∀ row ∈ rows, ∀ edge ∈ row, EdgePost valid heap edge) _
  · apply map_certified valid clear (group top)
      (fun heap edges => Edges heap edges ∧ ClosedEdges edges ∧ ∀ edge ∈ edges, SourceCurrentHereditaryConstructors.Edge valid edge)
      (fun heap rows => ∀ edge ∈ rows, EdgePost valid heap edge)
      (fun _ _ effect _ ready => ⟨fun edge member => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge (ready.1 edge member), ready.2⟩)
      (fun _ _ effect _ ready edge member => edge_grows effect edge (ready edge member)) groups
      (fun edges _ heap semantic costs ready => group_certified valid clear top topValid edges heap semantic costs ready.1 ready.2.1 ready.2.2)
      before semantic costs (fun edges member => ⟨resident edges member, closed edges member, annotated edges member⟩)
  · intro rows middle effect ready
    exact node_certified valid clear rows.flatten middle effect.semantic effect.costs
      (fun edge member => by obtain ⟨row, outer, inner⟩ := List.mem_flatten.mp member; exact (ready row outer edge inner).1.1)
      (fun edge member => by obtain ⟨row, outer, inner⟩ := List.mem_flatten.mp member; exact (ready row outer edge inner).1.2)
      (fun edge member => by obtain ⟨row, outer, inner⟩ := List.mem_flatten.mp member; exact (ready row outer edge inner).2)

private theorem body_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (annotated : Annotated valid input) :
    Certified valid clear (body top input) before (fun _ output => Annotated valid output) := by
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
        exact (root_certified valid clear top topValid _ before semantic costs
          (fun group member edge inner => resident edge (original group member edge inner))
          (fun group member edge inner => rowsClosed edge (original group member edge inner))
          (fun group member edge inner => SourceCurrentHereditaryConstructors.node_edge annotated edge (original group member edge inner))).mono
          (fun _ _ ready => ready.2)
      · simpa only [body, closed, ite_false, Certified] using annotated
  | empty | reference | mu | union => exact annotated

/-- Actual instructions retain both completed memo laws and the causal Mu store. -/
theorem run_store [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : valid top)
    {code : Code Symbol Guard Output} {before after : State Symbol Guard}
    {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ post : State Symbol Guard → Output → Prop, SemanticReady before → CostHeap before →
      SourceCurrentMemoMergeEffects.Stored before memo → SourceCurrentHereditaryMerge.Stored valid memo →
      MuStored valid before → Certified valid clear code before post →
      Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧ SourceCurrentHereditaryMerge.Stored valid saved ∧
        MuStored valid after ∧ post after output := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ =>
        SemanticReady before → CostHeap before → SourceCurrentMemoMergeEffects.Stored before memo →
        SourceCurrentHereditaryMerge.Stored valid memo → MuStored valid before → Available before input → Annotated valid input →
          Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧ SourceCurrentHereditaryMerge.Stored valid saved ∧
            MuStored valid after ∧ SourceCurrentHereditaryMerge.Contract valid input before output after) with
  | pure value state memo =>
      intro post semantic costs physical annotations stored checked
      exact ⟨SourceCurrentMemoMergeEffects.effect_refl _ semantic costs, physical, annotations, stored, checked⟩
  | work job state memo =>
      intro post semantic costs physical annotations stored checked
      exact ⟨checked.2.1, physical.grows checked.2.1.keeps, annotations, stored.preserve checked.1, checked.2.2⟩
  | select fuel done =>
      intro post semantic costs physical annotations stored checked
      have original := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _ semantic costs checked.1 _ _ done
      have effect : Effect _ _ := ⟨original.keeps, original.semantic, original.costs⟩
      have retained := SourceCurrentHereditarySelection.select valid clear fuel _ _ semantic costs
        checked.1 checked.2.1 checked.2.2.1 stored _ _ done
      exact ⟨effect, physical.grows effect.keeps, annotations, retained.1, checked.2.2.2 fuel _ _ done effect⟩
  | request actual ih =>
      intro post semantic costs physical annotations stored checked
      obtain ⟨effect, physicalAfter, annotationsAfter, storedAfter, returned⟩ :=
        ih semantic costs physical annotations stored checked.1 checked.2.1
      exact ⟨effect, physicalAfter, annotationsAfter, storedAfter, checked.2.2 _ _ effect returned⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs physical annotations stored checked
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstPhysical, firstAnnotations, firstStored, intermediateValid⟩ :=
        ihFirst intermediate semantic costs physical annotations stored firstChecked
      obtain ⟨laterEffect, laterPhysical, laterAnnotations, laterStored, returned⟩ :=
        ihLater post firstEffect.semantic firstEffect.costs firstPhysical firstAnnotations firstStored
          (nextChecked _ _ firstEffect intermediateValid)
      exact ⟨firstEffect.trans laterEffect, laterPhysical, laterAnnotations, laterStored, returned⟩
  | hit found =>
      rename_i semantic costs physical annotations stored available _annotated
      obtain ⟨effect, physicalAfter, annotationsAfter, returned⟩ :=
        SourceCurrentHereditaryMerge.call valid topValid (.hit found) semantic costs physical annotations available
      exact ⟨effect, physicalAfter, annotationsAfter, stored, returned⟩
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs physical annotations stored available annotated
      obtain ⟨_effect, _physicalAfter, _annotationsAfter, storedAfter, _candidateAnnotations⟩ :=
        ih _ semantic costs physical annotations stored
          (body_certified valid clear top topValid input before semantic costs available annotated)
      obtain ⟨effect, physicalAfter, annotationsAfter, returned⟩ :=
        SourceCurrentHereditaryMerge.call valid topValid (.miss absent actual) semantic costs physical annotations available
      exact ⟨effect, physicalAfter, annotationsAfter, storedAfter, returned⟩

/-- A completed current call retains the causal store without a future recursive result premise. -/
theorem call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : valid top)
    {input output : Value Symbol Guard} {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (physical : SourceCurrentMemoMergeEffects.Stored before memo)
    (annotations : SourceCurrentHereditaryMerge.Stored valid memo) (stored : MuStored valid before)
    (available : Available before input) (annotated : Annotated valid input) :
    Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧ SourceCurrentHereditaryMerge.Stored valid saved ∧
      MuStored valid after ∧ SourceCurrentHereditaryMerge.Contract valid input before output after :=
  run_store valid topValid (.request actual) (fun after output => SourceCurrentHereditaryMerge.Contract valid input before output after)
    semantic costs physical annotations stored ⟨available, annotated, fun _ _ _ returned => returned⟩

/-- Cold completed calls derive their memo laws and retain the same actual causal constructor store. -/
theorem cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : valid top)
    {input output : Value Symbol Guard} {before after : State Symbol Guard} {saved : Memo Symbol Guard}
    (actual : Call clear top input before empty output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (stored : MuStored valid before)
    (available : Available before input) (annotated : Annotated valid input) :
    Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧ SourceCurrentHereditaryMerge.Stored valid saved ∧
      MuStored valid after ∧ Annotated valid output := by
  obtain ⟨effect, physical, annotations, retained, returned⟩ := call valid topValid actual semantic costs
    (SourceCurrentMemoMergeEffects.stored_empty before) (SourceCurrentHereditaryMerge.stored_empty valid) stored available annotated
  exact ⟨effect, physical, annotations, retained, returned.2 annotated⟩

end MicroCFTA.SourceCurrentHereditaryMergeStore
