import MicroCFTA.SourceCurrentHereditaryConstructors
import MicroCFTA.SourceCurrentMemoMergeQueryMemos

/-!
# Local annotations through the current memo-aware Merge graph

A completed table records a conditional law for each captured original.
The actual mutual graph proves each new candidate before publication.
An earlier winner uses its own law at the current returned table.
-/
namespace MicroCFTA.SourceCurrentHereditaryMerge
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect ValueReady EdgeReady)
open SourceEqualityAnnotationLanguage
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- Each result preserves annotations of its own complete captured original. -/
def Certificate (valid : Guard → Prop) (input output : Value Symbol Guard) : Prop :=
  Annotated valid input → Annotated valid output

/-- Warm entries carry local conditional laws without restricting other heap guards. -/
def Stored (valid : Guard → Prop) (memo : Memo Symbol Guard) : Prop :=
  ∀ key entry, memo key = some entry → Certificate valid entry.original entry.result

/-- Empty completed tables need no annotation premise. -/
theorem stored_empty (valid : Guard → Prop) : Stored valid (empty : Memo Symbol Guard) := by
  intro key entry found
  cases found

/-- Completion retains old laws and checks only the actual new candidate. -/
theorem stored_remember {valid : Guard → Prop} {memo : Memo Symbol Guard}
    (stored : Stored valid memo) (input output : Value Symbol Guard)
    (law : Certificate valid input output) : Stored valid (remember memo input output) := by
  intro key entry found
  rcases remember_cases memo input output key entry found with old | ⟨_, same⟩
  · exact stored key entry old
  · subst entry
    exact law

/-- Requests retain their original physical contract and local annotation law. -/
def Contract (valid : Guard → Prop) (input : Value Symbol Guard) (before : State Symbol Guard)
    (output : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SourceCurrentMemoMergeEffects.Contract input before output after ∧ Certificate valid input output

/-- Instructions use the stronger contract at their actual recursive calls. -/
abbrev Certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (post : State Symbol Guard → Output → Prop) : Prop :=
  SourceCurrentMemoMergeEffects.Certified (Contract valid) clear code before post

private theorem lift_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (post : State Symbol Guard → Output → Prop)
    (checked : SourceCurrentMemoMergeEffects.Certified SourceCurrentMemoMergeEffects.Contract clear code before post) :
    Certified valid clear code before post := by
  induction code generalizing before with
  | pure value => exact checked
  | work job => exact checked
  | select inputs => exact checked
  | request input => exact ⟨checked.1, fun output after effect returned => checked.2 output after effect returned.1⟩
  | bind first next ihFirst ihNext =>
      obtain ⟨intermediate, firstChecked, later⟩ := checked
      exact ⟨intermediate, ihFirst _ _ firstChecked,
        fun value middle effect valid => ihNext value _ _ (later value middle effect valid)⟩

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
  exact ⟨checked.1, checked.2, SourceCurrentHereditaryConstructors.makeEdge valid symbol guard values before
    semantic.ready.semantic.1.normal.facts.coherent semantic.ready.semantic.1.normal.facts.cached available annotation annotated⟩

private theorem node_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : ClosedEdges edges)
    (annotated : ∀ edge ∈ edges, SourceCurrentHereditaryConstructors.Edge valid edge) :
    Certified valid clear (.work (makeNode edges)) before (ValuePost valid) := by
  have checked := SourceCurrentMemoMergeEffects.node_certified clear edges before semantic costs resident closed
  exact ⟨checked.1, checked.2, SourceCurrentHereditaryConstructors.makeNode valid edges before
    semantic.ready.semantic.1.normal.facts.coherent semantic.ready.semantic.1.normal.facts.linked resident annotated⟩

private theorem request_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (input : Value Symbol Guard) (before : State Symbol Guard)
    (ready : ValuePost valid before input) : Certified valid clear (.request input) before (ValuePost valid) :=
  ⟨ready.1.1, fun _ _ _ returned => ⟨⟨returned.1.1, returned.1.2 ready.1.2⟩, returned.2 ready.2⟩⟩

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
      exact ⟨⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
        (InternedShallowHeap.makeUnion_noNewMu values before)⟩, checked.2,
        SourceCurrentHereditaryConstructors.makeUnion valid values before semantic.ready.semantic.1.normal.facts available annotated⟩
    · simp only [boundary, Bool.false_eq_true, ite_false]
      have checked := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
        values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      apply SourceCurrentMemoMergeEffects.bind_certified (Contract valid) clear _ _ before (ValuePost valid) _
      · exact ⟨⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
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
  apply SourceCurrentMemoMergeEffects.bind_certified (Contract valid) clear _ _ before
    (fun heap values => Values heap values ∧ ClosedValues values ∧ ∀ value ∈ values, Annotated valid value) _
  · refine ⟨available, closed, ?_⟩
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
  apply SourceCurrentMemoMergeEffects.bind_certified (Contract valid) clear _ _ before
    (fun heap values => ∀ value ∈ values, ValuePost valid heap value) _
  · exact SourceCurrentMemoMergeEffects.map_certified (Contract valid) clear Code.request (ValuePost valid) (ValuePost valid)
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
  apply SourceCurrentMemoMergeEffects.bind_certified (Contract valid) clear _ _ before
    (fun heap values => ∀ value ∈ values, ValuePost valid heap value) _
  · apply SourceCurrentMemoMergeEffects.map_certified (Contract valid) clear column
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
  · exact SourceCurrentMemoMergeEffects.map_certified (Contract valid) clear small (EdgePost valid) (EdgePost valid)
      (fun _ _ effect edge ready => edge_grows effect edge ready) (fun _ _ effect edge ready => edge_grows effect edge ready)
      edges (fun edge _ heap semantic costs ready => small_certified valid clear edge heap semantic costs ready)
      before semantic costs (fun edge member => ⟨⟨resident edge member, closed edge member⟩, annotated edge member⟩)
  · cases edges with
    | nil => simp_all
    | cons first rest =>
        apply SourceCurrentMemoMergeEffects.bind_certified (Contract valid) clear _ _ before (EdgePost valid) _
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
  apply SourceCurrentMemoMergeEffects.bind_certified (Contract valid) clear _ _ before
    (fun heap rows => ∀ row ∈ rows, ∀ edge ∈ row, EdgePost valid heap edge) _
  · apply SourceCurrentMemoMergeEffects.map_certified (Contract valid) clear (group top)
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
      · simpa only [body, closed, ite_false] using annotated
  | empty | reference | mu | union => exact annotated

/-- The actual mutual graph discharges all recursive annotation contracts. -/
theorem run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : valid top)
    {code : Code Symbol Guard Output} {before after : State Symbol Guard}
    {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before →
      SourceCurrentMemoMergeEffects.Stored before memo → Stored valid memo → Certified valid clear code before post →
      Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧ Stored valid saved ∧ post after output := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ =>
        SemanticReady before → CostHeap before → SourceCurrentMemoMergeEffects.Stored before memo → Stored valid memo →
        Available before input → Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧
          Stored valid saved ∧ Contract valid input before output after) with
  | pure value state memo =>
      intro post semantic costs physical annotations checked
      exact ⟨SourceCurrentMemoMergeEffects.effect_refl _ semantic costs, physical, annotations, checked⟩
  | work job state memo =>
      intro post semantic costs physical annotations checked
      exact ⟨checked.1, physical.grows checked.1.keeps, annotations, checked.2⟩
  | select fuel done =>
      intro post semantic costs physical annotations checked
      have original := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _ semantic costs checked.1 _ _ done
      have effect : Effect _ _ := ⟨original.keeps, original.semantic, original.costs⟩
      exact ⟨effect, physical.grows effect.keeps, annotations, checked.2.2 fuel _ _ done effect⟩
  | request actual ih =>
      intro post semantic costs physical annotations checked
      obtain ⟨effect, physicalAfter, annotationsAfter, returned⟩ := ih semantic costs physical annotations checked.1
      exact ⟨effect, physicalAfter, annotationsAfter, checked.2 _ _ effect returned⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs physical annotations checked
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstPhysical, firstAnnotations, intermediateValid⟩ := ihFirst intermediate semantic costs physical annotations firstChecked
      obtain ⟨laterEffect, laterPhysical, laterAnnotations, returned⟩ := ihLater post firstEffect.semantic firstEffect.costs
        firstPhysical firstAnnotations (nextChecked _ _ firstEffect intermediateValid)
      exact ⟨firstEffect.trans laterEffect, laterPhysical, laterAnnotations, returned⟩
  | hit found =>
      rename_i semantic costs physical annotations available
      obtain ⟨same, result, closed⟩ := SourceCurrentMemoMergeEffects.hit_original semantic available physical found
      have law := annotations _ _ found
      rw [same] at law
      exact ⟨SourceCurrentMemoMergeEffects.effect_refl _ semantic costs, physical, annotations, ⟨result, closed⟩, law⟩
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs physical annotations available
      have checked := lift_certified valid clear (body top input) before _
        (SourceCurrentMemoMergeEffects.body_certified clear top input before semantic costs available)
      obtain ⟨effect, physicalAfter, annotationsAfter, candidatePhysical⟩ := ih _ semantic costs physical annotations checked
      have candidateLaw : Certificate valid input candidate := by
        intro annotated
        exact (ih _ semantic costs physical annotations
          (body_certified valid clear top topValid input before semantic costs available annotated)).2.2.2
      have inputAvailable := effect.keeps.available input available
      have completed := SourceCurrentMemoMergeEffects.stored_remember physicalAfter input candidate inputAvailable candidatePhysical.1 candidatePhysical.2
      have completedAnnotations := stored_remember annotationsAfter input candidate candidateLaw
      obtain ⟨same, result, closed⟩ := SourceCurrentMemoMergeEffects.hit_original effect.semantic inputAvailable completed (winner_found current input candidate)
      have law := completedAnnotations _ _ (winner_found current input candidate)
      rw [same] at law
      exact ⟨effect, completed, completedAnnotations, ⟨result, closed⟩, law⟩

/-- Current completed calls retain their own warm laws and annotate the actual winner. -/
theorem call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : valid top)
    {input output : Value Symbol Guard} {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (physical : SourceCurrentMemoMergeEffects.Stored before memo)
    (annotations : Stored valid memo) (available : Available before input) :
    Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧ Stored valid saved ∧ Contract valid input before output after :=
  run valid topValid (.request actual) (fun after output => Contract valid input before output after)
    semantic costs physical annotations ⟨available, fun _ _ _ returned => returned⟩

/-- A cold call needs no future result law or annotation heap. -/
theorem cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : valid top)
    {input output : Value Symbol Guard} {before after : State Symbol Guard} {saved : Memo Symbol Guard}
    (actual : Call clear top input before empty output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before input) (annotated : Annotated valid input) :
    Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧ Stored valid saved ∧ Annotated valid output := by
  obtain ⟨effect, physical, stored, returned⟩ := call valid topValid actual semantic costs
    (SourceCurrentMemoMergeEffects.stored_empty before) (stored_empty valid) available
  exact ⟨effect, physical, stored, returned.2 annotated⟩

end MicroCFTA.SourceCurrentHereditaryMerge
