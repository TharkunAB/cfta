import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeGuardCode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection

/-!
# Hereditary guard certificates for actual Merge bodies

Small groups retain their full original guards. Large groups use Top.
Column selection retains original operands. Ordinary unions concatenate
those operands' rows. Each recursive request supplies its own captured
certificate before the next constructor runs.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeGuardBody
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect)
open SourceCurrentAllocatedFiniteOrdinaryMergeGuardCode
open MergedOrdinaryHeight (ordinaryUnion)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "Top" => SourceEqualityConstraintConstructors.top
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

private abbrev ValuePost (limits : Limits) (heap : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  Available heap value ∧ SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node limits value
private abbrev EdgePost (limits : Limits) (heap : State Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop :=
  EdgeResident heap edge ∧ SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits edge

private theorem value_grows {before after : State Symbol Guard} (effect : Effect before after)
    (limits : Limits) (value : Value Symbol Guard) (ready : ValuePost limits before value) :
    ValuePost limits after value := ⟨effect.keeps.available value ready.1, ready.2⟩

private theorem edge_grows {before after : State Symbol Guard} (effect : Effect before after)
    (limits : Limits) (edge : EdgeValue Symbol Guard) (ready : EdgePost limits before edge) :
    EdgePost limits after edge :=
  ⟨InternedEdgeResidency.edge_grows before after effect.keeps.growth edge ready.1, ready.2⟩

private theorem all₂_right {Input Output : Type} {relation : Input → Output → Prop}
    {inputs : List Input} {outputs : List Output} (related : Language.All₂ relation inputs outputs)
    (output : Output) (member : output ∈ outputs) : ∃ input ∈ inputs, relation input output := by
  induction related with
  | nil => cases member
  | @cons first value rest values valid later ih =>
      rcases List.mem_cons.mp member with same | member
      · subst output; exact ⟨first, List.mem_cons_self, valid⟩
      · obtain ⟨input, present, valid⟩ := ih member
        exact ⟨input, List.mem_cons_of_mem _ present, valid⟩

private theorem value_collection {Input : Type} {inputs : List Input} {values : List (Value Symbol Guard)}
    {limits : Limits} {heap : State Symbol Guard}
    (related : Language.All₂ (fun _ value => ValuePost limits heap value) inputs values) :
    Values heap values ∧ SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children limits values := by
  have each : ∀ value ∈ values, ValuePost limits heap value := by
    intro value member
    obtain ⟨_, _, valid⟩ := all₂_right related value member
    exact valid
  exact ⟨fun value member => (each value member).1,
    SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.children_of_members limits values (fun value member => (each value member).2)⟩

variable [DecidableEq Symbol] [edgeEq : DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Small rows retain their complete original constraint. -/
theorem small_certified (clear : Guard → Bool) (edge : EdgeValue Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : EdgeResident before edge)
    (limits : Limits) (profile : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge limits edge) :
    Certified clear (small edge) before (EdgePost limits) := by
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  apply bind_certified clear _ _ before
    (fun heap values => Language.All₂ (fun _ value => ValuePost limits heap value) edge.children values) _
  · apply map_certified clear Code.request (fun heap value => Available heap value)
      (fun heap _ value => ValuePost limits heap value)
      (fun _ _ effect value ready => effect.keeps.available value ready)
      (fun _ _ effect _ value ready => value_grows effect _ value ready) edge.children
      ?_ before semantic costs available
    intro value member heap _ _ ready
    apply (request_certified clear value heap ready).mono
    intro after output returned
    exact ⟨returned.1.1, returned.2 limits (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.member edge.children (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.children edge profile) value member)⟩
  · intro values middle effect related
    obtain ⟨available, profiled⟩ := value_collection related
    exact (edge_certified clear _ _ values middle effect.semantic effect.costs available
      limits (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.guard edge profile) profiled).mono (fun _ _ result => ⟨result.1.1, result.2⟩)

private theorem retained_certified (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before inputs) (limits : Limits) (profile : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children limits inputs) :
    Certified clear (retainedColumn inputs) before (ValuePost limits) := by
  have ordinary : inputs.any MergedOrdinaryHeight.recursiveBoundary = false := List.any_eq_false.mpr (by
    intro value member
    have domain := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node.domain value (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.member inputs profile value member)
    cases domain <;> simp [MergedOrdinaryHeight.recursiveBoundary])
  have many (values : List (Value Symbol Guard)) (available : Values before values)
      (profile : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children limits values) (ordinary : values.any MergedOrdinaryHeight.recursiveBoundary = false) :
      Certified clear (.bind (.work (ordinaryUnion values)) Code.request) before (ValuePost limits) := by
    have facts := semantic.ready.semantic.1.normal.facts
    have closed : MergedColdReaderClosedInputs.ClosedValues values := fun value member =>
      SourceCurrentAllocatedFiniteOrdinaryFinite.closed before facts.coherent value (available value member)
        (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node.domain value (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.member values profile value member))
    have physical := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
      values before semantic available closed ordinary
    have output := SourceCurrentAllocatedFiniteOrdinaryGuardConstructors.ordinaryUnion values before
      facts.coherent facts.linked available profile
    apply bind_certified clear _ _ before (ValuePost limits) _
    · exact ⟨⟨physical.1.1, physical.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
        (InternedShallowHeap.makeNode_noNewMu _ before)⟩, physical.2.1, output⟩
    · intro value middle _ valid
      apply (request_certified clear value middle valid.1).mono
      intro after output returned
      exact ⟨returned.1.1, returned.2 limits valid.2⟩
  cases inputs with
  | nil => simpa only [retainedColumn, ordinary, Bool.false_eq_true, ite_false] using many [] available profile ordinary
  | cons first rest =>
      cases rest with
      | nil => exact ⟨available first List.mem_cons_self, SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.member [first] profile first List.mem_cons_self⟩
      | cons second rest => simpa only [retainedColumn, ordinary, Bool.false_eq_true, ite_false] using many _ available profile ordinary

/-- Actual selection retains the hereditary bounds of original column operands. -/
theorem column_certified (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (_costs : CostHeap before)
    (available : Values before inputs) (limits : Limits) (profile : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children limits inputs) :
    Certified clear (column inputs) before (ValuePost limits) := by
  have facts := semantic.ready.semantic.1.normal.facts
  have closed : MergedColdReaderClosedInputs.ClosedValues inputs := fun value member =>
    SourceCurrentAllocatedFiniteOrdinaryFinite.closed before facts.coherent value (available value member)
      (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node.domain value (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.member inputs profile value member))
  apply bind_certified clear _ _ before
    (fun heap values => Values heap values ∧ SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children limits values) _
  · refine ⟨available, closed, ?_⟩
    intro fuel values after done _
    have physical := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
      (fun _ _ _ => rfl) inputs before semantic available closed values after done
    have selected := SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.selected_inputs clear fuel inputs values before after done
    exact ⟨physical.2.1, SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.children_of_members limits values
      (fun value member => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.member inputs profile value (selected.1 value member))⟩
  · intro values middle effect valid
    exact retained_certified clear values middle effect.semantic effect.costs valid.1 limits valid.2

/-- Large groups replace only their parent guard with the literal Top constraint. -/
theorem large_certified (clear : Guard → Bool) (first : EdgeValue Symbol Guard)
    (rest : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before (first :: rest))
    (limits : Limits) (profile : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows limits (first :: rest)) :
    Certified clear (large Top first rest) before (EdgePost limits) := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (values : List (Value Symbol Guard)) (member : values ∈ columns)
      (value : Value Symbol Guard) (inside : value ∈ values) : ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨children, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ values member value inside
    obtain ⟨edge, outer, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, outer, inner⟩
  apply bind_certified clear _ _ before
    (fun heap values => Language.All₂ (fun _ value => ValuePost limits heap value) columns values) _
  · apply map_certified clear column (fun heap values => Values heap values)
      (fun heap _ value => ValuePost limits heap value)
      (fun _ _ effect values available value member => effect.keeps.available value (available value member))
      (fun _ _ effect _ value ready => value_grows effect _ value ready) columns ?_ before semantic costs ?_
    · intro values member heap semantic costs available
      apply column_certified clear values heap semantic costs available limits
      apply SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.children_of_members
      intro value inside
      obtain ⟨edge, outer, inner⟩ := original values member value inside
      exact SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children.member edge.children (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.children edge (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows.member _ profile edge outer)) value inner
    · intro values member value inside
      obtain ⟨edge, outer, inner⟩ := original values member value inside
      exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner
  · intro values middle effect related
    obtain ⟨available, profiled⟩ := value_collection related
    exact (edge_certified clear _ _ values middle effect.semantic effect.costs available limits
      (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.top_bounds limits) profiled).mono
      (fun _ _ result => ⟨result.1.1, result.2⟩)

private abbrev GroupPost (limits : Limits) (heap : State Symbol Guard) (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ edge ∈ edges, EdgePost limits heap edge

/-- Both literal threshold branches derive bounds for all returned rows. -/
theorem group_certified (clear : Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (limits : Limits) (profile : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows limits edges) :
    Certified clear (group Top edges) before (GroupPost limits) := by
  unfold group
  split
  · have checked := map_certified clear small (fun heap edge => EdgeResident heap edge)
      (fun heap _ edge => EdgePost limits heap edge)
      (fun _ _ effect edge resident => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge resident)
      (fun _ _ effect _ edge ready => edge_grows effect _ edge ready) edges
      (fun edge member heap semantic costs resident => small_certified clear edge heap semantic costs resident
        limits (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows.member edges profile edge member)) before semantic costs resident
    apply checked.mono
    intro heap values related edge member
    obtain ⟨_, _, valid⟩ := all₂_right related edge member
    exact valid
  · cases edges with
    | nil => intro edge member; cases member
    | cons first rest =>
        apply bind_certified clear _ _ before (EdgePost limits) _
          (large_certified clear first rest before semantic costs resident limits profile)
        intro edge _ _ ready value member
        exact (List.mem_singleton.mp member) ▸ ready

/-- Every ordered group completes before the actual normalized node constructor. -/
theorem root_certified (clear : Guard → Bool) (groups : List (List (EdgeValue Symbol Guard)))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : ∀ group ∈ groups, Edges before group) (limits : Limits)
    (profile : ∀ group ∈ groups, SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows limits group) :
    Certified clear (root Top groups) before (ValuePost limits) := by
  apply bind_certified clear _ _ before
    (fun heap outputs => Language.All₂ (fun _ values => GroupPost limits heap values) groups outputs) _
  · apply map_certified clear (group Top) (fun heap edges => Edges heap edges)
      (fun heap _ values => GroupPost limits heap values)
      (fun _ _ effect edges resident edge member => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge (resident edge member))
      (fun _ _ effect _ values valid edge member => edge_grows effect _ edge (valid edge member)) groups
      (fun edges member heap semantic costs resident => group_certified clear edges heap semantic costs resident limits (profile edges member))
      before semantic costs resident
  · intro outputs middle effect related
    have each (edge : EdgeValue Symbol Guard) (member : edge ∈ outputs.flatten) : EdgePost limits middle edge := by
      obtain ⟨output, present, inside⟩ := List.mem_flatten.mp member
      obtain ⟨_, _, valid⟩ := all₂_right related output present
      exact valid edge inside
    exact (node_certified clear outputs.flatten middle effect.semantic effect.costs
      (fun edge member => (each edge member).1) limits
      (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.rows_of_members limits _ (fun edge member => (each edge member).2))).mono (fun _ _ result => ⟨result.1.1, result.2⟩)

/-- The actual full body retains every hereditary initial guard bound. -/
theorem body_certified (clear : Guard → Bool) (input : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before input) (limits : Limits) (profile : SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node limits input) :
    Certified clear (body Top input) before (fun _ output => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node limits output) := by
  cases input with
  | empty => trivial
  | reference | mu | union => cases profile
  | node entry edges depth free =>
      by_cases closed : free = []
      · simp only [body, closed, ite_true]
        have facts := semantic.ready.semantic.1.normal.facts
        have resident := resident_edges before facts.linked _ available.resident
        have grouping := MergedSourceGrouping.groups_correct edges
        exact (root_certified clear _ before semantic costs
          (fun group member edge inside => resident edge (grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, inside⟩)))
          limits (fun group member => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.rows_of_members limits _ (fun edge inside => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows.member edges profile edge
            (grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, inside⟩))))).mono (fun _ _ result => result.2)
      · simp only [body, closed, ite_false]
        exact profile

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeGuardBody
