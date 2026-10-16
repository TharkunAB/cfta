import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection

/-!
# Complete local profile certificate for current merge bodies

Each branch follows the actual source instruction order. Recursive requests
supply their original-relative profile certificate. Selection retains only
original column values. Ordered maps retain the exact result multiplicity.
The certificate does not assume a completed body or its returned profile.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileBody
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds
open SourceCurrentAllocatedFiniteOrdinaryMergeProfileCode
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight ordinaryUnion)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private abbrev ValuePost (rows arity bound : Nat) (heap : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  Available heap value ∧ NodeShape rows arity value ∧ height value ≤ bound

private abbrev EdgePost (rows arity bound : Nat) (heap : State Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop :=
  EdgeResident heap edge ∧ EdgeShape rows arity edge ∧ edgeHeight edge ≤ bound

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem value_grows {before after : State Symbol Guard} (effect : Effect before after)
    (rows arity bound : Nat) (value : Value Symbol Guard) (ready : ValuePost rows arity bound before value) :
    ValuePost rows arity bound after value := ⟨effect.keeps.available value ready.1, ready.2⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem edge_grows {before after : State Symbol Guard} (effect : Effect before after)
    (rows arity bound : Nat) (edge : EdgeValue Symbol Guard) (ready : EdgePost rows arity bound before edge) :
    EdgePost rows arity bound after edge :=
  ⟨InternedEdgeResidency.edge_grows before after effect.keeps.growth edge ready.1, ready.2⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
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

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem value_collection {Input : Type} {inputs : List Input} {values : List (Value Symbol Guard)}
    {rows arity bound : Nat} {heap : State Symbol Guard}
    (related : Language.All₂ (fun _ value => ValuePost rows arity bound heap value) inputs values) :
    Values heap values ∧ ChildrenShape rows arity values ∧ childrenHeight values ≤ bound ∧ values.length = inputs.length := by
  have each : ∀ value ∈ values, ValuePost rows arity bound heap value := by
    intro value member
    obtain ⟨_, _, valid⟩ := all₂_right related value member
    exact valid
  exact ⟨fun value member => (each value member).1,
    SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.children_of_members values (fun value member => (each value member).2.1),
    (MergedOrdinaryHeight.childrenHeight_le values bound).mpr (fun value member => (each value member).2.2), related.length_eq.symm⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem row_collection {Input : Type} {inputs : List Input} {values : List (EdgeValue Symbol Guard)}
    {rows arity bound : Nat} {heap : State Symbol Guard}
    (related : Language.All₂ (fun _ value => EdgePost rows arity bound heap value) inputs values) :
    (∀ value ∈ values, EdgePost rows arity bound heap value) ∧ values.length = inputs.length := by
  constructor
  · intro value member
    obtain ⟨_, _, valid⟩ := all₂_right related value member
    exact valid
  · exact related.length_eq.symm

/-- Small rows retain the original guard and each ordered child result. -/
theorem small_certified (clear : Guard → Bool) (edge : EdgeValue Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : EdgeResident before edge)
    (rows arity bound : Nat) (profile : EdgeShape rows arity edge) (bounded : edgeHeight edge ≤ bound) :
    Certified clear (small edge) before (EdgePost (envelope rows (bound + 1)) arity bound) := by
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  apply bind_certified clear _ _ before
    (fun heap values => Language.All₂ (fun _ value => ValuePost (envelope rows (bound + 1)) arity bound heap value) edge.children values) _
  · apply map_certified clear Code.request (fun heap value => Available heap value)
      (fun heap _ value => ValuePost (envelope rows (bound + 1)) arity bound heap value)
      (fun _ _ effect value ready => effect.keeps.available value ready)
      (fun _ _ effect _ value ready => value_grows effect _ _ _ value ready) edge.children
      ?_ before semantic costs available
    intro value member heap _ _ ready
    apply (request_certified clear value heap ready).mono
    intro after output returned
    have childProfile := ChildrenShape.member edge.children (EdgeShape.children edge profile) value member
    have childBound := Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge edge value member) bounded
    have outputProfile := returned.2 rows arity bound childProfile childBound
    exact ⟨returned.1.1, NodeShape.mono output outputProfile.1 (envelope_succ rows bound) (Nat.le_refl _),
      Nat.le_trans outputProfile.2 childBound⟩
  · intro values middle effect related
    obtain ⟨available, profiled, heightBound, count⟩ := value_collection related
    exact (edge_certified clear _ _ values middle effect.semantic effect.costs available
      (envelope rows (bound + 1)) arity bound profiled (count ▸ EdgeShape.arity edge profile) heightBound).mono
      (fun _ _ result => ⟨result.1.1, result.2⟩)

private theorem retained_certified (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before inputs) (rows arity bound : Nat) (profile : ChildrenShape rows arity inputs)
    (count : inputs.length ≤ rows) (bounded : childrenHeight inputs ≤ bound) :
    Certified clear (retainedColumn inputs) before (ValuePost (envelope rows (bound + 1)) arity bound) := by
  rw [SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.retained_column inputs rows arity profile]
  have many (values : List (Value Symbol Guard)) (available : Values before values)
      (profile : ChildrenShape rows arity values) (count : values.length ≤ rows)
      (bounded : childrenHeight values ≤ bound) :
      Certified clear (.bind (.work (ordinaryUnion values)) Code.request) before
        (ValuePost (envelope rows (bound + 1)) arity bound) := by
    have facts := semantic.ready.semantic.1.normal.facts
    have closed : MergedColdReaderClosedInputs.ClosedValues values := fun value member =>
      SourceCurrentAllocatedFiniteOrdinaryFinite.closed before facts.coherent value (available value member)
        (NodeShape.domain value (ChildrenShape.member values profile value member))
    have ordinary : values.any MergedOrdinaryHeight.recursiveBoundary = false := List.any_eq_false.mpr (by
      intro value member
      have domain := NodeShape.domain value (ChildrenShape.member values profile value member)
      cases domain <;> simp [MergedOrdinaryHeight.recursiveBoundary])
    have physical := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
      values before semantic available closed ordinary
    have output := ordinary_union values before facts.coherent facts.linked available rows arity profile
    have unionProfile := NodeShape.mono _ output.1 (Nat.mul_le_mul_right rows count) (Nat.le_refl _)
    have unionHeight := Nat.le_trans output.2 bounded
    apply bind_certified clear _ _ before (ValuePost (rows * rows) arity bound) _
    · exact ⟨⟨physical.1.1, physical.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
        (InternedShallowHeap.makeNode_noNewMu _ before)⟩, physical.2.1, unionProfile, unionHeight⟩
    · intro value middle _ valid
      apply (request_certified clear value middle valid.1).mono
      intro after output returned
      have result := returned.2 (rows * rows) arity bound valid.2.1 valid.2.2
      exact ⟨returned.1.1, NodeShape.mono output result.1 (column_envelope rows bound) (Nat.le_refl _),
        Nat.le_trans result.2 valid.2.2⟩
  cases inputs with
  | nil => exact many [] available profile count bounded
  | cons first rest =>
      cases rest with
      | nil =>
          exact ⟨available first List.mem_cons_self,
            NodeShape.mono first profile.1 (rows_le_envelope rows (bound + 1)) (Nat.le_refl _),
            (MergedOrdinaryHeight.childrenHeight_le [first] bound).mp bounded first List.mem_cons_self⟩
      | cons second rest => exact many _ available profile count bounded

/-- Selection preserves source profiles and counts before the actual column union. -/
theorem column_certified (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (_costs : CostHeap before)
    (available : Values before inputs) (rows arity bound : Nat) (profile : ChildrenShape rows arity inputs)
    (count : inputs.length ≤ rows) (bounded : childrenHeight inputs ≤ bound) :
    Certified clear (column inputs) before (ValuePost (envelope rows (bound + 1)) arity bound) := by
  have facts := semantic.ready.semantic.1.normal.facts
  have closed : MergedColdReaderClosedInputs.ClosedValues inputs := fun value member =>
    SourceCurrentAllocatedFiniteOrdinaryFinite.closed before facts.coherent value (available value member)
      (NodeShape.domain value (ChildrenShape.member inputs profile value member))
  apply bind_certified clear _ _ before
    (fun heap values => Values heap values ∧ ChildrenShape rows arity values ∧ values.length ≤ rows ∧ childrenHeight values ≤ bound) _
  · refine ⟨available, closed, ?_⟩
    intro fuel values after done _
    have checked := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
      (fun _ _ _ => rfl) inputs before semantic available closed values after done
    have selected := SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.selected_profile
      clear fuel inputs values before after done rows arity profile
    have inside := SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.selected_inputs clear fuel inputs values before after done
    exact ⟨checked.2.1, selected.1, Nat.le_trans selected.2 count,
      (MergedOrdinaryHeight.childrenHeight_le values bound).mpr (fun value member =>
        (MergedOrdinaryHeight.childrenHeight_le inputs bound).mp bounded value (inside.1 value member))⟩
  · intro values middle effect valid
    exact retained_certified clear values middle effect.semantic effect.costs valid.1 rows arity bound
      valid.2.1 valid.2.2.1 valid.2.2.2

/-- Large groups process every column before the literal Top-row constructor. -/
theorem large_certified (clear : Guard → Bool) (top : Guard) (first : EdgeValue Symbol Guard)
    (rest : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before (first :: rest))
    (rows arity bound : Nat) (profile : RowsShape rows arity (first :: rest))
    (count : (first :: rest).length ≤ rows) (bounded : edgesHeight (first :: rest) ≤ bound) :
    Certified clear (large top first rest) before (EdgePost (envelope rows (bound + 1)) arity bound) := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (values : List (Value Symbol Guard)) (member : values ∈ columns)
      (value : Value Symbol Guard) (inside : value ∈ values) : ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨children, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ values member value inside
    obtain ⟨edge, outer, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, outer, inner⟩
  apply bind_certified clear _ _ before
    (fun heap values => Language.All₂ (fun _ value => ValuePost (envelope rows (bound + 1)) arity bound heap value) columns values) _
  · apply map_certified clear column (fun heap values => Values heap values)
      (fun heap _ value => ValuePost (envelope rows (bound + 1)) arity bound heap value)
      (fun _ _ effect values available value member => effect.keeps.available value (available value member))
      (fun _ _ effect _ value ready => value_grows effect _ _ _ value ready) columns ?_ before semantic costs ?_
    · intro values member heap semantic costs available
      have selected := column_inputs (first :: rest) first.children.length rows arity profile values member
      apply column_certified clear values heap semantic costs available rows arity bound selected.1 (Nat.le_trans selected.2 count)
      apply (MergedOrdinaryHeight.childrenHeight_le values bound).mpr
      intro value inside
      obtain ⟨edge, outer, inner⟩ := original values member value inside
      exact Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge edge value inner)
        ((MergedOrdinaryHeight.edgesHeight_le _ bound).mp bounded edge outer)
    · intro values member value inside
      obtain ⟨edge, outer, inner⟩ := original values member value inside
      exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner
  · intro values middle effect related
    obtain ⟨available, profiled, heightBound, lengthBound⟩ := value_collection related
    have count : values.length ≤ arity := by
      rw [lengthBound, MergedPhysicalGroupEdges.columns_length]
      exact EdgeShape.arity first profile.1
    exact (edge_certified clear _ _ values middle effect.semantic effect.costs available
      (envelope rows (bound + 1)) arity bound profiled count heightBound).mono
      (fun _ _ result => ⟨result.1.1, result.2⟩)

private abbrev GroupPost (rows arity bound : Nat) (heap : State Symbol Guard)
    (originals outputs : List (EdgeValue Symbol Guard)) : Prop :=
  outputs.length ≤ originals.length ∧ ∀ edge ∈ outputs, EdgePost rows arity bound heap edge

/-- Both threshold branches retain the original row-count bound and every result profile. -/
theorem group_certified (clear : Guard → Bool) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (rows arity bound : Nat) (profile : RowsShape rows arity edges)
    (count : edges.length ≤ rows) (bounded : edgesHeight edges ≤ bound) :
    Certified clear (group top edges) before (fun heap values => GroupPost (envelope rows (bound + 1)) arity bound heap edges values) := by
  unfold group
  split
  · have checked := map_certified clear small (fun heap edge => EdgeResident heap edge)
      (fun heap _ edge => EdgePost (envelope rows (bound + 1)) arity bound heap edge)
      (fun _ _ effect edge resident => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge resident)
      (fun _ _ effect _ edge ready => edge_grows effect _ _ _ edge ready) edges
      (fun edge member heap semantic costs resident =>
        small_certified clear edge heap semantic costs resident rows arity bound
          (RowsShape.member edges profile edge member)
          ((MergedOrdinaryHeight.edgesHeight_le edges bound).mp bounded edge member))
      before semantic costs resident
    exact checked.mono (fun _ _ related =>
      ⟨Nat.le_of_eq (row_collection related).2, (row_collection related).1⟩)
  · cases edges with
    | nil => exact ⟨Nat.le_refl _, fun _ member => by cases member⟩
    | cons first rest =>
        apply bind_certified clear _ _ before (EdgePost (envelope rows (bound + 1)) arity bound) _
          (large_certified clear top first rest before semantic costs resident rows arity bound profile count bounded)
        intro edge _ _ ready
        exact ⟨by simp, fun value member => (List.mem_singleton.mp member) ▸ ready⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem group_length_le_flatten {Input : Type} (groups : List (List Input)) (group : List Input)
    (member : group ∈ groups) : group.length ≤ groups.flatten.length := by
  induction groups with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [List.flatten_cons, List.length_append] using Nat.le_add_right group.length rest.flatten.length
      · simpa only [List.flatten_cons, List.length_append] using
          Nat.le_trans (ih member) (Nat.le_add_left rest.flatten.length first.length)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem flattened_length {originals outputs : List (List (EdgeValue Symbol Guard))}
    {rows arity bound : Nat} {heap : State Symbol Guard}
    (related : Language.All₂ (GroupPost rows arity bound heap) originals outputs) :
    outputs.flatten.length ≤ originals.flatten.length := by
  induction related with
  | nil => exact Nat.le_refl _
  | cons first rest ih => simpa only [List.flatten_cons, List.length_append] using Nat.add_le_add first.1 ih

/-- All actual groups finish before the final normalized node constructor. -/
theorem root_certified (clear : Guard → Bool) (top : Guard) (groups : List (List (EdgeValue Symbol Guard)))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : ∀ group ∈ groups, Edges before group) (rows arity bound : Nat)
    (profile : RowsShape rows arity groups.flatten) (count : groups.flatten.length ≤ rows)
    (bounded : edgesHeight groups.flatten ≤ bound) :
    Certified clear (root top groups) before (ValuePost (envelope rows (bound + 1)) arity (bound + 1)) := by
  apply bind_certified clear _ _ before
    (fun heap outputs => Language.All₂ (GroupPost (envelope rows (bound + 1)) arity bound heap) groups outputs) _
  · apply map_certified clear (group top) (fun heap edges => Edges heap edges)
      (GroupPost (envelope rows (bound + 1)) arity bound)
      (fun _ _ effect edges resident edge member => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge (resident edge member))
      (fun _ _ effect originals values valid => ⟨valid.1, fun edge member => edge_grows effect _ _ _ edge (valid.2 edge member)⟩)
      groups ?_ before semantic costs resident
    intro edges member heap semantic costs resident
    have inside (edge : EdgeValue Symbol Guard) (present : edge ∈ edges) : edge ∈ groups.flatten :=
      List.mem_flatten.mpr ⟨edges, member, present⟩
    exact group_certified clear top edges heap semantic costs resident rows arity bound
      (SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.rows_subset groups.flatten edges profile inside)
      (Nat.le_trans (group_length_le_flatten groups edges member) count)
      ((MergedOrdinaryHeight.edgesHeight_le edges bound).mpr (fun edge present =>
        (MergedOrdinaryHeight.edgesHeight_le groups.flatten bound).mp bounded edge (inside edge present)))
  · intro outputs middle effect related
    have each (edge : EdgeValue Symbol Guard) (member : edge ∈ outputs.flatten) :
        EdgePost (envelope rows (bound + 1)) arity bound middle edge := by
      obtain ⟨output, present, inside⟩ := List.mem_flatten.mp member
      obtain ⟨_, _, valid⟩ := all₂_right related output present
      exact valid.2 edge inside
    exact (node_certified clear outputs.flatten middle effect.semantic effect.costs
      (fun edge member => (each edge member).1) (envelope rows (bound + 1)) arity (bound + 1)
      (SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.rows_of_members _ (fun edge member => (each edge member).2.1))
      (Nat.le_trans (Nat.le_trans (flattened_length related) count) (rows_le_envelope rows (bound + 1)))
      (fun edge member => Nat.succ_le_succ (each edge member).2.2)).mono
      (fun _ _ result => ⟨result.1.1, result.2⟩)

/-- The full ordinary body derives its fixed profile at the same actual local return. -/
theorem body_certified (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before input) (rows arity : Nat) (profile : NodeShape rows arity input) :
    Certified clear (body top input) before
      (fun _ output => NodeShape (envelope rows (height input)) arity output ∧ height output ≤ height input) := by
  cases input with
  | empty => exact ⟨True.intro, Nat.le_refl _⟩
  | reference | mu | union => cases profile
  | node entry edges depth free =>
      by_cases closed : free = []
      · simp only [body, closed, ite_true]
        have facts := semantic.ready.semantic.1.normal.facts
        have resident := resident_edges before facts.linked _ available.resident
        have grouping := MergedSourceGrouping.groups_correct edges
        have sameProfile : RowsShape rows arity (MergedSourceGrouping.groups edges).flatten :=
          SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.rows_of_members _ (fun edge member =>
            RowsShape.member edges profile.2 edge (grouping.partition.mem_iff.mp member))
        have sameHeight : edgesHeight (MergedSourceGrouping.groups edges).flatten ≤ edgesHeight edges :=
          (MergedOrdinaryHeight.edgesHeight_le _ _).mpr (fun edge member =>
            (MergedOrdinaryHeight.edgesHeight_le edges _).mp (Nat.le_refl _) edge (grouping.partition.mem_iff.mp member))
        exact (root_certified clear top _ before semantic costs
          (fun group member edge inside => resident edge (grouping.partition.mem_iff.mp (List.mem_flatten.mpr ⟨group, member, inside⟩)))
          rows arity (edgesHeight edges) sameProfile
          (Nat.le_trans (Nat.le_of_eq grouping.partition.length_eq) profile.1) sameHeight).mono (fun _ _ result => result.2)
      · simp only [body, closed, ite_false]
        exact ⟨NodeShape.mono _ profile (rows_le_envelope rows _) (Nat.le_refl _), Nat.le_refl _⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileBody
