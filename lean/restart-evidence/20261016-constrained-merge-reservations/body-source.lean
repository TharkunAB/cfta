import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeSelection

/-!
# Complete constructor budgets for current ordinary merge bodies

Each branch retains actual ordered constructor traces. Recursive requests
use the universal budget for their exact original input. Ordinary selection
returns at the same heap. No successful body or returned count is supplied.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetBody
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect ValueReady EdgeReady value_grows edge_grows)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode
open SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers (nodeBudget edgeBudget)
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight ordinaryUnion)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private abbrev lowerNodes (rows arity bound : Nat) := nodeBudget (rows * rows) arity bound
private abbrev lowerEdges (rows arity bound : Nat) := edgeBudget (rows * rows) arity bound

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem sum_constant {Input : Type} (inputs : List Input) (cost : Nat) :
    (inputs.map (fun _ => cost)).sum = inputs.length * cost := by
  induction inputs with
  | nil => simp
  | cons first rest ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul, Nat.add_comm]

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem sum_lengths {Input : Type} (inputs : List (List Input)) (cost : Nat) :
    (inputs.map (fun values => values.length * cost)).sum = inputs.flatten.length * cost := by
  induction inputs with
  | nil => simp
  | cons first rest ih => simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append, ih, Nat.add_mul]

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
    {heap : State Symbol Guard} (related : Language.All₂ (fun _ value => ValueReady heap value) inputs values) :
    Values heap values ∧ ClosedValues values := by
  constructor <;> intro value member
  · obtain ⟨_, _, valid⟩ := all₂_right related value member; exact valid.1
  · obtain ⟨_, _, valid⟩ := all₂_right related value member; exact valid.2

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem closed_values (before : State Symbol Guard) (semantic : SemanticReady before)
    (values : List (Value Symbol Guard)) (available : Values before values)
    (rows arity : Nat) (profile : ChildrenShape rows arity values) : ClosedValues values :=
  fun value member => SourceCurrentAllocatedFiniteOrdinaryFinite.closed before
    semantic.ready.semantic.1.normal.facts.coherent value (available value member)
    (NodeShape.domain value (ChildrenShape.member values profile value member))

/-- Small rows charge their actual ordered children and one literal row constructor. -/
theorem small_certified (clear : Guard → Bool) (edge : EdgeValue Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : EdgeResident before edge)
    (rows arity bound : Nat) (profile : EdgeShape rows arity edge) (bounded : edgeHeight edge ≤ bound) :
    Certified clear (small edge) before (fun after result =>
      Budget before after (edge.children.length * lowerNodes rows arity bound)
        (1 + edge.children.length * lowerEdges rows arity bound) ∧ EdgeReady after result) := by
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
  apply bind_certified clear _ _ before
    (fun heap values => Budget before heap (edge.children.length * lowerNodes rows arity bound)
      (edge.children.length * lowerEdges rows arity bound) ∧
      Language.All₂ (fun _ value => ValueReady heap value) edge.children values) _
  · have checked := map_certified clear Code.request (fun heap value => Available heap value)
      (fun heap _ value => ValueReady heap value)
      (fun _ _ effect value ready => effect.keeps.available value ready)
      (fun _ _ effect _ value ready => value_grows effect value ready)
      (fun _ => lowerNodes rows arity bound) (fun _ => lowerEdges rows arity bound) edge.children
      (fun value member heap semantic _ ready => by
        apply (request_certified clear value heap ready).mono
        intro after output returned
        have childProfile := ChildrenShape.member edge.children (EdgeShape.children edge profile) value member
        have childBound := Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge edge value member) bounded
        have wideProfile := NodeShape.mono value childProfile (Nat.le_mul_self rows) (Nat.le_refl _)
        have childClosed := SourceCurrentAllocatedFiniteOrdinaryFinite.closed heap
          semantic.ready.semantic.1.normal.facts.coherent value ready (NodeShape.domain value childProfile)
        exact ⟨returned.2 (rows * rows) arity bound wideProfile childBound,
          returned.1.1.1, returned.1.1.2 childClosed⟩)
      before semantic costs available
    simpa only [sum_constant] using checked
  · intro values middle effect ready
    have collected := value_collection ready.2
    exact (edge_certified clear _ _ values middle effect.semantic effect.costs collected.1 collected.2).mono
      (fun _ _ result => ⟨(ready.1.trans result.1).mono (by omega) (by omega), result.2⟩)

private theorem retained_certified (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before inputs) (rows arity bound : Nat) (profile : ChildrenShape rows arity inputs)
    (count : inputs.length ≤ rows) (bounded : childrenHeight inputs ≤ bound) :
    Certified clear (retainedColumn inputs) before (fun after result =>
      Budget before after (1 + lowerNodes rows arity bound) (lowerEdges rows arity bound) ∧ ValueReady after result) := by
  rw [SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.retained_column inputs rows arity profile]
  have many (values : List (Value Symbol Guard)) (available : Values before values)
      (profile : ChildrenShape rows arity values) (count : values.length ≤ rows)
      (bounded : childrenHeight values ≤ bound) :
      Certified clear (.bind (.work (ordinaryUnion values)) Code.request) before
        (fun after result => Budget before after (1 + lowerNodes rows arity bound) (lowerEdges rows arity bound) ∧ ValueReady after result) := by
    have facts := semantic.ready.semantic.1.normal.facts
    have resident : Edges before (values.flatMap nodeEdges) := by
      intro edge member
      obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
      exact resident_edges before facts.linked value (available value present).resident edge included
    have rowProfile := SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds.union_rows values rows arity profile
    have closed : ClosedEdges (values.flatMap nodeEdges) := by
      intro edge member value included
      exact SourceCurrentAllocatedFiniteOrdinaryFinite.closed before facts.coherent value
        (facts.cached.edges edge.entry.key edge (resident edge member) value included)
        (NodeShape.domain value (ChildrenShape.member edge.children
          (EdgeShape.children edge (RowsShape.member _ rowProfile edge member)) value included))
    have physical := node_certified clear (values.flatMap nodeEdges) before semantic costs resident closed
    have sourceProfile := SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds.ordinary_union values before
      facts.coherent facts.linked available rows arity profile
    apply bind_certified clear _ _ before
      (fun heap value => Budget before heap 1 0 ∧ ValueReady heap value ∧
        NodeShape (rows * rows) arity value ∧ height value ≤ bound) _
    · exact ⟨physical.1, physical.2.1, physical.2.2,
        NodeShape.mono _ sourceProfile.1 (Nat.mul_le_mul_right rows count) (Nat.le_refl _),
        Nat.le_trans sourceProfile.2 bounded⟩
    · intro value middle _ ready
      apply (request_certified clear value middle ready.2.1.1).mono
      intro after result returned
      have recursive := returned.2 (rows * rows) arity bound ready.2.2.1 ready.2.2.2
      exact ⟨by simpa only [lowerNodes, lowerEdges, Nat.zero_add] using ready.1.trans recursive,
        returned.1.1.1, returned.1.1.2 ready.2.1.2⟩
  cases inputs with
  | nil => exact many [] available profile count bounded
  | cons first rest =>
      cases rest with
      | nil =>
          exact ⟨(Budget.refl before).mono (Nat.zero_le _) (Nat.zero_le _),
            available first List.mem_cons_self, closed_values before semantic [first] available rows arity profile first List.mem_cons_self⟩
      | cons second rest => exact many _ available profile count bounded

/-- Ordinary selection contributes no constructor trace before the retained-column work. -/
theorem column_certified (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (_costs : CostHeap before)
    (available : Values before inputs) (rows arity bound : Nat) (profile : ChildrenShape rows arity inputs)
    (count : inputs.length ≤ rows) (bounded : childrenHeight inputs ≤ bound) :
    Certified clear (column inputs) before (fun after result =>
      Budget before after (1 + lowerNodes rows arity bound) (lowerEdges rows arity bound) ∧ ValueReady after result) := by
  have closed := closed_values before semantic inputs available rows arity profile
  apply bind_certified clear _ _ before
    (fun heap values => heap = before ∧ Values heap values ∧ ChildrenShape rows arity values ∧
      values.length ≤ rows ∧ childrenHeight values ≤ bound) _
  · refine ⟨available, closed, ?_⟩
    intro fuel values after done _
    have same := (SourceCurrentAllocatedFiniteOrdinaryMergeSelection.done profile done).2
    subst after
    have selected := SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.selected_profile
      clear fuel inputs values before before done rows arity profile
    have inside := SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.selected_inputs clear fuel inputs values before before done
    exact ⟨rfl, (fun value member => available value (inside.1 value member)), selected.1, Nat.le_trans selected.2 count,
      (MergedOrdinaryHeight.childrenHeight_le values bound).mpr (fun value member =>
        (MergedOrdinaryHeight.childrenHeight_le inputs bound).mp bounded value (inside.1 value member))⟩
  · intro values middle effect ready
    rcases ready with ⟨same, available, profiled, count, bounded⟩
    subst middle
    exact retained_certified clear values before effect.semantic effect.costs available rows arity bound profiled count bounded

/-- Large groups charge each source column, then one literal Top-row request. -/
theorem large_certified (clear : Guard → Bool) (top : Guard) (first : EdgeValue Symbol Guard)
    (rest : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before (first :: rest))
    (rows arity bound : Nat) (profile : RowsShape rows arity (first :: rest))
    (count : (first :: rest).length ≤ rows) (bounded : edgesHeight (first :: rest) ≤ bound) :
    Certified clear (large top first rest) before (fun after result =>
      Budget before after (arity * (1 + lowerNodes rows arity bound))
        (1 + arity * lowerEdges rows arity bound) ∧ EdgeReady after result) := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (values : List (Value Symbol Guard)) (member : values ∈ columns)
      (value : Value Symbol Guard) (inside : value ∈ values) : ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨children, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ values member value inside
    obtain ⟨edge, outer, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, outer, inner⟩
  apply bind_certified clear _ _ before
    (fun heap values => Budget before heap (columns.length * (1 + lowerNodes rows arity bound))
      (columns.length * lowerEdges rows arity bound) ∧ Language.All₂ (fun _ value => ValueReady heap value) columns values) _
  · have checked := map_certified clear column (fun heap values => Values heap values)
      (fun heap _ value => ValueReady heap value)
      (fun _ _ effect values available value member => effect.keeps.available value (available value member))
      (fun _ _ effect _ value ready => value_grows effect value ready)
      (fun _ => 1 + lowerNodes rows arity bound) (fun _ => lowerEdges rows arity bound) columns
      (fun values member heap semantic costs available => by
        have selected := SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds.column_inputs
          (first :: rest) first.children.length rows arity profile values member
        apply column_certified clear values heap semantic costs available rows arity bound selected.1 (Nat.le_trans selected.2 count)
        apply (MergedOrdinaryHeight.childrenHeight_le values bound).mpr
        intro value inside
        obtain ⟨edge, outer, inner⟩ := original values member value inside
        exact Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryDomain.child_le_edge edge value inner)
          ((MergedOrdinaryHeight.edgesHeight_le _ bound).mp bounded edge outer))
      before semantic costs (fun values member value inside => by
        obtain ⟨edge, outer, inner⟩ := original values member value inside
        exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner)
    simpa only [sum_constant] using checked
  · intro values middle effect ready
    have collected := value_collection ready.2
    have arityBound : columns.length ≤ arity := by
      rw [MergedPhysicalGroupEdges.columns_length]
      exact EdgeShape.arity first profile.1
    exact (edge_certified clear _ _ values middle effect.semantic effect.costs collected.1 collected.2).mono
      (fun _ _ result => ⟨(ready.1.trans result.1).mono
        (by simpa only [Nat.add_zero] using Nat.mul_le_mul_right (1 + lowerNodes rows arity bound) arityBound)
        (by have h := Nat.mul_le_mul_right (lowerEdges rows arity bound) arityBound; omega), result.2⟩)

/-- Each threshold branch is bounded by the original group length. -/
theorem group_certified (clear : Guard → Bool) (top : Guard) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (rows arity bound : Nat) (profile : RowsShape rows arity edges)
    (count : edges.length ≤ rows) (bounded : edgesHeight edges ≤ bound) :
    Certified clear (group top edges) before (fun after outputs =>
      Budget before after (edges.length * (arity * (1 + lowerNodes rows arity bound)))
        (edges.length * (1 + arity * lowerEdges rows arity bound)) ∧ ∀ edge ∈ outputs, EdgeReady after edge) := by
  unfold group
  split
  · have checked := map_certified clear small (fun heap edge => EdgeResident heap edge)
      (fun heap _ edge => EdgeReady heap edge)
      (fun _ _ effect edge resident => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge resident)
      (fun _ _ effect _ edge ready => edge_grows effect edge ready)
      (fun _ => arity * (1 + lowerNodes rows arity bound)) (fun _ => 1 + arity * lowerEdges rows arity bound) edges
      (fun edge member heap semantic costs resident => by
        have rowProfile := RowsShape.member edges profile edge member
        apply (small_certified clear edge heap semantic costs resident rows arity bound rowProfile
          ((MergedOrdinaryHeight.edgesHeight_le edges bound).mp bounded edge member)).mono
        intro after output result
        have arityBound := EdgeShape.arity edge rowProfile
        have nbound := Nat.le_trans (Nat.mul_le_mul_right (lowerNodes rows arity bound) arityBound)
          (Nat.mul_le_mul_left arity (Nat.le_add_left (lowerNodes rows arity bound) 1))
        have ebound := Nat.add_le_add_left (Nat.mul_le_mul_right (lowerEdges rows arity bound) arityBound) 1
        exact ⟨result.1.mono nbound ebound, result.2⟩)
      before semantic costs resident
    apply checked.mono
    intro _ outputs result
    refine ⟨?_, ?_⟩
    · simpa only [sum_constant] using result.1
    · intro edge member
      obtain ⟨_, _, ready⟩ := all₂_right result.2 edge member
      exact ready
  · cases edges with
    | nil => exact ⟨by simpa only [List.length_nil, Nat.zero_mul] using Budget.refl before,
        fun _ member => by cases member⟩
    | cons first rest =>
        apply bind_certified clear _ _ before
          (fun heap edge => Budget before heap (arity * (1 + lowerNodes rows arity bound))
            (1 + arity * lowerEdges rows arity bound) ∧ EdgeReady heap edge) _
          (large_certified clear top first rest before semantic costs resident rows arity bound profile count bounded)
        intro edge _ _ ready
        have positive : 1 ≤ (first :: rest).length := by simp
        have nodes := Nat.mul_le_mul_right (arity * (1 + lowerNodes rows arity bound)) positive
        have edges := Nat.mul_le_mul_right (1 + arity * lowerEdges rows arity bound) positive
        exact ⟨ready.1.mono (by simpa only [Nat.one_mul] using nodes)
          (by simpa only [Nat.one_mul] using edges),
          fun value member => (List.mem_singleton.mp member) ▸ ready.2⟩

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

/-- Every ordered group contributes its own source-length budget before the final node request. -/
theorem root_certified (clear : Guard → Bool) (top : Guard) (groups : List (List (EdgeValue Symbol Guard)))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : ∀ group ∈ groups, Edges before group) (rows arity bound : Nat)
    (profile : RowsShape rows arity groups.flatten) (count : groups.flatten.length ≤ rows)
    (bounded : edgesHeight groups.flatten ≤ bound) :
    Certified clear (root top groups) before (fun after result =>
      Budget before after (nodeBudget rows arity (bound + 1)) (edgeBudget rows arity (bound + 1)) ∧ ValueReady after result) := by
  apply bind_certified clear _ _ before
    (fun heap outputs => Budget before heap
      (groups.flatten.length * (arity * (1 + lowerNodes rows arity bound)))
      (groups.flatten.length * (1 + arity * lowerEdges rows arity bound)) ∧
      Language.All₂ (fun _ values => ∀ edge ∈ values, EdgeReady heap edge) groups outputs) _
  · have checked := map_certified clear (group top) (fun heap edges => Edges heap edges)
      (fun heap _ values => ∀ edge ∈ values, EdgeReady heap edge)
      (fun _ _ effect edges resident edge member => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge (resident edge member))
      (fun _ _ effect _ values ready edge member => edge_grows effect edge (ready edge member))
      (fun edges => edges.length * (arity * (1 + lowerNodes rows arity bound)))
      (fun edges => edges.length * (1 + arity * lowerEdges rows arity bound)) groups
      (fun edges member heap semantic costs resident => by
        have inside (edge : EdgeValue Symbol Guard) (present : edge ∈ edges) : edge ∈ groups.flatten :=
          List.mem_flatten.mpr ⟨edges, member, present⟩
        exact group_certified clear top edges heap semantic costs resident rows arity bound
          (SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.rows_subset groups.flatten edges profile inside)
          (Nat.le_trans (group_length_le_flatten groups edges member) count)
          ((MergedOrdinaryHeight.edgesHeight_le edges bound).mpr (fun edge present =>
            (MergedOrdinaryHeight.edgesHeight_le groups.flatten bound).mp bounded edge (inside edge present))))
      before semantic costs resident
    simpa only [sum_lengths] using checked
  · intro outputs middle effect ready
    have each (edge : EdgeValue Symbol Guard) (member : edge ∈ outputs.flatten) : EdgeReady middle edge := by
      obtain ⟨values, present, inside⟩ := List.mem_flatten.mp member
      obtain ⟨_, _, valid⟩ := all₂_right ready.2 values present
      exact valid edge inside
    exact (node_certified clear outputs.flatten middle effect.semantic effect.costs
      (fun edge member => (each edge member).1) (fun edge member => (each edge member).2)).mono
      (fun _ _ result => ⟨(ready.1.trans result.1).mono
        (by have h := Nat.mul_le_mul_right (arity * (1 + lowerNodes rows arity bound)) count
            simp only [nodeBudget, lowerNodes, Nat.mul_assoc] at *
            omega)
        (by have h := Nat.mul_le_mul_right (1 + arity * lowerEdges rows arity bound) count
            simp only [edgeBudget, lowerEdges, Nat.mul_add, Nat.mul_assoc, Nat.mul_one] at *
            omega), result.2⟩)

/-- The full body obtains its original-height constructor budget from initial input facts. -/
theorem body_certified (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before input) (rows arity : Nat) (profile : NodeShape rows arity input) :
    Certified clear (body top input) before (fun after _ =>
      Budget before after (nodeBudget rows arity (height input)) (edgeBudget rows arity (height input))) := by
  cases input with
  | empty => exact Budget.refl before
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
          (Nat.le_trans (Nat.le_of_eq grouping.partition.length_eq) profile.1) sameHeight).mono (fun _ _ result => result.1)
      · simp only [body, closed, ite_false]
        exact (Budget.refl before).mono (Nat.zero_le _) (Nat.zero_le _)

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetBody
