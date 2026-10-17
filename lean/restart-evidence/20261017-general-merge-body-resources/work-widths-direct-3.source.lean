import MicroCFTA.SourceCurrentMemoMergeResourceCertificate
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection

/-!
# Constructor widths of the general Merge body

Original payload mass bounds literal row and column counts. Ordered requests
retain list length even when they return larger values. Selection retains
original occurrences. Each work instruction checks its actual current heap.
This local certificate does not assert recursive Merge completion.
-/
namespace MicroCFTA.SourceCurrentMemoMergeWorkWidths
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect Contract ValueReady EdgeReady value_grows edge_grows)
open SourceCurrentMemoMergeResourceCertificate (Checked bind_checked)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

private theorem values_length (values : List (Value Symbol Guard)) :
    values.length ≤ InternedValueMass.values values := by
  rw [InternedValueMass.values_eq_length_sum]
  omega

private theorem edges_length (edges : List (EdgeValue Symbol Guard)) :
    edges.length ≤ InternedValueMass.edges edges := by
  rw [InternedValueMass.edges_eq_length_sum]
  omega

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Ordered calls retain physical results and their exact occurrence count. -/
theorem map_checked (width : Nat) (clear : Guard → Bool) (call : Request → Code Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop) (post : State Symbol Guard → Output → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (postGrows : ∀ before after, Effect before after → ∀ value, post before value → post after value)
    (requests : List Request)
    (checked : ∀ request ∈ requests, ∀ before, SemanticReady before → CostHeap before → pre before request →
      Checked width clear (call request) before post)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (inputs : ∀ request ∈ requests, pre before request) :
    Checked width clear (SourceCurrentMemoMergeGraph.map call requests) before
      (fun after values => (∀ value ∈ values, post after value) ∧ values.length = requests.length) := by
  induction requests generalizing before with
  | nil => exact ⟨by simp, rfl⟩
  | cons first rest ih =>
      apply bind_checked width clear _ _ before post _
        (checked first List.mem_cons_self before semantic costs (inputs first List.mem_cons_self))
      intro value middle effect valid
      apply bind_checked width clear _ _ middle _ _
        (ih (fun request member => checked request (List.mem_cons_of_mem _ member)) middle effect.semantic effect.costs
          (fun request member => preGrows before middle effect request (inputs request (List.mem_cons_of_mem _ member))))
      intro values after later ready
      refine ⟨?_, congrArg Nat.succ ready.2⟩
      intro output member
      rcases List.mem_cons.mp member with rfl | member
      · exact postGrows middle after later _ valid
      · exact ready.1 output member

/-- Edge work checks its literal child width at every current heap bound. -/
theorem edge_checked (width : Nat) (clear : Guard → Bool) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before values) (closed : ClosedValues values) (length : values.length ≤ width) :
    Checked width clear (.work (makeEdge symbol guard values)) before EdgeReady := by
  have physical := SourceCurrentMemoMergeEffects.edge_certified clear symbol guard values before semantic costs available closed
  exact ⟨physical.1, fun bound fits =>
    (SourceCurrentMemoMergeResourceControl.edge symbol guard values before bound width fits available length).1, physical.2⟩

/-- Node work checks its complete literal row list before normalization. -/
theorem node_checked (width : Nat) (clear : Guard → Bool) (rows : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before rows) (closed : ClosedEdges rows) (length : rows.length ≤ width) :
    Checked width clear (.work (makeNode rows)) before ValueReady := by
  have physical := SourceCurrentMemoMergeEffects.node_certified clear rows before semantic costs resident closed
  exact ⟨physical.1, fun bound fits =>
    (SourceCurrentMemoMergeResourceControl.node rows before bound width fits resident length).1, physical.2⟩

/-- Recursive requests use their actual returned physical result. -/
theorem request_checked (width : Nat)
    (clear : Guard → Bool) (value : Value Symbol Guard) (before : State Symbol Guard)
    (ready : ValueReady before value) : Checked width clear (.request value) before ValueReady :=
  ⟨ready.1, fun _ _ _ returned => ⟨returned.1, returned.2 ready.2⟩⟩

/-- Retained columns derive all constructor and recursive request obligations. -/
theorem retained_checked (width : Nat)
    (clear : Guard → Bool) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before inputs)
    (closed : ClosedValues inputs) (length : inputs.length ≤ width) : Checked width clear (retainedColumn inputs) before ValueReady := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values) (closed : ClosedValues values) (length : values.length ≤ width) :
      Checked width clear
        (if values.any MergedOrdinaryHeight.recursiveBoundary then .work (makeUnion values)
          else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) before ValueReady := by
    by_cases boundary : values.any MergedOrdinaryHeight.recursiveBoundary = true
    · simp only [boundary, ite_true]
      have checked := SourceMergedCache.union values before semantic available closed
      exact ⟨⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
        (InternedShallowHeap.makeUnion_noNewMu values before)⟩,
        (fun bound fits => (SourceCurrentMemoMergeResourceControl.union values before bound width fits available length).1), checked.2⟩
    · simp only [boundary, Bool.false_eq_true, ite_false]
      have checked := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
        values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      apply bind_checked width clear (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request before ValueReady _
        ⟨⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
          (InternedShallowHeap.makeNode_noNewMu _ before)⟩,
          (fun bound fits => (SourceCurrentMemoMergeResourceControl.ordinaryUnion values before bound width fits available length).1), checked.2.1, checked.2.2.1⟩
      exact fun value middle _ ready => request_checked width clear value middle ready
  cases inputs with
  | nil => exact branches [] available closed length
  | cons first rest =>
      cases rest with
      | nil => exact ⟨available first List.mem_cons_self, closed first List.mem_cons_self⟩
      | cons second rest => exact branches (first :: second :: rest) available closed length

/-- Selection retains actual original values before retained-column normalization. -/
theorem column_checked (width : Nat)
    (clear : Guard → Bool) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (_costs : CostHeap before) (available : Values before inputs)
    (closed : ClosedValues inputs) (length : inputs.length ≤ width) : Checked width clear (column inputs) before ValueReady := by
  apply bind_checked width clear _ _ before (fun heap values => Values heap values ∧ ClosedValues values ∧ values.length ≤ width) _
  · refine ⟨available, closed, ?_⟩
    intro fuel values after done effect
    have checked := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
      (fun _ _ _ => rfl) inputs before semantic available closed values after done
    have selected := SourceCurrentAllocatedFiniteOrdinaryMergeProfileSelection.selected_inputs clear fuel inputs values before after done
    exact ⟨checked.2.1, checked.2.2.1, Nat.le_trans selected.2 length⟩
  · intro values middle effect ready
    exact retained_checked width clear values middle effect.semantic effect.costs ready.1 ready.2.1 ready.2.2

/-- Small rows check each actual child request before construction. -/
theorem small_checked (width : Nat)
    (clear : Guard → Bool) (edge : EdgeValue Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (ready : EdgeReady before edge) (length : edge.children.length ≤ width) :
    Checked width clear (small edge) before EdgeReady := by
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge ready.1
  apply bind_checked width clear _ _ before (fun heap values => (∀ value ∈ values, ValueReady heap value) ∧ values.length = edge.children.length) _
    (map_checked width clear Code.request ValueReady ValueReady
      (fun _ _ effect value ready => value_grows effect value ready)
      (fun _ _ effect value ready => value_grows effect value ready) edge.children
      (fun value _ heap _ _ ready => request_checked width clear value heap ready) before semantic costs
      (fun value member => ⟨available value member, ready.2 value member⟩))
  intro values middle effect valid
  exact edge_checked width clear _ _ values middle effect.semantic effect.costs
    (fun value member => (valid.1 value member).1) (fun value member => (valid.1 value member).2)
    (by rw [valid.2]; exact length)

/-- Large groups check actual column inputs derived from their original rows. -/
theorem large_checked (width : Nat)
    (clear : Guard → Bool) (top : Guard) (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before (first :: rest)) (closed : ClosedEdges (first :: rest))
    (rowLength : (first :: rest).length ≤ width) (childLength : first.children.length ≤ width) :
    Checked width clear (large top first rest) before EdgeReady := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard) (included : value ∈ column) :
      ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  apply bind_checked width clear _ _ before (fun heap values => (∀ value ∈ values, ValueReady heap value) ∧ values.length = columns.length) _
    (map_checked width clear column (fun heap values => Values heap values ∧ ClosedValues values ∧ values.length ≤ width) ValueReady
      (fun _ _ effect _ ready => ⟨(fun value member => effect.keeps.available _ (ready.1 value member)), ready.2⟩)
      (fun _ _ effect value ready => value_grows effect value ready) columns
      (fun values _ heap semantic costs ready => column_checked width clear values heap semantic costs ready.1 ready.2.1 ready.2.2)
      before semantic costs (fun column member => ⟨(by
        intro value included
        obtain ⟨edge, outer, inner⟩ := original column member value included
        exact semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge (resident edge outer) value inner), (by
        intro value included
        obtain ⟨edge, outer, inner⟩ := original column member value included
        exact closed edge outer value inner), (by
        have small := SourceCurrentAllocatedFiniteOrdinaryMergeProfileBounds.column_length
          ((first :: rest).map EdgeValue.children) first.children.length column member
        exact Nat.le_trans small (by simpa only [List.length_map] using rowLength))⟩))
  intro values middle effect valid
  exact edge_checked width clear _ _ values middle effect.semantic effect.costs
    (fun value member => (valid.1 value member).1) (fun value member => (valid.1 value member).2)
    (by rw [valid.2, MergedPhysicalGroupEdges.columns_length]; exact childLength)

/-- Both threshold branches retain physical rows and the original row bound. -/
theorem group_checked (width bound : Nat) (clear : Guard → Bool) (top : Guard)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : ClosedEdges edges)
    (length : edges.length ≤ bound) (children : ∀ edge ∈ edges, edge.children.length ≤ width)
    (enough : bound ≤ width) :
    Checked width clear (group top edges) before
      (fun heap rows => (∀ edge ∈ rows, EdgeReady heap edge) ∧ rows.length ≤ bound) := by
  unfold group
  split
  · exact (map_checked width clear small EdgeReady EdgeReady
      (fun _ _ effect edge ready => edge_grows effect edge ready)
      (fun _ _ effect edge ready => edge_grows effect edge ready) edges
      (fun edge member heap semantic costs ready => small_checked width clear edge heap semantic costs ready (children edge member))
      before semantic costs (fun edge member => ⟨resident edge member, closed edge member⟩)).mono
      (fun _ _ ready => ⟨ready.1, by rw [ready.2]; exact length⟩)
  · cases edges with
    | nil => simp_all
    | cons first rest =>
        apply bind_checked width clear _ _ before EdgeReady _
          (large_checked width clear top first rest before semantic costs resident closed
            (Nat.le_trans length enough) (children first List.mem_cons_self))
        intro edge middle _ ready
        refine ⟨?_, ?_⟩
        · intro value member
          exact List.mem_singleton.mp member ▸ ready
        · simp only [List.length_singleton]
          have positive : 1 ≤ (first :: rest).length := by simp
          exact Nat.le_trans positive length

private theorem flatten_length (values : List (List Input)) (bound : Nat)
    (small : ∀ value ∈ values, value.length ≤ bound) : values.flatten.length ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons first rest ih =>
      have firstBound := small first List.mem_cons_self
      have tailBound := ih (fun value member => small value (List.mem_cons_of_mem _ member))
      simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- Ordered group counts bound the final literal row list before node work. -/
theorem root_checked (width bound : Nat) (clear : Guard → Bool) (top : Guard)
    (groups : List (List (EdgeValue Symbol Guard))) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : ∀ group ∈ groups, Edges before group) (closed : ∀ group ∈ groups, ClosedEdges group)
    (groupLength : groups.length ≤ bound) (rowLength : ∀ group ∈ groups, group.length ≤ bound)
    (children : ∀ group ∈ groups, ∀ edge ∈ group, edge.children.length ≤ width)
    (enough : bound ≤ width) (square : bound * bound ≤ width) :
    Checked width clear (root top groups) before ValueReady := by
  apply bind_checked width clear _ _ before
    (fun heap rows => (∀ row ∈ rows, (∀ edge ∈ row, EdgeReady heap edge) ∧ row.length ≤ bound) ∧ rows.length = groups.length) _
    (map_checked width clear (group top)
      (fun heap edges => Edges heap edges ∧ ClosedEdges edges ∧ edges.length ≤ bound ∧
        ∀ edge ∈ edges, edge.children.length ≤ width)
      (fun heap rows => (∀ edge ∈ rows, EdgeReady heap edge) ∧ rows.length ≤ bound)
      (fun _ _ effect _ ready => ⟨(fun edge member => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge (ready.1 edge member)), ready.2⟩)
      (fun _ _ effect _ ready => ⟨(fun edge member => edge_grows effect edge (ready.1 edge member)), ready.2⟩) groups
      (fun edges _ heap semantic costs ready => group_checked width bound clear top edges heap semantic costs ready.1 ready.2.1 ready.2.2.1 ready.2.2.2 enough)
      before semantic costs (fun edges member => ⟨resident edges member, closed edges member, rowLength edges member, children edges member⟩))
  intro rows middle effect valid
  apply node_checked width clear rows.flatten middle effect.semantic effect.costs
  · intro edge member
    obtain ⟨row, outer, inner⟩ := List.mem_flatten.mp member
    exact ((valid.1 row outer).1 edge inner).1
  · intro edge member
    obtain ⟨row, outer, inner⟩ := List.mem_flatten.mp member
    exact ((valid.1 row outer).1 edge inner).2
  · have small := flatten_length rows bound (fun row member => (valid.1 row member).2)
    rw [valid.2] at small
    exact Nat.le_trans small (Nat.le_trans (Nat.mul_le_mul_right bound groupLength) square)

/-- Initial payload mass supplies every constructor width in the full general body. -/
theorem body_checked (clear : Guard → Bool) (top : Guard) (input : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before input) (bound : Nat) (mass : InternedValueMass.value input ≤ bound) :
    Checked ((bound + 1) ^ 2) clear (body top input) before
      (fun after output => Available after output ∧ (input.free = [] → output.free = [])) := by
  have enough : bound ≤ (bound + 1) ^ 2 := by
    simpa only [Nat.pow_two] using Nat.le_trans (Nat.le_succ bound) (Nat.le_mul_self (bound + 1))
  have square : bound * bound ≤ (bound + 1) ^ 2 := by
    simpa only [Nat.pow_two] using Nat.mul_le_mul (Nat.le_succ bound) (Nat.le_succ bound)
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
        have rowsBound : edges.length ≤ bound := by
          have small := edges_length edges
          simp only [InternedValueMass.value] at mass
          omega
        have groupsBound : (MergedSourceGrouping.groups edges).length ≤ bound := by
          have flat : (MergedSourceGrouping.groups edges).flatten.length = edges.length := grouping.partition.length_eq
          have nonempty : ∀ group ∈ MergedSourceGrouping.groups edges, 1 ≤ group.length := by
            intro group member
            obtain ⟨first, rest, same, _⟩ := grouping.exact group member
            simp only [same, List.length_cons]
            omega
          have length : ∀ groups : List (List (EdgeValue Symbol Guard)),
              (∀ group ∈ groups, 1 ≤ group.length) → groups.length ≤ groups.flatten.length := by
            intro groups nonempty
            induction groups with
            | nil => simp
            | cons first rest ih =>
                have head := nonempty first List.mem_cons_self
                have tail := ih (fun group member => nonempty group (List.mem_cons_of_mem _ member))
                simp only [List.length_cons, List.flatten_cons, List.length_append]
                omega
          exact Nat.le_trans (length _ nonempty) (flat ▸ rowsBound)
        have groupBound (group : List (EdgeValue Symbol Guard)) (member : group ∈ MergedSourceGrouping.groups edges) :
            group.length ≤ bound := by
          obtain ⟨first, rest, _same, exactGroup⟩ := grouping.exact group member
          rw [exactGroup]
          exact Nat.le_trans (List.length_filter_le _ _) rowsBound
        have childBound (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) : edge.children.length ≤ (bound + 1) ^ 2 := by
          have row := InternedValueMass.edge_mem_lt edge edges member
          have children := values_length edge.children
          rw [InternedValueMass.edge_children] at row
          simp only [InternedValueMass.value] at mass
          exact Nat.le_trans (by omega : edge.children.length ≤ bound) enough
        have checked := root_checked ((bound + 1) ^ 2) bound clear top _ before semantic costs
          (fun group member edge inner => resident edge (original group member edge inner))
          (fun group member edge inner => rowsClosed edge (original group member edge inner))
          groupsBound groupBound (fun group member edge inner => childBound edge (original group member edge inner)) enough square
        exact checked.mono (fun _ _ ready => ⟨ready.1, fun _ => ready.2⟩)
      · simp only [body, closed, ite_false, Checked]
        exact ⟨available, id⟩
  | empty | reference | mu | union => exact ⟨available, id⟩

end MicroCFTA.SourceCurrentMemoMergeWorkWidths
