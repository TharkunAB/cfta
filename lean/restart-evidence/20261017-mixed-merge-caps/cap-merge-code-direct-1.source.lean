import MicroCFTA.SourceCurrentConstrainedCap
import MicroCFTA.SourceCurrentMemoMergeQueryMemos

/-!
# Local finite caps through the current memo-aware Merge graph

The certificate preserves each input cap at the same depth. Small rows
retain their original guards. Large rows use the supplied valid Top guard.
Recursive request laws are local obligations. This module does not assume
or prove completed recursive execution.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapMemoMergeCode
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect ValueReady EdgeReady)
open SourceEqualityAnnotationLanguage
open SourceCurrentConstrainedCap (Cap)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- Each result preserves every finite cap of its own captured original. -/
def Certificate (valid : Guard → Prop) (input output : Value Symbol Guard) : Prop :=
  ∀ depth, SourceCurrentConstrainedCap.Cap valid depth input → SourceCurrentConstrainedCap.Cap valid depth output

/-- Requests retain their original physical contract and local annotation law. -/
def Contract (valid : Guard → Prop) (input : Value Symbol Guard) (before : State Symbol Guard)
    (output : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SourceCurrentMemoMergeEffects.Contract input before output after ∧ Certificate valid input output

/-- Instructions use the stronger contract at their actual recursive calls. -/
abbrev Certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (code : Code Symbol Guard Output)
    (before : State Symbol Guard) (post : State Symbol Guard → Output → Prop) : Prop :=
  SourceCurrentMemoMergeEffects.Certified (Contract valid) clear code before post

/-- A stronger recursive contract retains each physical continuation. -/
theorem lift_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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

/-- A returned value is available, closed, and bounded at the supplied depth. -/
abbrev ValuePost (valid : Guard → Prop) (capDepth : Nat) (heap : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ValueReady heap value ∧ Cap valid capDepth value
/-- A returned row is resident, closed, and bounded at its parent depth. -/
abbrev EdgePost (valid : Guard → Prop) (capDepth : Nat) (heap : State Symbol Guard) (edge : EdgeValue Symbol Guard) : Prop :=
  EdgeReady heap edge ∧ SourceCurrentConstrainedCap.Edge valid capDepth edge

private theorem value_grows {valid : Guard → Prop} {capDepth : Nat} {before after : State Symbol Guard}
    (effect : Effect before after) (value : Value Symbol Guard) (ready : ValuePost valid capDepth before value) :
    ValuePost valid capDepth after value := ⟨SourceCurrentMemoMergeEffects.value_grows effect value ready.1, ready.2⟩
private theorem edge_grows {valid : Guard → Prop} {capDepth : Nat} {before after : State Symbol Guard}
    (effect : Effect before after) (edge : EdgeValue Symbol Guard) (ready : EdgePost valid capDepth before edge) :
    EdgePost valid capDepth after edge := ⟨SourceCurrentMemoMergeEffects.edge_grows effect edge ready.1, ready.2⟩

private theorem edge_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (capDepth : Nat) (clear : Guard → Bool) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (closed : ClosedValues values) (annotation : capDepth = 0 → valid guard)
    (annotated : ∀ value ∈ values, Cap valid (capDepth - 1) value) :
    Certified valid clear (.work (makeEdge symbol guard values)) before (EdgePost valid capDepth) := by
  have checked := SourceCurrentMemoMergeEffects.edge_certified clear symbol guard values before semantic costs available closed
  exact ⟨checked.1, checked.2, SourceCurrentConstrainedCap.makeEdge valid capDepth symbol guard values before
    semantic.ready.semantic.1.normal.facts.coherent semantic.ready.semantic.1.normal.facts.cached available annotation annotated⟩

private theorem node_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (capDepth : Nat) (clear : Guard → Bool) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before edges) (closed : ClosedEdges edges)
    (annotated : ∀ edge ∈ edges, SourceCurrentConstrainedCap.Edge valid capDepth edge) :
    Certified valid clear (.work (makeNode edges)) before (ValuePost valid capDepth) := by
  have checked := SourceCurrentMemoMergeEffects.node_certified clear edges before semantic costs resident closed
  exact ⟨checked.1, checked.2, SourceCurrentConstrainedCap.makeNode valid capDepth edges before
    semantic.ready.semantic.1.normal.facts.coherent semantic.ready.semantic.1.normal.facts.linked resident annotated⟩

private theorem edge_guard {valid : Guard → Prop} {capDepth : Nat} {edge : EdgeValue Symbol Guard}
    (bounded : SourceCurrentConstrainedCap.Edge valid capDepth edge) (zero : capDepth = 0) :
    valid edge.entry.key.constraint := by
  subst capDepth
  exact bounded.1

private theorem edge_child {valid : Guard → Prop} {capDepth : Nat} {edge : EdgeValue Symbol Guard}
    (bounded : SourceCurrentConstrainedCap.Edge valid capDepth edge) (value : Value Symbol Guard)
    (member : value ∈ edge.children) : Cap valid (capDepth - 1) value := by
  cases capDepth with
  | zero => exact .plain 0 (bounded.2 value member)
  | succ depth => exact bounded value member

/-- Literal ordinary union copies bounded rows from its original operands. -/
theorem ordinary_union [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent state) (linked : InternedNestedFacts.Linked state)
    (available : Values state values) (bounded : ∀ value ∈ values, Cap valid capDepth value) :
    Cap valid capDepth (run (MergedOrdinaryHeight.ordinaryUnion values) state).1 := by
  apply SourceCurrentConstrainedCap.makeNode valid capDepth _ state coherent linked
  · intro edge member
    obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
    exact InternedEdgeResidency.resident_edges state linked value (available value present).resident edge included
  · intro edge member
    obtain ⟨value, present, included⟩ := List.mem_flatMap.mp member
    exact SourceCurrentConstrainedCap.node_edge (bounded value present) edge included

private theorem request_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (capDepth : Nat) (clear : Guard → Bool) (input : Value Symbol Guard) (before : State Symbol Guard)
    (ready : ValuePost valid capDepth before input) : Certified valid clear (.request input) before (ValuePost valid capDepth) :=
  ⟨ready.1.1, fun _ _ _ returned => ⟨⟨returned.1.1, returned.1.2 ready.1.2⟩, returned.2 capDepth ready.2⟩⟩

/-- Retained columns preserve caps through boundary and ordinary union branches. -/
theorem retained_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (capDepth : Nat) (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before inputs) (closed : ClosedValues inputs)
    (annotated : ∀ value ∈ inputs, Cap valid capDepth value) :
    Certified valid clear (retainedColumn inputs) before (ValuePost valid capDepth) := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values)
      (closed : ClosedValues values) (annotated : ∀ value ∈ values, Cap valid capDepth value) :
      Certified valid clear
        (if values.any MergedOrdinaryHeight.recursiveBoundary then .work (makeUnion values)
          else .bind (.work (MergedOrdinaryHeight.ordinaryUnion values)) Code.request) before (ValuePost valid capDepth) := by
    by_cases boundary : values.any MergedOrdinaryHeight.recursiveBoundary = true
    · simp only [boundary, ite_true]
      have checked := SourceMergedCache.union values before semantic available closed
      exact ⟨⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
        (InternedShallowHeap.makeUnion_noNewMu values before)⟩, checked.2,
        SourceCurrentConstrainedCap.makeUnion valid capDepth values before semantic.ready.semantic.1.normal.facts available annotated⟩
    · simp only [boundary, Bool.false_eq_true, ite_false]
      have checked := SourceMergedCache.ordinary_exact (fun _ _ => true) (fun _ _ => False)
        values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      apply SourceCurrentMemoMergeEffects.bind_certified (Contract valid) clear _ _ before (ValuePost valid capDepth) _
      · exact ⟨⟨checked.1.1, checked.1.2, InternedFreshOrdinaryCostHeap.preserve before _ costs
          (InternedShallowHeap.makeNode_noNewMu _ before)⟩, ⟨checked.2.1, checked.2.2.1⟩,
          ordinary_union valid capDepth values before semantic.ready.semantic.1.normal.facts.coherent
            semantic.ready.semantic.1.normal.facts.linked available annotated⟩
      · exact fun value middle _ ready => request_certified valid capDepth clear value middle ready
  cases inputs with
  | nil => exact branches [] available closed annotated
  | cons first rest =>
      cases rest with
      | nil => exact ⟨⟨available first List.mem_cons_self, closed first List.mem_cons_self⟩, annotated first List.mem_cons_self⟩
      | cons second rest => exact branches _ available closed annotated

private theorem column_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (capDepth : Nat) (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (_costs : CostHeap before)
    (available : Values before inputs) (closed : ClosedValues inputs)
    (annotated : ∀ value ∈ inputs, Cap valid capDepth value) :
    Certified valid clear (column inputs) before (ValuePost valid capDepth) := by
  apply SourceCurrentMemoMergeEffects.bind_certified (Contract valid) clear _ _ before
    (fun heap values => Values heap values ∧ ClosedValues values ∧ ∀ value ∈ values, Cap valid capDepth value) _
  · refine ⟨available, closed, ?_⟩
    intro fuel values after done _
    have checked := SourceMergedSelectionLanguage.select_exact clear fuel (fun _ _ => true) (fun _ _ => False)
      (fun _ _ _ => rfl) inputs before semantic available closed values after done
    exact ⟨checked.2.1, checked.2.2.1, fun value member => annotated value (checked.2.2.2.1 value member)⟩
  · intro values middle effect ready
    exact retained_certified valid capDepth clear values middle effect.semantic effect.costs ready.1 ready.2.1 ready.2.2

/-- Small rows use smaller child caps and retain their exact original guard. -/
theorem small_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (capDepth : Nat) (clear : Guard → Bool) (edge : EdgeValue Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (ready : EdgePost valid capDepth before edge) :
    Certified valid clear (small edge) before (EdgePost valid capDepth) := by
  have available := semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge ready.1.1
  apply SourceCurrentMemoMergeEffects.bind_certified (Contract valid) clear _ _ before
    (fun heap values => ∀ value ∈ values, ValuePost valid (capDepth - 1) heap value) _
  · exact SourceCurrentMemoMergeEffects.map_certified (Contract valid) clear Code.request (ValuePost valid (capDepth - 1)) (ValuePost valid (capDepth - 1))
      (fun _ _ effect value ready => value_grows effect value ready)
      (fun _ _ effect value ready => value_grows effect value ready) edge.children
      (fun value _ heap _ _ ready => request_certified valid (capDepth - 1) clear value heap ready) before semantic costs
      (fun value member => ⟨⟨available value member, ready.1.2 value member⟩, edge_child ready.2 value member⟩)
  · intro values middle effect readyValues
    exact edge_certified valid capDepth clear _ _ values middle effect.semantic effect.costs
      (fun value member => (readyValues value member).1.1) (fun value member => (readyValues value member).1.2)
      (edge_guard ready.2) (fun value member => (readyValues value member).2)

/-- Large rows process literal columns before they construct the valid Top row. -/
theorem large_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (capDepth : Nat) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : Edges before (first :: rest)) (closed : ClosedEdges (first :: rest))
    (annotated : ∀ edge ∈ first :: rest, SourceCurrentConstrainedCap.Edge valid capDepth edge) :
    Certified valid clear (large top first rest) before (EdgePost valid capDepth) := by
  let columns := MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length
  have original (column : List (Value Symbol Guard)) (member : column ∈ columns) (value : Value Symbol Guard)
      (included : value ∈ column) : ∃ edge ∈ first :: rest, value ∈ edge.children := by
    obtain ⟨row, present, inner⟩ := MergedPhysicalGroupEdges.columns_member _ _ column member value included
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact ⟨edge, member, inner⟩
  apply SourceCurrentMemoMergeEffects.bind_certified (Contract valid) clear _ _ before
    (fun heap values => ∀ value ∈ values, ValuePost valid (capDepth - 1) heap value) _
  · apply SourceCurrentMemoMergeEffects.map_certified (Contract valid) clear column
      (fun heap values => Values heap values ∧ ClosedValues values ∧ ∀ value ∈ values, Cap valid (capDepth - 1) value) (ValuePost valid (capDepth - 1))
      (fun _ _ effect _ ready => ⟨fun value member => effect.keeps.available _ (ready.1 value member), ready.2⟩)
      (fun _ _ effect value ready => value_grows effect value ready) columns
      (fun values _ heap semantic costs ready => column_certified valid (capDepth - 1) clear values heap semantic costs ready.1 ready.2.1 ready.2.2)
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
      exact edge_child (annotated edge outer) value inner
  · intro values middle effect ready
    exact edge_certified valid capDepth clear _ _ values middle effect.semantic effect.costs
      (fun value member => (ready value member).1.1) (fun value member => (ready value member).1.2)
      (fun _ => topValid) (fun value member => (ready value member).2)

/-- The exact four-row threshold retains the parent cap in both branches. -/
theorem group_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (capDepth : Nat) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (resident : Edges before edges)
    (closed : ClosedEdges edges) (annotated : ∀ edge ∈ edges, SourceCurrentConstrainedCap.Edge valid capDepth edge) :
    Certified valid clear (group top edges) before (fun heap rows => ∀ edge ∈ rows, EdgePost valid capDepth heap edge) := by
  unfold group
  split
  · exact SourceCurrentMemoMergeEffects.map_certified (Contract valid) clear small (EdgePost valid capDepth) (EdgePost valid capDepth)
      (fun _ _ effect edge ready => edge_grows effect edge ready) (fun _ _ effect edge ready => edge_grows effect edge ready)
      edges (fun edge _ heap semantic costs ready => small_certified valid capDepth clear edge heap semantic costs ready)
      before semantic costs (fun edge member => ⟨⟨resident edge member, closed edge member⟩, annotated edge member⟩)
  · cases edges with
    | nil => simp_all
    | cons first rest =>
        apply SourceCurrentMemoMergeEffects.bind_certified (Contract valid) clear _ _ before (EdgePost valid capDepth) _
          (large_certified valid capDepth clear top topValid first rest before semantic costs resident closed annotated)
        intro edge _ _ ready value member
        exact (List.mem_singleton.mp member) ▸ ready

/-- Ordered groups finish before the actual bounded root constructor runs. -/
theorem root_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (capDepth : Nat) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (groups : List (List (EdgeValue Symbol Guard))) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (resident : ∀ group ∈ groups, Edges before group) (closed : ∀ group ∈ groups, ClosedEdges group)
    (annotated : ∀ group ∈ groups, ∀ edge ∈ group, SourceCurrentConstrainedCap.Edge valid capDepth edge) :
    Certified valid clear (root top groups) before (ValuePost valid capDepth) := by
  apply SourceCurrentMemoMergeEffects.bind_certified (Contract valid) clear _ _ before
    (fun heap rows => ∀ row ∈ rows, ∀ edge ∈ row, EdgePost valid capDepth heap edge) _
  · apply SourceCurrentMemoMergeEffects.map_certified (Contract valid) clear (group top)
      (fun heap edges => Edges heap edges ∧ ClosedEdges edges ∧ ∀ edge ∈ edges, SourceCurrentConstrainedCap.Edge valid capDepth edge)
      (fun heap rows => ∀ edge ∈ rows, EdgePost valid capDepth heap edge)
      (fun _ _ effect _ ready => ⟨fun edge member => InternedEdgeResidency.edge_grows _ _ effect.keeps.growth edge (ready.1 edge member), ready.2⟩)
      (fun _ _ effect _ ready edge member => edge_grows effect edge (ready edge member)) groups
      (fun edges _ heap semantic costs ready => group_certified valid capDepth clear top topValid edges heap semantic costs ready.1 ready.2.1 ready.2.2)
      before semantic costs (fun edges member => ⟨resident edges member, closed edges member, annotated edges member⟩)
  · intro rows middle effect ready
    exact node_certified valid capDepth clear rows.flatten middle effect.semantic effect.costs
      (fun edge member => by obtain ⟨row, outer, inner⟩ := List.mem_flatten.mp member; exact (ready row outer edge inner).1.1)
      (fun edge member => by obtain ⟨row, outer, inner⟩ := List.mem_flatten.mp member; exact (ready row outer edge inner).1.2)
      (fun edge member => by obtain ⟨row, outer, inner⟩ := List.mem_flatten.mp member; exact (ready row outer edge inner).2)

/-- Each actual body branch preserves a supplied initial finite cap. -/
theorem body_depth_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (capDepth : Nat) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input)
    (annotated : Cap valid capDepth input) :
    Certified valid clear (body top input) before (fun _ output => Cap valid capDepth output) := by
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
        exact (root_certified valid capDepth clear top topValid _ before semantic costs
          (fun group member edge inner => resident edge (original group member edge inner))
          (fun group member edge inner => rowsClosed edge (original group member edge inner))
          (fun group member edge inner => SourceCurrentConstrainedCap.node_edge annotated edge (original group member edge inner))).mono
          (fun _ _ ready => ready.2)
      · simpa only [body, closed, ite_false, Certified, SourceCurrentMemoMergeEffects.Certified] using annotated
  | empty | reference | mu | union => exact annotated

/-- The least input cap supplies every conditional output cap. -/
theorem body_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (top : Guard) (topValid : valid top)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input) :
    Certified valid clear (body top input) before (fun _ output => Certificate valid input output) := by
  classical
  by_cases bounded : ∃ depth, Cap valid depth input
  · have least := Nat.find_spec bounded
    exact (body_depth_certified valid (Nat.find bounded) clear top topValid input before semantic costs available least).mono
      (fun _ output cap depth original => cap.mono (Nat.find_min' bounded original))
  · exact (lift_certified valid clear _ before _
      (SourceCurrentMemoMergeEffects.body_certified clear top input before semantic costs available)).mono
      (fun _ _ _ depth original => False.elim (bounded ⟨depth, original⟩))

end MicroCFTA.SourceCurrentConstrainedCapMemoMergeCode
