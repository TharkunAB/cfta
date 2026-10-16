import MicroCFTA.SourceCurrentAllocatedPartialMemoSound
import MicroCFTA.SourceCurrentAllocatedPartialFrames
import MicroCFTA.FlatMemoThunkRunningBefore
import MicroCFTA.MergedOrdinaryHeight

/-!
# Concrete active-owner order for current outer requests

The order uses immutable ordinary heights and separates node and edge
requests. Coherent resident key aliases have the same rank. Actual demand
cannot observe busy below all active owners. Publication adds only its
selected owner. Completion removes that owner and retains the others.

Returned-edge height bounds are a separate structural invariant. Semantic
EdgeLaw does not imply them. This module does not derive such bounds from
general constrained local reduction and does not prove outer completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialActiveOrder
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialFrames (Protocol)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

/-- A node ranks above the edges at its greatest ordinary child height. -/
def nodeRank (request : NodeRequest) : Nat := 2 * MergedOrdinaryHeight.height request.value + 1

/-- An edge ranks above each original ordinary child node. -/
def edgeRank (request : EdgeRequest) : Nat := 2 * (MergedOrdinaryHeight.edgeHeight request.value + 1)

/-- Both request families use one natural-valued order. -/
def rank : Sum NodeRequest EdgeRequest → Nat
  | .inl request => nodeRank request
  | .inr request => edgeRank request

/-- Strict rank descent is well founded without a finite future key inventory. -/
theorem wellFounded : WellFounded (fun child parent => rank child < rank parent) := (measure rank).wf

/-- The literal edge of an ordinary node is below its node request. -/
theorem edge_lt_node (inherited : EqValue) (entry) (edges : List Edge) (depth free)
    (edge : Edge) (member : edge ∈ edges) :
    edgeRank ⟨inherited, edge⟩ < nodeRank ⟨inherited, .node entry edges depth free⟩ := by
  have bounded := (MergedOrdinaryHeight.edgesHeight_le edges (MergedOrdinaryHeight.edgesHeight edges)).mp
    (Nat.le_refl _) edge member
  simp only [nodeRank, edgeRank, MergedOrdinaryHeight.height]
  omega

/-- Changing inherited payloads does not change proper-child rank descent. -/
theorem child_lt_edge (parentInherited childInherited : EqValue) (edge : Edge) (child : Node)
    (member : child ∈ edge.children) : nodeRank ⟨childInherited, child⟩ < edgeRank ⟨parentInherited, edge⟩ := by
  have bounded : MergedOrdinaryHeight.height child ≤ MergedOrdinaryHeight.edgeHeight edge := by
    cases edge with
    | mk entry children =>
      exact (MergedOrdinaryHeight.childrenHeight_le children (MergedOrdinaryHeight.childrenHeight children)).mp
        (Nat.le_refl _) child member
  simp only [nodeRank, edgeRank]
  omega

/-- Current coherent resident node keys identify the same rank. -/
theorem nodeRank_of_key (heap : InternedConstructorTemplates.State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap) (first second : NodeRequest)
    (firstAvailable : Available heap first.value) (secondAvailable : Available heap second.value)
    (same : first.key = second.key) : nodeRank first = nodeRank second := by
  have values := SourceEqualityPartialKeyTransport.available_reference_eq heap coherent _ _
    firstAvailable secondAvailable (congrArg Prod.snd same)
  simp only [nodeRank, values]

/-- Current coherent resident edge keys identify the same rank. -/
theorem edgeRank_of_key (heap : InternedConstructorTemplates.State Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap) (first second : EdgeRequest)
    (firstResident : EdgeResident heap first.value) (secondResident : EdgeResident heap second.value)
    (same : first.key = second.key) : edgeRank first = edgeRank second := by
  have values := edge_identity_unique heap coherent _ _ firstResident secondResident (congrArg Prod.snd same)
  simp only [edgeRank, values]

/-- A selected finish handle can be excluded while its ancestor bound is retained. -/
structure ActiveExcept (bound : Nat) (nodeSkip edgeSkip : Option Nat) (state : Caller width) : Prop where
  nodes : ∀ handle request, some handle ≠ nodeSkip →
    state.nodeResults.cells handle = some ⟨request, .evaluating⟩ → bound < nodeRank request
  edges : ∀ handle request, some handle ≠ edgeSkip →
    state.edgeResults.cells handle = some ⟨request, .evaluating⟩ → bound < edgeRank request

/-- Every evaluating owner in both families is strictly above this bound. -/
abbrev ActiveAbove (bound : Nat) (state : Caller width) := ActiveExcept bound none none state

/-- Empty outer tables admit every bound and retain all supplied lower warm state. -/
theorem initial_above (bound : Nat) (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    ActiveAbove bound (initial checked merge fourth) := by
  constructor <;> intros <;> contradiction

/-- Decreasing a bound retains all existing protected owners. -/
theorem ActiveExcept.mono {small bound : Nat} {nodeSkip edgeSkip : Option Nat} {state : Caller width}
    (active : ActiveExcept bound nodeSkip edgeSkip state) (below : small ≤ bound) :
    ActiveExcept small nodeSkip edgeSkip state :=
  ⟨fun handle request different found => Nat.lt_of_le_of_lt below (active.nodes handle request different found),
    fun handle request different found => Nat.lt_of_le_of_lt below (active.edges handle request different found)⟩

/-- Lower checked work retains the exact two outer result tables and their order. -/
theorem ActiveExcept.advance {bound : Nat} {nodeSkip edgeSkip : Option Nat} {before : Caller width}
    (active : ActiveExcept bound nodeSkip edgeSkip before) (checked : SourceEqualityNativeDemand.State width)
    (fourth : SourceCurrentEmptinessMemo.Memo) (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) :
    ActiveExcept bound nodeSkip edgeSkip (advance before checked fourth merge) := ⟨active.nodes, active.edges⟩

/-- Finishing one node restores the ancestor bound at every remaining active cell. -/
theorem finishNode_above {bound handle : Nat} {before : Caller width} (result : Node)
    (active : ActiveExcept bound (some handle) none before) : ActiveAbove bound (finishNode handle result before) := by
  constructor
  · intro other request _ found
    have different : other ≠ handle := by
      intro same
      subst other
      exact FlatMemoThunk.finish_not_running handle result before.nodeResults request found
    exact active.nodes other request (by simpa using different)
      (FlatMemoThunk.finish_running_before handle result before.nodeResults other request found)
  · exact active.edges

/-- Finishing one edge restores the ancestor bound in both result families. -/
theorem finishEdge_above {bound handle : Nat} {before : Caller width} (result : Edge)
    (active : ActiveExcept bound none (some handle) before) : ActiveAbove bound (finishEdge handle result before) := by
  constructor
  · exact active.nodes
  · intro other request _ found
    have different : other ≠ handle := by
      intro same
      subst other
      exact FlatMemoThunk.finish_not_running handle result before.edgeResults request found
    exact active.edges other request (by simpa using different)
      (FlatMemoThunk.finish_running_before handle result before.edgeResults other request found)

variable {width : Nat}

/-- Actual node publication can add an active phase only at its selected handle. -/
theorem beginNode_except (request : NodeRequest) (before : Caller width) {bound : Nat}
    (active : ActiveAbove bound before) :
    ActiveExcept bound (some (beginNode request before).1) none (beginNode request before).2.2 := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.nodeResults
  constructor
  · intro handle owner different found
    have old := FlatMemoThunk.demand_running_before_other published.1 handle published.2 owner
      (by simpa [beginNode, published] using different) found
    exact active.nodes handle owner (by simp)
      (FlatMemoThunk.lookup_running_before request.key request before.nodeResults handle owner old)
  · exact active.edges

/-- Actual edge publication protects the unchanged node family and every other edge owner. -/
theorem beginEdge_except (request : EdgeRequest) (before : Caller width) {bound : Nat}
    (active : ActiveAbove bound before) :
    ActiveExcept bound none (some (beginEdge request before).1) (beginEdge request before).2.2 := by
  let published := FlatMemoThunk.lookupOrInsert request.key request before.edgeResults
  constructor
  · exact active.nodes
  · intro handle owner different found
    have old := FlatMemoThunk.demand_running_before_other published.1 handle published.2 owner
      (by simpa [beginEdge, published] using different) found
    exact active.edges handle owner (by simp)
      (FlatMemoThunk.lookup_running_before request.key request before.edgeResults handle owner old)

/-- A real stored node owner has the candidate rank in the current coherent heap. -/
theorem node_owner_rank (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {request owner : NodeRequest}
    {before running : Caller width} {handle : Nat}
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .evaluate owner, running)) : nodeRank owner = nodeRank request := by
  obtain ⟨_, _, good, key⟩ := SourceCurrentAllocatedPartialMemoSound.beginNode_evaluate_sound
    formulas solver request before sound inherited available handle owner running started
  have parts := beginNode_components request before
  rw [started] at parts
  dsimp only at parts
  exact nodeRank_of_key _ coherent owner request (parts.1 ▸ good.input) available key

/-- A real stored edge owner has the candidate rank in the current coherent heap. -/
theorem edge_owner_rank (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {request owner : EdgeRequest}
    {before running : Caller width} {handle : Nat}
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (started : beginEdge request before = (handle, .evaluate owner, running)) : edgeRank owner = edgeRank request := by
  obtain ⟨_, _, good, key⟩ := SourceCurrentAllocatedPartialMemoSound.beginEdge_evaluate_sound
    formulas solver request before sound inherited resident handle owner running started
  have parts := beginEdge_components request before
  rw [started] at parts
  dsimp only at parts
  exact edgeRank_of_key _ coherent owner request (parts.1 ▸ good.input) resident key

/-- A resident node below all active owners observes only a ready result or a real start. -/
theorem node_begin_safe (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (request : NodeRequest) (before : Caller width)
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (available : Available before.checked.native.machine.heap request.value)
    (active : ActiveAbove (nodeRank request) before) :
    (∃ value, (beginNode request before).2.1 = .ready value) ∨
      ∃ owner, (beginNode request before).2.1 = .evaluate owner := by
  cases published : before.nodeResults.table request.key with
  | none =>
      exact Or.inr ⟨request, by simp [beginNode, FlatMemoThunk.lookupOrInsert, published, FlatMemoThunk.demand, put]⟩
  | some handle =>
      obtain ⟨⟨owner, phase⟩, present, linked⟩ := sound.valid.nodes.linked request.key handle published
      cases phase with
      | suspended => exact Or.inr ⟨owner, by simp only [beginNode, FlatMemoThunk.lookup_hit _ _ _ _ published,
          FlatMemoThunk.demand, present]⟩
      | returned value => exact Or.inl ⟨value, by simp only [beginNode, FlatMemoThunk.lookup_hit _ _ _ _ published,
          FlatMemoThunk.demand, present]⟩
      | evaluating =>
          have above := active.nodes handle owner (by simp) present
          have same := nodeRank_of_key _ coherent owner request
            (sound.nodes handle _ present).input available linked.2
          rw [same] at above
          exact False.elim ((Nat.lt_irrefl _) above)

/-- The separate resident edge family also excludes busy and absent demand below its owners. -/
theorem edge_begin_safe (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (request : EdgeRequest) (before : Caller width)
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (active : ActiveAbove (edgeRank request) before) :
    (∃ value, (beginEdge request before).2.1 = .ready value) ∨
      ∃ owner, (beginEdge request before).2.1 = .evaluate owner := by
  cases published : before.edgeResults.table request.key with
  | none =>
      exact Or.inr ⟨request, by simp [beginEdge, FlatMemoThunk.lookupOrInsert, published, FlatMemoThunk.demand, put]⟩
  | some handle =>
      obtain ⟨⟨owner, phase⟩, present, linked⟩ := sound.valid.edges.linked request.key handle published
      cases phase with
      | suspended => exact Or.inr ⟨owner, by simp only [beginEdge, FlatMemoThunk.lookup_hit _ _ _ _ published,
          FlatMemoThunk.demand, present]⟩
      | returned value => exact Or.inl ⟨value, by simp only [beginEdge, FlatMemoThunk.lookup_hit _ _ _ _ published,
          FlatMemoThunk.demand, present]⟩
      | evaluating =>
          have above := active.edges handle owner (by simp) present
          have same := edgeRank_of_key _ coherent owner request
            (sound.edges handle _ present).input resident linked.2
          rw [same] at above
          exact False.elim ((Nat.lt_irrefl _) above)

/-- An actual node start admits each strictly smaller recursive request bound. -/
theorem node_push (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {request owner : NodeRequest}
    {before running : Caller width} {handle lower : Nat}
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (active : ActiveAbove (nodeRank request) before) (smaller : lower < nodeRank request)
    (started : beginNode request before = (handle, .evaluate owner, running)) : ActiveAbove lower running := by
  have rest := beginNode_except request before active
  rw [started] at rest
  dsimp only at rest
  have cell := (SourceCurrentAllocatedPartialFrames.beginNode_owner request before handle owner running
    (Protocol.of_valid sound.valid) started).1
  have same := node_owner_rank formulas solver sound coherent inherited available started
  constructor
  · intro other original _ found
    by_cases equal : other = handle
    · subst other
      have owners := congrArg FlatMemoThunk.Cell.request (Option.some.inj (cell.symm.trans found))
      change owner = original at owners
      rw [← owners, same]
      exact smaller
    · exact Nat.lt_trans smaller (rest.nodes other original (by simpa using equal) found)
  · intro other original different found
    exact Nat.lt_trans smaller (rest.edges other original different found)

/-- An actual edge start admits each strictly smaller recursive request bound. -/
theorem edge_push (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {request owner : EdgeRequest}
    {before running : Caller width} {handle lower : Nat}
    (sound : SourceCurrentAllocatedPartialMemoSound.Sound formulas solver before)
    (coherent : InternedRecordCoherence.Coherent before.checked.native.machine.heap)
    (inherited : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value)
    (active : ActiveAbove (edgeRank request) before) (smaller : lower < edgeRank request)
    (started : beginEdge request before = (handle, .evaluate owner, running)) : ActiveAbove lower running := by
  have rest := beginEdge_except request before active
  rw [started] at rest
  dsimp only at rest
  have cell := (SourceCurrentAllocatedPartialFrames.beginEdge_owner request before handle owner running
    (Protocol.of_valid sound.valid) started).1
  have same := edge_owner_rank formulas solver sound coherent inherited resident started
  constructor
  · intro other original different found
    exact Nat.lt_trans smaller (rest.nodes other original different found)
  · intro other original _ found
    by_cases equal : other = handle
    · subst other
      have owners := congrArg FlatMemoThunk.Cell.request (Option.some.inj (cell.symm.trans found))
      change owner = original at owners
      rw [← owners, same]
      exact smaller
    · exact Nat.lt_trans smaller (rest.edges other original (by simpa using equal) found)

/-- A structural returned-edge bound is separate from its independent language law. -/
def ReturnedBounds (state : Caller width) : Prop :=
  ∀ handle owner result, state.edgeResults.cells handle = some ⟨owner, .returned result⟩ →
    MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgeHeight owner.value

/-- Empty outer tables derive the structural result invariant without a returned-edge oracle. -/
theorem initial_bounds (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo) :
    ReturnedBounds (initial checked merge fourth) := by
  intro handle owner result found
  cases found

/-- Lower checked work retains every immutable structural returned-edge bound. -/
theorem ReturnedBounds.advance {before : Caller width} (bounds : ReturnedBounds before)
    (checked : SourceEqualityNativeDemand.State width) (fourth : SourceCurrentEmptinessMemo.Memo)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) : ReturnedBounds (advance before checked fourth merge) := bounds

/-- Exact original or erased children derive the required returned-edge height bound. -/
theorem original_or_erased_bound (original result : Edge)
    (shape : result.children = original.children ∨ result.children = original.children.map (fun _ => .empty)) :
    MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgeHeight original := by
  have childrenBound : MergedOrdinaryHeight.childrenHeight result.children ≤
      MergedOrdinaryHeight.childrenHeight original.children := by
    apply (MergedOrdinaryHeight.childrenHeight_le _ _).mpr
    intro child member
    rcases shape with same | erased
    · rw [same] at member
      exact (MergedOrdinaryHeight.childrenHeight_le _ _).mp (Nat.le_refl _) child member
    · rw [erased] at member
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp member
      exact Nat.zero_le _
  cases result
  cases original
  exact childrenBound

/-- Every child of a bounded returned edge lies below its original edge request. -/
theorem returned_child_lt {before : Caller width} (bounds : ReturnedBounds before)
    {handle : Nat} {owner : EdgeRequest} {result : Edge}
    (returned : before.edgeResults.cells handle = some ⟨owner, .returned result⟩)
    (inherited : EqValue) {child : Node} (member : child ∈ result.children) :
    nodeRank ⟨inherited, child⟩ < edgeRank owner := by
  have below := child_lt_edge owner.inherited inherited result child member
  have bounded := bounds handle owner result returned
  simp only [edgeRank] at below ⊢
  omega

/-- A literal finish stores a separately proved structural bound at its actual owner. -/
theorem ReturnedBounds.finishEdge {before : Caller width} (bounds : ReturnedBounds before)
    {handle : Nat} {owner : EdgeRequest} (result : Edge)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (bounded : MergedOrdinaryHeight.edgeHeight result ≤ MergedOrdinaryHeight.edgeHeight owner.value) :
    ReturnedBounds (finishEdge handle result before) := by
  intro other original output found
  by_cases same : other = handle
  · subst other
    have installed := finishEdge_returned handle owner result before running
    have equal := Option.some.inj (installed.symm.trans found)
    cases equal
    exact bounded
  · exact bounds other original output (by
      change (FlatMemoThunk.finish handle result before.edgeResults).cells other = _ at found
      simpa only [FlatMemoThunk.finish, running, FlatMemoThunk.setStatus,
        put, ite_eq_right same] using found)

end MicroCFTA.SourceCurrentAllocatedPartialActiveOrder
