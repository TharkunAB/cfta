import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentAllocatedPartialFrames
import MicroCFTA.SourceCurrentAllocatedMuRebuild

/-!
# Current result-cell induction steps

Each start derives the stored owner's input facts. Each finish uses the
smaller actual body receipt and its protected evaluating cell. The mutual
caller proof must derive that body receipt. No completion law is assumed.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialCallSteps
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialMemoSound
open SourceCurrentAllocatedPartialInvariant
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
variable {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] in
/-- An unchanged node satisfies both parts of the inherited-conditioned law. -/
theorem node_refl (request : NodeRequest) : NodeLaw formulas solver request request.value :=
  fun _ _ => ⟨id, fun _ => Iff.rfl⟩

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- A node start derives its actual owner and retains every other entry fact. -/
theorem node_start {inventory : Inventory} {request original : NodeRequest}
    {before running : Caller width} {memos : Memos} {handle : Nat}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .evaluate original, running)) :
    Context formulas solver inventory running memos ∧
      NodeGood formulas solver running.checked ⟨original, .evaluating⟩ ∧
      original.key = request.key ∧ running.nodeResults.cells handle = some ⟨original, .evaluating⟩ := by
  obtain ⟨sound, cell, owner, key⟩ := beginNode_evaluate_sound formulas solver request before initial.sound
    inherited available handle original running started
  have components := beginNode_components request before
  rw [started] at components
  dsimp only at components
  obtain ⟨checked, merge, fourth, _⟩ := components
  exact ⟨initial.rebase checked merge fourth sound, owner, key, cell⟩

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- An edge start derives its own owner in the independent result family. -/
theorem edge_start {inventory : Inventory} {request original : EdgeRequest}
    {before running : Caller width} {memos : Memos} {handle : Nat}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (started : beginEdge request before = (handle, .evaluate original, running)) :
    Context formulas solver inventory running memos ∧
      EdgeGood formulas solver running.checked ⟨original, .evaluating⟩ ∧
      original.key = request.key ∧ running.edgeResults.cells handle = some ⟨original, .evaluating⟩ := by
  obtain ⟨sound, cell, owner, key⟩ := beginEdge_evaluate_sound formulas solver request before initial.sound
    inherited resident handle original running started
  have components := beginEdge_components request before
  rw [started] at components
  dsimp only at components
  obtain ⟨checked, merge, fourth, _⟩ := components
  exact ⟨initial.rebase checked merge fourth sound, owner, key, cell⟩

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- A completed node hit keeps the whole caller and derives its candidate law. -/
theorem node_hit {inventory : Inventory} {request : NodeRequest} {before after : Caller width}
    {memos : Memos} {handle : Nat} {result : Value Symbol Guard}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .ready result, after)) :
    Post formulas solver inventory before after memos ∧
      Available after.checked.native.machine.heap result ∧ NodeLaw formulas solver request result := by
  obtain ⟨same, resident, law⟩ := beginNode_ready_sound formulas solver request before initial.sound
    initial.ready.good.operations.constraints initial.ready.semantic.ready.semantic.1.normal.facts.coherent
    inherited available handle result after started
  subst after
  exact ⟨Post.refl initial, resident, law⟩

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- A completed edge hit uses its stored owner without evaluating a body. -/
theorem edge_hit {inventory : Inventory} {request : EdgeRequest} {before after : Caller width}
    {memos : Memos} {handle : Nat} {result : EdgeValue Symbol Guard}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (started : beginEdge request before = (handle, .ready result, after)) :
    Post formulas solver inventory before after memos ∧
      Resident after.checked.native.machine.heap result ∧ EdgeLaw formulas solver request result := by
  obtain ⟨same, available, law⟩ := beginEdge_ready_sound formulas solver request before initial.sound
    initial.ready.good.operations.constraints initial.ready.semantic.ready.semantic.1.normal.facts.coherent
    inherited resident handle result after started
  subst after
  exact ⟨Post.refl initial, available, law⟩

/-- A smaller actual node body supplies the result installed at its protected owner. -/
theorem node_finish {inventory next : Inventory} {budget : Nat} {request original : NodeRequest}
    {before running middle : Caller width} {memos final : Memos} {handle : Nat} {result : Value Symbol Guard}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value)
    (started : beginNode request before = (handle, .evaluate original, running))
    (body : NodeBody budget original running result middle)
    (post : Post formulas solver next running middle final)
    (resident : Available middle.checked.native.machine.heap result)
    (bodyLaw : NodeLaw formulas solver original result) :
    Post formulas solver next before (finishNode handle result middle) final ∧
      Available (finishNode handle result middle).checked.native.machine.heap result ∧
      NodeLaw formulas solver request result := by
  obtain ⟨runningContext, owner, key, cell⟩ := node_start formulas solver initial inherited available started
  have frame := SourceCurrentAllocatedPartialFrames.node_body body
    (SourceCurrentAllocatedPartialFrames.Protocol.of_valid runningContext.sound.valid)
  have current := frame.node_running handle original cell
  have completed := finishNode_sound formulas solver handle original result middle post.context.sound current resident bodyLaw
  have components := beginNode_components request before
  rw [started] at components
  dsimp only at components
  obtain ⟨checked, merge, fourth, _⟩ := components
  have law := NodeLaw.of_key formulas solver running.checked.operations.constraints running.checked.native.machine.heap
    original request result runningContext.ready.good.operations.constraints
    runningContext.ready.semantic.ready.semantic.1.normal.facts.coherent owner.inherited
    (by simpa only [checked] using inherited)
    owner.input (by simpa only [checked] using available) key bodyLaw
  refine ⟨⟨⟨post.context.ready, post.context.admitted, completed, post.context.stored, post.context.covered,
      post.context.correct, post.context.globals, post.context.probes⟩, ?_, ?_, ?_⟩, resident, law⟩
  · simpa only [finishNode, checked] using post.effects
  · simpa only [finishNode, merge] using post.retained
  · simpa only [finishNode, fourth] using post.fourthRetained

/-- A smaller actual edge body supplies the independent edge finish and candidate law. -/
theorem edge_finish {inventory next : Inventory} {budget : Nat} {request original : EdgeRequest}
    {before running middle : Caller width} {memos final : Memos} {handle : Nat} {result : EdgeValue Symbol Guard}
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Resident before.checked.native.machine.heap request.value)
    (started : beginEdge request before = (handle, .evaluate original, running))
    (body : EdgeBody budget original running result middle)
    (post : Post formulas solver next running middle final)
    (available : Resident middle.checked.native.machine.heap result)
    (bodyLaw : EdgeLaw formulas solver original result) :
    Post formulas solver next before (finishEdge handle result middle) final ∧
      Resident (finishEdge handle result middle).checked.native.machine.heap result ∧
      EdgeLaw formulas solver request result := by
  obtain ⟨runningContext, owner, key, cell⟩ := edge_start formulas solver initial inherited resident started
  have frame := SourceCurrentAllocatedPartialFrames.edge_body body
    (SourceCurrentAllocatedPartialFrames.Protocol.of_valid runningContext.sound.valid)
  have current := frame.edge_running handle original cell
  have completed := finishEdge_sound formulas solver handle original result middle post.context.sound current available bodyLaw
  have components := beginEdge_components request before
  rw [started] at components
  dsimp only at components
  obtain ⟨checked, merge, fourth, _⟩ := components
  have law := EdgeLaw.of_key formulas solver running.checked.operations.constraints running.checked.native.machine.heap
    original request result runningContext.ready.good.operations.constraints
    runningContext.ready.semantic.ready.semantic.1.normal.facts.coherent owner.inherited
    (by simpa only [checked] using inherited) owner.input (by simpa only [checked] using resident) key bodyLaw
  refine ⟨⟨⟨post.context.ready, post.context.admitted, completed, post.context.stored, post.context.covered,
      post.context.correct, post.context.globals, post.context.probes⟩, ?_, ?_, ?_⟩, available, law⟩
  · simpa only [finishEdge, checked] using post.effects
  · simpa only [finishEdge, merge] using post.retained
  · simpa only [finishEdge, fourth] using post.fourthRetained

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- A resident binder rebuilds to its derived cleanup at the unchanged caller. -/
theorem node_binder {inventory : Inventory} {inherited : SourceEqualityConstraintAllocation.Value}
    {entry : Interned InternedBinderProtocol.NodeKey} {body depth ordinary result : Value Symbol Guard}
    {heap : InternedConstructorTemplates.State Symbol Guard} {before : Caller width} {memos : Memos}
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap (.mu entry body depth ordinary))
    (actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap =
      .done result heap) :
    Post formulas solver inventory before
      (advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩)
        before.fourth before.merge) memos ∧
      Available heap result ∧ NodeLaw formulas solver ⟨inherited, .mu entry body depth ordinary⟩ result := by
  obtain ⟨sameResult, sameHeap⟩ := SourceCurrentAllocatedMuRebuild.actual_rebuild before.checked initial.ready initial.probes
    entry body depth ordinary available result heap actual
  subst result
  subst heap
  have clean := SourceCurrentAllocatedMuRebuild.resident_rebuild before.checked initial.ready initial.probes
    entry body depth ordinary available
  have unchanged : advance before
      (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked
        ⟨before.checked.native.machine.heap, before.checked.operations⟩) before.fourth before.merge = before := by
    cases before
    rfl
  rw [unchanged]
  refine ⟨Post.refl initial, clean.2.1, ?_⟩
  intro ambient term
  have same := Iff.of_eq (congrFun (clean.2.2.2 (SourceEqualityPCSGuard.holds formulas solver) ambient) term)
  exact ⟨same.mp, fun _ => same⟩

end MicroCFTA.SourceCurrentAllocatedPartialCallSteps
