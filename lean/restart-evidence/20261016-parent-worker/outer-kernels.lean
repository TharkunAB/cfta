import MicroCFTA.SourceCurrentAllocatedPartialWorker

namespace MicroCFTA.CurrentOuterWorkerChecks
open Language InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "advanceHeap" => SourceCurrentAllocatedQueryMemo.advancePhysical
variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
  [DecidableEq Node] {width : Nat}

-- A concrete returned node cell skips all bounds and retains the entire caller state.
example (candidate original : NodeRequest) (before : Caller width) (handle : Nat) (result : Node)
    (published : before.nodeResults.table candidate.key = some handle)
    (returned : before.nodeResults.cells handle = some ⟨original, .returned result⟩) :
    nodeCall 0 0 0 0 0 0 0 0 0 0 0 candidate before = .done result before := by
  exact nodeCall_ready 0 0 0 0 0 0 0 0 0 0 0 candidate before before handle result
    (beginNode_ready candidate original before handle result published returned)

-- A concrete edge hit skips even the parent worker at zero bounds.
example (candidate original : EdgeRequest) (before : Caller width) (handle : Nat) (result : Edge)
    (published : before.edgeResults.table candidate.key = some handle)
    (returned : before.edgeResults.cells handle = some ⟨original, .returned result⟩) :
    edgeCall 0 0 0 0 0 0 0 0 0 0 0 candidate before = .done result before := by
  exact edgeCall_ready 0 0 0 0 0 0 0 0 0 0 0 candidate before before handle result
    (beginEdge_ready candidate original before handle result published returned)

-- A stored Empty owner wins over a later candidate and completes its selected cell at zero fuel.
example (candidate : NodeRequest) (inherited : EqValue) (before : Caller width) (handle : Nat)
    (published : before.nodeResults.table candidate.key = some handle)
    (suspended : before.nodeResults.cells handle = some ⟨⟨inherited, .empty⟩, .suspended⟩) :
    let running := {before with nodeResults := FlatMemoThunk.setStatus handle .evaluating before.nodeResults}
    nodeCall 0 0 0 0 0 0 0 0 0 0 0 candidate before = .done .empty (finishNode handle .empty running) ∧
      (finishNode handle .empty running).nodeResults.cells handle = some ⟨⟨inherited, .empty⟩, .returned .empty⟩ := by
  dsimp only
  have started := beginNode_suspended candidate ⟨inherited, .empty⟩ before handle published suspended
  have running := FlatMemoThunk.setStatus_cell handle (.evaluating : FlatMemoThunk.Status Node)
    before.nodeResults ⟨⟨inherited, .empty⟩, .suspended⟩ suspended
  exact ⟨nodeCall_body_done 0 0 0 0 0 0 0 0 0 0 0 candidate ⟨inherited, .empty⟩ before _ _ handle .empty started (by simp only [nodeBody]),
    finishNode_returned handle ⟨inherited, .empty⟩ .empty _ running⟩

-- Exhaustion after publication preserves the actual evaluating owner and never finishes it.
example (candidate : NodeRequest) (inherited : EqValue) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List Edge) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (before : Caller width) (handle : Nat)
    (published : before.nodeResults.table candidate.key = some handle)
    (suspended : before.nodeResults.cells handle = some ⟨⟨inherited, .node entry edges depth free⟩, .suspended⟩) :
    let running := {before with nodeResults := FlatMemoThunk.setStatus handle .evaluating before.nodeResults}
    nodeCall 0 0 0 0 0 0 0 0 0 0 0 candidate before = .failed (.exhausted .nodeBody) running ∧
      running.nodeResults.cells handle = some ⟨⟨inherited, .node entry edges depth free⟩, .evaluating⟩ := by
  dsimp only
  have started := beginNode_suspended candidate ⟨inherited, .node entry edges depth free⟩ before handle published suspended
  exact ⟨nodeCall_body_failed 0 0 0 0 0 0 0 0 0 0 0 candidate _ before _ _ handle (.exhausted .nodeBody) started (by simp only [nodeBody]),
    FlatMemoThunk.setStatus_cell _ _ _ _ suspended⟩

-- Busy and missing remain distinct incomplete observations, even with all stage bounds zero.
example (node : NodeRequest) (edge : EdgeRequest) (before nodeAfter edgeAfter : Caller width) (nh eh : Nat)
    (busy : beginNode node before = (nh, .busy, nodeAfter))
    (absent : beginEdge edge before = (eh, .absent, edgeAfter)) :
    nodeCall 0 0 0 0 0 0 0 0 0 0 0 node before = .failed (.nodeMemo nh .busy) nodeAfter ∧
      edgeCall 0 0 0 0 0 0 0 0 0 0 0 edge before = .failed (.edgeMemo eh .absent) edgeAfter :=
  ⟨nodeCall_busy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ busy,
    edgeCall_absent _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ absent⟩

-- A rejected winning edge uses the actual parent sentinel and finishes only the selected owner.
example (candidate original : EdgeRequest) (before running : Caller width) (handle : Nat)
    (started : beginEdge candidate before = (handle, .evaluate original, running))
    (rejected : SourceEqualityMkEdgeAllocation.contradictory original.value.entry.key.constraint = true) :
    let built := SourceCurrentAllocatedMkEdge.reject original.value.entry.key.symbol running.checked
    edgeCall 0 0 0 0 0 0 0 0 0 0 0 candidate before =
      .done built.1 (finishEdge handle built.1 (advance running built.2 running.fourth running.merge)) := by
  dsimp only
  apply edgeCall_body_done 0 0 0 0 0 0 0 0 0 0 0 candidate original before running _ handle _ started
  simp only [edgeBody, SourceCurrentAllocatedParentWorker.edge_rejected _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rejected]

-- A failed inherited prefix keeps its own returned operation state and makes no child call.
example (inherited : EqValue) (value : Edge) (before : Caller width) (message : String)
    (failed : (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations).1 = .error message) :
    descendants 0 0 0 0 0 0 0 0 0 0 0 inherited value before =
      .failed (.inherited message) (advance before
        (advanceHeap before.checked ⟨before.checked.native.machine.heap,
          (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations).2⟩)
        before.fourth before.merge) := by
  simp only [descendants, failed]

-- A missing inherited value remains distinct at the same actual prefix return.
example (inherited : EqValue) (value : Edge) (before : Caller width)
    (missing : (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations).1 = .ok none) :
    descendants 0 0 0 0 0 0 0 0 0 0 0 inherited value before =
      .failed .missingInherited (advance before
        (advanceHeap before.checked ⟨before.checked.native.machine.heap,
          (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations).2⟩)
        before.fourth before.merge) := by
  simp only [descendants, missing]

-- Contradiction erases every current slot, including an empty list, without inspecting child calls.
example (values : List Node) (before : Caller width) :
    children 0 0 0 0 0 0 0 0 0 0 0 .contradiction values before =
      .done (EqualityLeafProjectionRuntimeEmpty.erase values) before ∧
      (EqualityLeafProjectionRuntimeEmpty.erase values).length = values.length := by
  exact ⟨by simp only [children], by simp [EqualityLeafProjectionRuntimeEmpty.erase]⟩

-- Mu pending retains its actual partial heap and all other caller components.
example (inherited : EqValue) (entry : Cache.Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Node)
    (before : Caller width) (key : InternedBinderProtocol.NodeKey) (heap : Heap)
    (pending : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap = .pending key heap) :
    nodeBody 0 0 0 0 0 0 0 0 0 0 0 ⟨inherited, .mu entry body depth ordinary⟩ before =
      .failed (.binder (.pending key heap))
        (advance before (advanceHeap before.checked ⟨heap, before.checked.operations⟩) before.fourth before.merge) := by
  simp only [nodeBody, pending]

-- A row consumes its narrowed returned edge, descendants return, and then the suffix in order.
example (f g s r e p h m c n budget : Nat) (inherited : EqValue) (original narrowed result : Edge)
    (rest results : List Edge) (before middle after final : Caller width)
    (head : edgeCall f g s r e p h m c n budget ⟨inherited, original⟩ before = .done narrowed middle)
    (child : descendants f g s r e p h m c n budget inherited narrowed middle = .done result after)
    (tail : rows f g s r e p h m c n budget inherited rest after = .done results final) :
    rows (f+1) g s r e p h m c n budget inherited (original::rest) before = .done (result::results) final := by
  simp only [rows, head, child, tail, Outcome.bind]

-- Indexed descent occurs at the actual current state, and its node return supplies the tail state.
example (f g s r e p h m c n budget : Nat) (combined : EqValue) (index : Nat) (value result : Node)
    (rest results : List Node) (before middle after : Caller width)
    (head : nodeCall f g s r e p h m c n budget
      ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
      (SourceCurrentAllocatedPartialGraph.descend before combined index).2 = .done result middle)
    (tail : walk f g s r e p h m c n budget combined (index+1) rest middle = .done results after) :
    walk (f+1) g s r e p h m c n budget combined index (value::rest) before = .done (result::results) after := by
  simp only [walk, head, tail, Outcome.bind]

end MicroCFTA.CurrentOuterWorkerChecks
