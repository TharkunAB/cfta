import MicroCFTA.SourceCurrentAllocatedPartialWorker
import MicroCFTA.SourceCurrentAllocatedParentWorkerCompletion

/-!
# Stable literal execution of finite mutual caller graphs

Every supplied completed graph derives ten sufficient bounds for its exact
result and full caller state. The proof follows the two owner protocols,
ordered rows, returned-edge descendants, and actual indexed descent.
It does not construct a finite graph for every input or prove host demand.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion
open Language InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

/-- Ten independent sufficient bounds retain the same result and complete caller return. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Outcome A width)
    (result : A) (after : Caller width) : Prop :=
  ∃ f g s r e p h m c n, ∀ F G S R E P H M C N,
    f ≤ F → g ≤ G → s ≤ S → r ≤ R → e ≤ E → p ≤ P → h ≤ H → m ≤ M → c ≤ C → n ≤ N →
      evaluation F G S R E P H M C N = .done result after

private theorem post_stable
    {evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Outcome A width}
    {value : A} {middle : Caller width} {result : B} {after : Caller width}
    (one : StableRun evaluation value middle) (next : A → Caller width → Outcome B width)
    (completed : next value middle = .done result after) :
    StableRun (fun f g s r e p h m c n => (evaluation f g s r e p h m c n).bind next) result after := by
  obtain ⟨f, g, s, r, e, p, h, m, c, n, stable⟩ := one
  refine ⟨f, g, s, r, e, p, h, m, c, n, ?_⟩
  intro F G S R E P H M C N hf hg hs hr he hp hh hm hc hn
  simp only [stable F G S R E P H M C N hf hg hs hr he hp hh hm hc hn, Outcome.bind, completed]

private theorem bind_stable
    (first : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Outcome A width)
    (next : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → A → Caller width → Outcome B width)
    {value : A} {middle : Caller width} {result : B} {after : Caller width}
    (one : StableRun first value middle)
    (two : StableRun (fun f g s r e p h m c n => next f g s r e p h m c n value middle) result after) :
    StableRun (fun f g s r e p h m c n => (first f g s r e p h m c n).bind (next f g s r e p h m c n)) result after := by
  obtain ⟨f, g, s, r, e, p, h, m, c, n, stable⟩ := one
  obtain ⟨f', g', s', r', e', p', h', m', c', n', later⟩ := two
  refine ⟨max f f', max g g', max s s', max r r', max e e', max p p', max h h', max m m', max c c', max n n', ?_⟩
  intro F G S R E P H M C N hf hg hs hr he hp hh hm hc hn
  have firstDone := stable F G S R E P H M C N
    (Nat.le_trans (Nat.le_max_left _ _) hf) (Nat.le_trans (Nat.le_max_left _ _) hg)
    (Nat.le_trans (Nat.le_max_left _ _) hs) (Nat.le_trans (Nat.le_max_left _ _) hr)
    (Nat.le_trans (Nat.le_max_left _ _) he) (Nat.le_trans (Nat.le_max_left _ _) hp)
    (Nat.le_trans (Nat.le_max_left _ _) hh) (Nat.le_trans (Nat.le_max_left _ _) hm)
    (Nat.le_trans (Nat.le_max_left _ _) hc) (Nat.le_trans (Nat.le_max_left _ _) hn)
  have nextDone := later F G S R E P H M C N
    (Nat.le_trans (Nat.le_max_right _ _) hf) (Nat.le_trans (Nat.le_max_right _ _) hg)
    (Nat.le_trans (Nat.le_max_right _ _) hs) (Nat.le_trans (Nat.le_max_right _ _) hr)
    (Nat.le_trans (Nat.le_max_right _ _) he) (Nat.le_trans (Nat.le_max_right _ _) hp)
    (Nat.le_trans (Nat.le_max_right _ _) hh) (Nat.le_trans (Nat.le_max_right _ _) hm)
    (Nat.le_trans (Nat.le_max_right _ _) hc) (Nat.le_trans (Nat.le_max_right _ _) hn)
  simp only [firstDone, Outcome.bind, nextDone]

private theorem succ_stable
    {evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Outcome A width}
    {result : A} {after : Caller width} (zero : Outcome A width) (one : StableRun evaluation result after) :
    StableRun (fun f g s r e p h m c n => match f with
      | 0 => zero | fuel + 1 => evaluation fuel g s r e p h m c n) result after := by
  obtain ⟨f, g, s, r, e, p, h, m, c, n, stable⟩ := one
  refine ⟨f + 1, g, s, r, e, p, h, m, c, n, ?_⟩
  intro F G S R E P H M C N hf hg hs hr he hp hh hm hc hn
  cases F with
  | zero => omega
  | succ fuel => exact stable fuel G S R E P H M C N (by omega) hg hs hr he hp hh hm hc hn

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}
open SourceCurrentAllocatedPartialGraph

private def NodeCallStable (budget : Nat) (request : NodeRequest) (before : Caller width) (result : Node) (after : Caller width) : Prop :=
  StableRun (fun f g s r e p h m c n => nodeCall f g s r e p h m c n budget request before) result after
private def NodeBodyStable (budget : Nat) (request : NodeRequest) (before : Caller width) (result : Node) (after : Caller width) : Prop :=
  StableRun (fun f g s r e p h m c n => nodeBody f g s r e p h m c n budget request before) result after
private def EdgeCallStable (budget : Nat) (request : EdgeRequest) (before : Caller width) (result : Edge) (after : Caller width) : Prop :=
  StableRun (fun f g s r e p h m c n => edgeCall f g s r e p h m c n budget request before) result after
private def EdgeBodyStable (budget : Nat) (request : EdgeRequest) (before : Caller width) (result : Edge) (after : Caller width) : Prop :=
  StableRun (fun f g s r e p h m c n => edgeBody f g s r e p h m c n budget request before) result after
private def RowsStable (budget : Nat) (inherited : EqValue) (originals : List Edge) (before : Caller width) (results : List Edge) (after : Caller width) : Prop :=
  StableRun (fun f g s r e p h m c n => rows f g s r e p h m c n budget inherited originals before) results after
private def DescendantsStable (budget : Nat) (inherited : EqValue) (edge : Edge) (before : Caller width) (result : Edge) (after : Caller width) : Prop :=
  StableRun (fun f g s r e p h m c n => descendants f g s r e p h m c n budget inherited edge before) result after
private def ChildrenStable (budget : Nat) (combined : EqValue) (values : List Node) (before : Caller width) (results : List Node) (after : Caller width) : Prop :=
  StableRun (fun f g s r e p h m c n => children f g s r e p h m c n budget combined values before) results after
private def WalkStable (budget : Nat) (combined : EqValue) (index : Nat) (values : List Node) (before : Caller width) (results : List Node) (after : Caller width) : Prop :=
  StableRun (fun f g s r e p h m c n => walk f g s r e p h m c n budget combined index values before) results after

private theorem all_complete (budget : Nat) :
    (∀ request before result after, NodeCall budget request before result after → NodeCallStable (width := width) budget request before result after) ∧
    (∀ request before result after, NodeBody budget request before result after → NodeBodyStable (width := width) budget request before result after) ∧
    (∀ request before result after, EdgeCall budget request before result after → EdgeCallStable (width := width) budget request before result after) ∧
    (∀ request before result after, EdgeBody budget request before result after → EdgeBodyStable (width := width) budget request before result after) ∧
    (∀ inherited originals before results after, Rows budget inherited originals before results after → RowsStable (width := width) budget inherited originals before results after) ∧
    (∀ inherited edge before result after, Descendants budget inherited edge before result after → DescendantsStable (width := width) budget inherited edge before result after) ∧
    (∀ combined values before results after, Children budget combined values before results after → ChildrenStable (width := width) budget combined values before results after) ∧
    (∀ combined index values before results after, Walk budget combined index values before results after → WalkStable (width := width) budget combined index values before results after) := by
  have nodeHit : ∀ {request before handle result running},
      beginNode request before = (handle, .ready result, running) → NodeCallStable (width := width) budget request before result running := by
    intro request before handle result running started
    refine ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ?_⟩
    intro F G S R E P H M C N _ _ _ _ _ _ _ _ _ _
    exact nodeCall_ready F G S R E P H M C N budget request before running handle result started
  have nodeEvaluate : ∀ {request before handle running original result middle},
      beginNode request before = (handle, .evaluate original, running) → NodeBody budget original running result middle →
      NodeBodyStable budget original running result middle →
      NodeCallStable (width := width) budget request before result (finishNode handle result middle) := by
    intro request before handle running original result middle started _ body
    have completed := post_stable body (fun value state => .done value (finishNode handle value state)) rfl
    simpa only [NodeCallStable, nodeCall, started] using completed
  have nodeEmpty : ∀ {inherited before}, NodeBodyStable (width := width) budget ⟨inherited, .empty⟩ before .empty before := by
    intros
    exact ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, by intros; simp only [nodeBody]⟩
  have nodeUnion : ∀ {inherited entry members depth free before},
      NodeBodyStable (width := width) budget ⟨inherited, .union entry members depth free⟩ before (.union entry members depth free) before := by
    intros
    exact ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, by intros; simp only [nodeBody]⟩
  have nodeBinder : ∀ {entry body depth ordinary before result heap inherited},
      SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap = .done result heap →
      NodeBodyStable (width := width) budget ⟨inherited, .mu entry body depth ordinary⟩ before result
        (advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩) before.fourth before.merge) := by
    intro entry body depth ordinary before result heap inherited rebuilt
    refine ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ?_⟩
    intro F G S R E P H M C N _ _ _ _ _ _ _ _ _ _
    simp only [nodeBody, rebuilt]
  have nodeOrdinary : ∀ {inherited original before results middle entry depth free},
      Rows budget inherited original before results middle → RowsStable budget inherited original before results middle →
      NodeBodyStable (width := width) budget ⟨inherited, .node entry original depth free⟩ before
        (SourceCurrentAllocatedRawRebuild.modify (.node entry original depth free) original results middle.checked).1
        (advance middle (SourceCurrentAllocatedRawRebuild.modify (.node entry original depth free) original results middle.checked).2 middle.fourth middle.merge) := by
    intro inherited original before results middle entry depth free _ rowDone
    have completed := post_stable rowDone (fun results after =>
      let rebuilt := SourceCurrentAllocatedRawRebuild.modify (.node entry original depth free) original results after.checked
      .done rebuilt.1 (advance after rebuilt.2 after.fourth after.merge)) rfl
    have program : (fun f g s r e p h m c n => nodeBody f g s r e p h m c n budget
        ⟨inherited, .node entry original depth free⟩ before) =
        (fun f g s r e p h m c n => match f with
        | 0 => .failed (.exhausted .nodeBody) before
        | fuel + 1 => (rows fuel g s r e p h m c n budget inherited original before).bind
            fun results after => let rebuilt := SourceCurrentAllocatedRawRebuild.modify (.node entry original depth free) original results after.checked
              .done rebuilt.1 (advance after rebuilt.2 after.fourth after.merge)) := by
      funext f g s r e p h m c n
      rw [nodeBody.eq_def]
      rfl
    change StableRun _ _ _
    rw [program]
    exact succ_stable (.failed (.exhausted .nodeBody) before) completed
  have edgeHit : ∀ {request before handle result running},
      beginEdge request before = (handle, .ready result, running) → EdgeCallStable (width := width) budget request before result running := by
    intro request before handle result running started
    refine ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ?_⟩
    intro F G S R E P H M C N _ _ _ _ _ _ _ _ _ _
    exact edgeCall_ready F G S R E P H M C N budget request before running handle result started
  have edgeEvaluate : ∀ {request before handle running original result middle},
      beginEdge request before = (handle, .evaluate original, running) → EdgeBody budget original running result middle →
      EdgeBodyStable budget original running result middle →
      EdgeCallStable (width := width) budget request before result (finishEdge handle result middle) := by
    intro request before handle running original result middle started _ body
    have completed := post_stable body (fun value state => .done value (finishEdge handle value state)) rfl
    simpa only [EdgeCallStable, edgeCall, started] using completed
  have edgeParent : ∀ {edge loaded inherited before result checked fourth merge},
      (SourceEqualityMkEdgeAllocation.contradictory edge.entry.key.constraint = false →
        SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint before.checked.operations.constraints = .ok (some loaded)) →
      SourceCurrentAllocatedParentEdge.Edge budget edge.entry.key.symbol edge.entry.key.constraint loaded inherited edge.children
        before.checked before.fourth before.merge result checked fourth merge →
      EdgeBodyStable (width := width) budget ⟨inherited, edge⟩ before result (advance before checked fourth merge) := by
    intro edge loaded inherited before result checked fourth merge field parent
    obtain ⟨g, s, r, e, p, h, m, c, n, stable⟩ := SourceCurrentAllocatedParentWorkerCompletion.edge_complete parent field
    refine ⟨0, g, s, r, e, p, h, m, c, n, ?_⟩
    intro F G S R E P H M C N _ hg hs hr he hp hh hm hc hn
    have completed := stable G S R E P H M C N hg hs hr he hp hh hm hc hn
    simp only [edgeBody, completed]
  have rowsNil : ∀ {inherited before}, RowsStable (width := width) budget inherited [] before [] before := by
    intros
    exact ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, by intros; simp only [rows]⟩
  have rowsCons : ∀ {inherited original before narrowed middle result afterChildren originals results after},
      EdgeCall budget ⟨inherited, original⟩ before narrowed middle →
      Descendants budget inherited narrowed middle result afterChildren → Rows budget inherited originals afterChildren results after →
      EdgeCallStable budget ⟨inherited, original⟩ before narrowed middle →
      DescendantsStable budget inherited narrowed middle result afterChildren → RowsStable budget inherited originals afterChildren results after →
      RowsStable (width := width) budget inherited (original :: originals) before (result :: results) after := by
    intro inherited original before narrowed middle result afterChildren originals results after _ _ _ edgeDone childDone restDone
    have tail := post_stable restDone (fun values state => .done (result :: values) state) rfl
    have later := bind_stable _ (fun f g s r e p h m c n result current =>
      (rows f g s r e p h m c n budget inherited originals current).bind fun values final => .done (result :: values) final) childDone tail
    have completed := bind_stable _ (fun f g s r e p h m c n narrowed current =>
      (descendants f g s r e p h m c n budget inherited narrowed current).bind fun result later =>
        (rows f g s r e p h m c n budget inherited originals later).bind fun values final => .done (result :: values) final) edgeDone later
    have program : (fun f g s r e p h m c n => rows f g s r e p h m c n budget inherited (original :: originals) before) =
        (fun f g s r e p h m c n => match f with
        | 0 => .failed (.exhausted .rows) before
        | fuel + 1 => (edgeCall fuel g s r e p h m c n budget ⟨inherited, original⟩ before).bind fun narrowed current =>
            (descendants fuel g s r e p h m c n budget inherited narrowed current).bind fun result later =>
              (rows fuel g s r e p h m c n budget inherited originals later).bind fun values final => .done (result :: values) final) := by
      funext f g s r e p h m c n
      rw [rows.eq_def]
      rfl
    change StableRun _ _ _
    rw [program]
    exact succ_stable (.failed (.exhausted .rows) before) completed
  have descendantsRun : ∀ {edge inherited before payload results middle},
      (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some payload) →
      Children budget payload edge.children (prefixState before edge inherited) results middle →
      ChildrenStable budget payload edge.children (prefixState before edge inherited) results middle →
      DescendantsStable (width := width) budget inherited edge before
        (SourceCurrentAllocatedRawRebuild.edge edge results middle.checked).1
        (advance middle (SourceCurrentAllocatedRawRebuild.edge edge results middle.checked).2 middle.fourth middle.merge) := by
    intro edge inherited before payload results middle combined _ childDone
    have completed := post_stable childDone (fun results after =>
      let rebuilt := SourceCurrentAllocatedRawRebuild.edge edge results after.checked
      .done rebuilt.1 (advance after rebuilt.2 after.fourth after.merge)) rfl
    simpa only [DescendantsStable, descendants, combined, prefixState, SourceCurrentAllocatedInheritedPrefix.state] using completed
  have childrenContradiction : ∀ {values before},
      ChildrenStable (width := width) budget .contradiction values before (EqualityLeafProjectionRuntimeEmpty.erase values) before := by
    intros
    exact ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, by intros; simp only [children]⟩
  have childrenLive : ∀ {identity records values before results after},
      Walk budget (.live identity records) 0 values before results after → WalkStable budget (.live identity records) 0 values before results after →
      ChildrenStable (width := width) budget (.live identity records) values before results after := by
    intro identity records values before results after _ walkDone
    simpa only [ChildrenStable, WalkStable, children] using walkDone
  have walkNil : ∀ {combined index before}, WalkStable (width := width) budget combined index [] before [] before := by
    intros
    exact ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, by intros; simp only [walk]⟩
  have walkCons : ∀ {before combined index value result middle values results after},
      NodeCall budget ⟨(descend before combined index).1, value⟩ (descend before combined index).2 result middle →
      Walk budget combined (index + 1) values middle results after →
      NodeCallStable budget ⟨(descend before combined index).1, value⟩ (descend before combined index).2 result middle →
      WalkStable budget combined (index + 1) values middle results after →
      WalkStable (width := width) budget combined index (value :: values) before (result :: results) after := by
    intro before combined index value result middle values results after _ _ headDone restDone
    have tail := post_stable restDone (fun values state => .done (result :: values) state) rfl
    have completed := bind_stable _ (fun f g s r e p h m c n result current =>
      (walk f g s r e p h m c n budget combined (index + 1) values current).bind fun values final =>
        .done (result :: values) final) headDone tail
    have program : (fun f g s r e p h m c n => walk f g s r e p h m c n budget combined index (value :: values) before) =
        (fun f g s r e p h m c n => match f with
        | 0 => .failed (.exhausted .walk) before
        | fuel + 1 => let actual := descend before combined index
            (nodeCall fuel g s r e p h m c n budget ⟨actual.1, value⟩ actual.2).bind fun result current =>
              (walk fuel g s r e p h m c n budget combined (index + 1) values current).bind fun values final => .done (result :: values) final) := by
      funext f g s r e p h m c n
      rw [walk.eq_def]
      rfl
    change StableRun _ _ _
    rw [program]
    exact succ_stable (.failed (.exhausted .walk) before) completed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro request before result after actual
    exact NodeCall.rec
      (motive_1 := fun request before result after _ => NodeCallStable budget request before result after)
      (motive_2 := fun request before result after _ => NodeBodyStable budget request before result after)
      (motive_3 := fun request before result after _ => EdgeCallStable budget request before result after)
      (motive_4 := fun request before result after _ => EdgeBodyStable budget request before result after)
      (motive_5 := fun inherited originals before results after _ => RowsStable budget inherited originals before results after)
      (motive_6 := fun inherited edge before result after _ => DescendantsStable budget inherited edge before result after)
      (motive_7 := fun combined values before results after _ => ChildrenStable budget combined values before results after)
      (motive_8 := fun combined index values before results after _ => WalkStable budget combined index values before results after)
      nodeHit nodeEvaluate nodeEmpty nodeUnion nodeBinder nodeOrdinary edgeHit edgeEvaluate edgeParent
      rowsNil rowsCons descendantsRun childrenContradiction childrenLive walkNil walkCons actual
  · intro request before result after actual
    exact NodeBody.rec
      (motive_1 := fun request before result after _ => NodeCallStable budget request before result after)
      (motive_2 := fun request before result after _ => NodeBodyStable budget request before result after)
      (motive_3 := fun request before result after _ => EdgeCallStable budget request before result after)
      (motive_4 := fun request before result after _ => EdgeBodyStable budget request before result after)
      (motive_5 := fun inherited originals before results after _ => RowsStable budget inherited originals before results after)
      (motive_6 := fun inherited edge before result after _ => DescendantsStable budget inherited edge before result after)
      (motive_7 := fun combined values before results after _ => ChildrenStable budget combined values before results after)
      (motive_8 := fun combined index values before results after _ => WalkStable budget combined index values before results after)
      nodeHit nodeEvaluate nodeEmpty nodeUnion nodeBinder nodeOrdinary edgeHit edgeEvaluate edgeParent
      rowsNil rowsCons descendantsRun childrenContradiction childrenLive walkNil walkCons actual
  · intro request before result after actual
    exact EdgeCall.rec
      (motive_1 := fun request before result after _ => NodeCallStable budget request before result after)
      (motive_2 := fun request before result after _ => NodeBodyStable budget request before result after)
      (motive_3 := fun request before result after _ => EdgeCallStable budget request before result after)
      (motive_4 := fun request before result after _ => EdgeBodyStable budget request before result after)
      (motive_5 := fun inherited originals before results after _ => RowsStable budget inherited originals before results after)
      (motive_6 := fun inherited edge before result after _ => DescendantsStable budget inherited edge before result after)
      (motive_7 := fun combined values before results after _ => ChildrenStable budget combined values before results after)
      (motive_8 := fun combined index values before results after _ => WalkStable budget combined index values before results after)
      nodeHit nodeEvaluate nodeEmpty nodeUnion nodeBinder nodeOrdinary edgeHit edgeEvaluate edgeParent
      rowsNil rowsCons descendantsRun childrenContradiction childrenLive walkNil walkCons actual
  · intro request before result after actual
    exact EdgeBody.rec
      (motive_1 := fun request before result after _ => NodeCallStable budget request before result after)
      (motive_2 := fun request before result after _ => NodeBodyStable budget request before result after)
      (motive_3 := fun request before result after _ => EdgeCallStable budget request before result after)
      (motive_4 := fun request before result after _ => EdgeBodyStable budget request before result after)
      (motive_5 := fun inherited originals before results after _ => RowsStable budget inherited originals before results after)
      (motive_6 := fun inherited edge before result after _ => DescendantsStable budget inherited edge before result after)
      (motive_7 := fun combined values before results after _ => ChildrenStable budget combined values before results after)
      (motive_8 := fun combined index values before results after _ => WalkStable budget combined index values before results after)
      nodeHit nodeEvaluate nodeEmpty nodeUnion nodeBinder nodeOrdinary edgeHit edgeEvaluate edgeParent
      rowsNil rowsCons descendantsRun childrenContradiction childrenLive walkNil walkCons actual
  · intro inherited originals before results after actual
    exact Rows.rec
      (motive_1 := fun request before result after _ => NodeCallStable budget request before result after)
      (motive_2 := fun request before result after _ => NodeBodyStable budget request before result after)
      (motive_3 := fun request before result after _ => EdgeCallStable budget request before result after)
      (motive_4 := fun request before result after _ => EdgeBodyStable budget request before result after)
      (motive_5 := fun inherited originals before results after _ => RowsStable budget inherited originals before results after)
      (motive_6 := fun inherited edge before result after _ => DescendantsStable budget inherited edge before result after)
      (motive_7 := fun combined values before results after _ => ChildrenStable budget combined values before results after)
      (motive_8 := fun combined index values before results after _ => WalkStable budget combined index values before results after)
      nodeHit nodeEvaluate nodeEmpty nodeUnion nodeBinder nodeOrdinary edgeHit edgeEvaluate edgeParent
      rowsNil rowsCons descendantsRun childrenContradiction childrenLive walkNil walkCons actual
  · intro inherited edge before result after actual
    exact Descendants.rec
      (motive_1 := fun request before result after _ => NodeCallStable budget request before result after)
      (motive_2 := fun request before result after _ => NodeBodyStable budget request before result after)
      (motive_3 := fun request before result after _ => EdgeCallStable budget request before result after)
      (motive_4 := fun request before result after _ => EdgeBodyStable budget request before result after)
      (motive_5 := fun inherited originals before results after _ => RowsStable budget inherited originals before results after)
      (motive_6 := fun inherited edge before result after _ => DescendantsStable budget inherited edge before result after)
      (motive_7 := fun combined values before results after _ => ChildrenStable budget combined values before results after)
      (motive_8 := fun combined index values before results after _ => WalkStable budget combined index values before results after)
      nodeHit nodeEvaluate nodeEmpty nodeUnion nodeBinder nodeOrdinary edgeHit edgeEvaluate edgeParent
      rowsNil rowsCons descendantsRun childrenContradiction childrenLive walkNil walkCons actual
  · intro combined values before results after actual
    exact Children.rec
      (motive_1 := fun request before result after _ => NodeCallStable budget request before result after)
      (motive_2 := fun request before result after _ => NodeBodyStable budget request before result after)
      (motive_3 := fun request before result after _ => EdgeCallStable budget request before result after)
      (motive_4 := fun request before result after _ => EdgeBodyStable budget request before result after)
      (motive_5 := fun inherited originals before results after _ => RowsStable budget inherited originals before results after)
      (motive_6 := fun inherited edge before result after _ => DescendantsStable budget inherited edge before result after)
      (motive_7 := fun combined values before results after _ => ChildrenStable budget combined values before results after)
      (motive_8 := fun combined index values before results after _ => WalkStable budget combined index values before results after)
      nodeHit nodeEvaluate nodeEmpty nodeUnion nodeBinder nodeOrdinary edgeHit edgeEvaluate edgeParent
      rowsNil rowsCons descendantsRun childrenContradiction childrenLive walkNil walkCons actual
  · intro combined index values before results after actual
    exact Walk.rec
      (motive_1 := fun request before result after _ => NodeCallStable budget request before result after)
      (motive_2 := fun request before result after _ => NodeBodyStable budget request before result after)
      (motive_3 := fun request before result after _ => EdgeCallStable budget request before result after)
      (motive_4 := fun request before result after _ => EdgeBodyStable budget request before result after)
      (motive_5 := fun inherited originals before results after _ => RowsStable budget inherited originals before results after)
      (motive_6 := fun inherited edge before result after _ => DescendantsStable budget inherited edge before result after)
      (motive_7 := fun combined values before results after _ => ChildrenStable budget combined values before results after)
      (motive_8 := fun combined index values before results after _ => WalkStable budget combined index values before results after)
      nodeHit nodeEvaluate nodeEmpty nodeUnion nodeBinder nodeOrdinary edgeHit edgeEvaluate edgeParent
      rowsNil rowsCons descendantsRun childrenContradiction childrenLive walkNil walkCons actual

/-- Finite node calls execute the same stored owner and exact finish handle. -/
theorem nodeCall_complete {budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    (actual : NodeCall budget request before result after) :
    StableRun (fun f g s r e p h m c n => nodeCall f g s r e p h m c n budget request before) result after :=
  (all_complete budget).1 request before result after actual

/-- Finite node bodies execute their literal terminal or ordinary reconstruction branch. -/
theorem nodeBody_complete {budget : Nat} {request : NodeRequest} {before after : Caller width} {result : Node}
    (actual : NodeBody budget request before result after) :
    StableRun (fun f g s r e p h m c n => nodeBody f g s r e p h m c n budget request before) result after :=
  (all_complete budget).2.1 request before result after actual

/-- Finite edge calls execute and finish their own stored winner. -/
theorem edgeCall_complete {budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (actual : EdgeCall budget request before result after) :
    StableRun (fun f g s r e p h m c n => edgeCall f g s r e p h m c n budget request before) result after :=
  (all_complete budget).2.2.1 request before result after actual

/-- Finite parent bodies retain their exact checked and warm-memo return in the full caller. -/
theorem edgeBody_complete {budget : Nat} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    (actual : EdgeBody budget request before result after) :
    StableRun (fun f g s r e p h m c n => edgeBody f g s r e p h m c n budget request before) result after :=
  (all_complete budget).2.2.2.1 request before result after actual

/-- Finite rows run edge, returned-edge descendants, and suffix at their exact returns. -/
theorem rows_complete {budget : Nat} {inherited : EqValue} {originals : List Edge} {before after : Caller width} {results : List Edge}
    (actual : Rows budget inherited originals before results after) :
    StableRun (fun f g s r e p h m c n => rows f g s r e p h m c n budget inherited originals before) results after :=
  (all_complete budget).2.2.2.2.1 inherited originals before results after actual

/-- Finite descendants use the actual inherited prefix before child work and raw rebuilding. -/
theorem descendants_complete {budget : Nat} {inherited : EqValue} {edge : Edge} {before after : Caller width} {result : Edge}
    (actual : Descendants budget inherited edge before result after) :
    StableRun (fun f g s r e p h m c n => descendants f g s r e p h m c n budget inherited edge before) result after :=
  (all_complete budget).2.2.2.2.2.1 inherited edge before result after actual

/-- Contradiction skips calls; a finite live child graph follows the same indexed walk. -/
theorem children_complete {budget : Nat} {combined : EqValue} {values : List Node} {before after : Caller width} {results : List Node}
    (actual : Children budget combined values before results after) :
    StableRun (fun f g s r e p h m c n => children f g s r e p h m c n budget combined values before) results after :=
  (all_complete budget).2.2.2.2.2.2.1 combined values before results after actual

/-- Finite indexed walks use each literal descent result at the current operation state. -/
theorem walk_complete {budget : Nat} {combined : EqValue} {index : Nat} {values : List Node} {before after : Caller width} {results : List Node}
    (actual : Walk budget combined index values before results after) :
    StableRun (fun f g s r e p h m c n => walk f g s r e p h m c n budget combined index values before) results after :=
  (all_complete budget).2.2.2.2.2.2.2 combined index values before results after actual

end MicroCFTA.SourceCurrentAllocatedPartialWorkerCompletion
