import MicroCFTA.SourceCurrentUnionNormalLocalParent
import MicroCFTA.SourceCurrentAllocatedPartialWorker

/-!
# Causal union normality through the full bounded outer worker

The proof includes both result families, actual captured owners, ordered
rows, inherited descent, Mu reconstruction, and raw rebuilding. Every
stopping outcome retains normality from its exact initial caller heap.
No closure, cap, successful callback, or future preservation law is used.
-/
namespace MicroCFTA.SourceCurrentUnionNormalOuter
open InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)

private theorem nested_bind (first : InternedNestedConstruction.Outcome Symbol Guard A)
    (next : A → State Symbol Guard → InternedNestedConstruction.Outcome Symbol Guard B)
    (normal : UnionNormal first.state)
    (later : ∀ value after, UnionNormal after → UnionNormal (next value after).state) :
    UnionNormal (first.bind next).state := by
  cases first with
  | pending => exact normal
  | done value state => exact later value state normal

private theorem matched [DecidableEq (EdgeKey Symbol Guard)] (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (name : InternedBinderProtocol.Reference)
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (SourceEqualityMuReconstruction.matched entry body depth ordinary name state).state := by
  unfold SourceEqualityMuReconstruction.matched
  split
  · exact normal
  · exact SourceCurrentRequiredUnionNormal.execute body _ state normal

private theorem callback [DecidableEq (EdgeKey Symbol Guard)] (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (name : InternedBinderProtocol.Reference)
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (SourceEqualityMuReconstruction.callback entry body depth ordinary name state).state :=
  nested_bind _ _ (matched entry body depth ordinary name state normal)
    (fun value after afterNormal => SourceCurrentRequiredUnionNormal.filter name value after afterNormal)

private theorem rebuild [DecidableEq (EdgeKey Symbol Guard)] (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (SourceEqualityMuReconstruction.rebuild entry body depth ordinary state).state := by
  apply nested_bind _ _ (callback entry body depth ordinary .depth state normal)
  intro actualDepth afterDepth depthNormal
  apply nested_bind _ _ (callback entry body depth ordinary _ afterDepth depthNormal)
  intro actualOrdinary afterOrdinary ordinaryNormal
  exact SourceCurrentRequiredUnionNormal.request true actualDepth actualOrdinary _ afterOrdinary ordinaryNormal
    (callback entry body depth ordinary)

open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

private def Normal (before : Caller width) : Prop := UnionNormal before.checked.native.machine.heap
private def Safe (actual : Outcome A width) : Prop := Normal actual.state

private theorem bind (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (normal : Safe first) (later : ∀ value after, Normal after → Safe (next value after)) : Safe (first.bind next) := by
  cases first with
  | failed => exact normal
  | done value state => exact later value state normal

private theorem raw_edge [DecidableEq (EdgeKey Symbol Guard)] (original : Edge) (values : List Node)
    (before : SourceEqualityNativeDemand.State width) (normal : UnionNormal before.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedRawRebuild.edge original values before).2.native.machine.heap :=
  SourceCurrentRequiredUnionNormal.edge original.entry.key.symbol original.entry.key.constraint values _ normal

private theorem raw_modify [DecidableEq (EdgeKey Symbol Guard)] (original : Node) (oldRows newRows : List Edge)
    (before : SourceEqualityNativeDemand.State width) (normal : UnionNormal before.native.machine.heap) :
    UnionNormal (SourceCurrentAllocatedRawRebuild.modify original oldRows newRows before).2.native.machine.heap := by
  unfold SourceCurrentAllocatedRawRebuild.modify SourceEqualityPartialNodeRebuild.modify
  dsimp only
  split
  · exact normal
  · exact SourceCurrentRequiredUnionNormal.node newRows _ normal

variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem edgeBody_safe (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before : Caller width) (normal : Normal before) : Safe (edgeBody fuel g s r e p h m c n budget request before) := by
  have retained := SourceCurrentUnionNormalLocalParent.parent g s r e p h m c n budget
    request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
    before.checked before.fourth before.merge normal
  cases actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited request.value.children
      before.checked before.fourth before.merge <;>
    simpa only [edgeBody,actual,SourceCurrentAllocatedParentWorker.Outcome.state,Safe,Normal,
      Outcome.state,advance] using retained

private theorem edgeCall_safe (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before : Caller width) (normal : Normal before) : Safe (edgeCall fuel g s r e p h m c n budget request before) := by
  rcases observed : beginEdge request before with ⟨handle,action,after⟩
  have afterNormal : Normal after := by
    have same := congrArg (fun result => result.2.2.checked) observed
    change before.checked = after.checked at same
    simpa only [←same] using normal
  cases action with
  | ready | busy | absent => simpa only [edgeCall,observed,Safe,Normal,Outcome.state] using afterNormal
  | evaluate owner =>
      simp only [edgeCall,observed]
      exact bind _ _ (edgeBody_safe fuel g s r e p h m c n budget owner after afterNormal)
        (fun _ _ middleNormal => middleNormal)

private def NodeCallAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget request (before : Caller width), Normal before →
    Safe (nodeCall fuel g s r e p h m c n budget request before)
private def NodeBodyAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget request (before : Caller width), Normal before →
    Safe (nodeBody fuel g s r e p h m c n budget request before)
private def RowsAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget inherited values (before : Caller width), Normal before →
    Safe (rows fuel g s r e p h m c n budget inherited values before)
private def DescendantsAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget inherited edge (before : Caller width), Normal before →
    Safe (descendants fuel g s r e p h m c n budget inherited edge before)
private def ChildrenAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget inherited values (before : Caller width), Normal before →
    Safe (children fuel g s r e p h m c n budget inherited values before)
private def WalkAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n budget inherited index values (before : Caller width), Normal before →
    Safe (walk fuel g s r e p h m c n budget inherited index values before)

private theorem all_safe (fuel : Nat) :
    NodeCallAt (width := width) fuel ∧ NodeBodyAt (width := width) fuel ∧
      RowsAt (width := width) fuel ∧ DescendantsAt (width := width) fuel ∧
      ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      have walkAt : WalkAt (width := width) fuel := by
        intro g s r e p h m c n budget inherited index values before normal
        cases values with
        | nil => simpa only [walk,Safe,Normal,Outcome.state] using normal
        | cons value rest =>
            cases fuel with
            | zero => simpa only [walk,Safe,Normal,Outcome.state] using normal
            | succ fuel =>
                simp only [walk]
                have descended : Normal (SourceCurrentAllocatedPartialGraph.descend before inherited index).2 := normal
                apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).1 _ _ _ _ _ _ _ _ _ _ _ _ descended)
                intro result middle middleNormal
                exact bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ middleNormal)
                  (fun _ _ afterNormal => afterNormal)
      have childrenAt : ChildrenAt (width := width) fuel := by
        intro g s r e p h m c n budget inherited values before normal
        cases inherited with
        | contradiction => simpa only [children,Safe,Normal,Outcome.state] using normal
        | live identity records =>
            exact walkAt g s r e p h m c n budget (.live identity records) 0 values before normal
      have descendantsAt : DescendantsAt (width := width) fuel := by
        intro g s r e p h m c n budget inherited edge before normal
        simp only [descendants]
        split
        · exact normal
        · exact normal
        · rename_i combined _
          apply bind _ _ (childrenAt g s r e p h m c n budget combined edge.children _ normal)
          intro results after afterNormal
          exact raw_edge edge results after.checked afterNormal
      have rowsAt : RowsAt (width := width) fuel := by
        intro g s r e p h m c n budget inherited values before normal
        cases values with
        | nil => simpa only [rows,Safe,Normal,Outcome.state] using normal
        | cons value rest =>
            cases fuel with
            | zero => simpa only [rows,Safe,Normal,Outcome.state] using normal
            | succ fuel =>
                simp only [rows]
                apply bind _ _ (edgeCall_safe _ _ _ _ _ _ _ _ _ _ _ _ _ normal)
                intro narrowed middle middleNormal
                apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ middleNormal)
                intro result after afterNormal
                exact bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ afterNormal)
                  (fun _ _ finalNormal => finalNormal)
      have bodyAt : NodeBodyAt (width := width) fuel := by
        intro g s r e p h m c n budget request before normal
        rcases request with ⟨inherited,value⟩
        cases value with
        | empty | union | reference => simpa only [nodeBody,Safe,Normal,Outcome.state] using normal
        | mu entry body depth ordinary =>
            have retained := rebuild entry body depth ordinary before.checked.native.machine.heap normal
            cases actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap <;>
              simpa only [nodeBody,actual,Safe,Normal,Outcome.state,advance,
                SourceCurrentAllocatedQueryMemo.advancePhysical,SourceRecursiveIntersectionThunks.advance,
                InternedNestedConstruction.Outcome.state] using retained
        | node entry originals depth free =>
            cases fuel with
            | zero => simpa only [nodeBody,Safe,Normal,Outcome.state] using normal
            | succ fuel =>
                simp only [nodeBody]
                exact bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ normal)
                  (fun results after afterNormal => raw_modify _ originals results after.checked afterNormal)
      have callAt : NodeCallAt (width := width) fuel := by
        intro g s r e p h m c n budget request before normal
        rcases observed : beginNode request before with ⟨handle,action,after⟩
        have afterNormal : Normal after := by
          have same := congrArg (fun result => result.2.2.checked) observed
          change before.checked = after.checked at same
          simpa only [←same] using normal
        cases action with
        | ready | busy | absent => simpa only [nodeCall,observed,Safe,Normal,Outcome.state] using afterNormal
        | evaluate owner =>
            simp only [nodeCall,observed]
            exact bind _ _ (bodyAt _ _ _ _ _ _ _ _ _ _ _ _ afterNormal)
              (fun _ _ middleNormal => middleNormal)
      exact ⟨callAt,bodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

/-- Actual node calls retain normality on ready, evaluating, busy, and absent observations. -/
theorem node_call (fuel g s r e p h m c n budget : Nat) (request : NodeRequest) (before : Caller width)
    (normal : UnionNormal before.checked.native.machine.heap) :
    UnionNormal (nodeCall fuel g s r e p h m c n budget request before).state.checked.native.machine.heap :=
  (all_safe fuel).1 _ _ _ _ _ _ _ _ _ _ _ _ normal

/-- All literal node bodies, including Mu callbacks and changed rows, retain normality. -/
theorem node_body (fuel g s r e p h m c n budget : Nat) (request : NodeRequest) (before : Caller width)
    (normal : UnionNormal before.checked.native.machine.heap) :
    UnionNormal (nodeBody fuel g s r e p h m c n budget request before).state.checked.native.machine.heap :=
  (all_safe fuel).2.1 _ _ _ _ _ _ _ _ _ _ _ _ normal

/-- Edge calls retain normality through the exact captured owner and finish handle. -/
theorem edge_call (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest) (before : Caller width)
    (normal : UnionNormal before.checked.native.machine.heap) :
    UnionNormal (edgeCall fuel g s r e p h m c n budget request before).state.checked.native.machine.heap :=
  edgeCall_safe _ _ _ _ _ _ _ _ _ _ _ _ _ normal

/-- The actual Parent worker supplies edge-body retention without an external callee law. -/
theorem edge_body (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest) (before : Caller width)
    (normal : UnionNormal before.checked.native.machine.heap) :
    UnionNormal (edgeBody fuel g s r e p h m c n budget request before).state.checked.native.machine.heap :=
  edgeBody_safe _ _ _ _ _ _ _ _ _ _ _ _ _ normal

/-- Ordered row traversal retains normality through every returned parent and descendant. -/
theorem row_pass (fuel g s r e p h m c n budget : Nat) (inherited : EqValue) (values : List Edge) (before : Caller width)
    (normal : UnionNormal before.checked.native.machine.heap) :
    UnionNormal (rows fuel g s r e p h m c n budget inherited values before).state.checked.native.machine.heap :=
  (all_safe fuel).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ normal

/-- Inherited prefixes and actual raw edge reconstruction retain the invariant. -/
theorem descendant_pass (fuel g s r e p h m c n budget : Nat) (inherited : EqValue) (value : Edge) (before : Caller width)
    (normal : UnionNormal before.checked.native.machine.heap) :
    UnionNormal (descendants fuel g s r e p h m c n budget inherited value before).state.checked.native.machine.heap :=
  (all_safe fuel).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ normal

/-- Contradictory erasure and live indexed children retain the same heap invariant. -/
theorem child_pass (fuel g s r e p h m c n budget : Nat) (inherited : EqValue) (values : List Node) (before : Caller width)
    (normal : UnionNormal before.checked.native.machine.heap) :
    UnionNormal (children fuel g s r e p h m c n budget inherited values before).state.checked.native.machine.heap :=
  (all_safe fuel).2.2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ normal

/-- Every indexed child walk retains normality at its exact stopping caller. -/
theorem indexed_walk (fuel g s r e p h m c n budget : Nat) (inherited : EqValue) (index : Nat) (values : List Node) (before : Caller width)
    (normal : UnionNormal before.checked.native.machine.heap) :
    UnionNormal (walk fuel g s r e p h m c n budget inherited index values before).state.checked.native.machine.heap :=
  (all_safe fuel).2.2.2.2.2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ normal
end MicroCFTA.SourceCurrentUnionNormalOuter
