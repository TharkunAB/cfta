import MicroCFTA.SourceCurrentWorkerOperationGrowth

/-!
# Operation growth along literal outer prefixes

Actual bounded calls derive operation growth without completed graphs or
range certificates. A reached activation retains its ready values and
successful field loads at the exact current caller. This does not exclude
an active key collision or bound the number of fresh requests.
-/
namespace MicroCFTA.SourceCurrentOuterExecutionGrowth
open Cache InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker
open SourceCurrentOuterCopiedWarmHit (Phase)
open SourceCurrentOuterExecutionAncestry (Step Reached Ancestor)
open SourceEqualityConstraintMemoAllocation (Grows)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "caller" => SourceCurrentOuterActiveAncestry.caller
local notation "run" => SourceCurrentOuterActiveAncestry.run

private theorem trans {before middle after : SourceEqualityConstraintMemoAllocation.State}
    (first : Grows before middle) (last : Grows middle after) : Grows before after :=
  SourceCurrentConjunctionEquality.grows_trans first last

private theorem bind (first : Outcome A width) (next : A → Caller width → Outcome B width)
    (head : Grows before first.state.checked.operations)
    (tail : ∀ value middle, Grows middle.checked.operations (next value middle).state.checked.operations) :
    Grows before (first.bind next).state.checked.operations := by
  cases first with
  | failed => exact head
  | done value middle => exact trans head (tail value middle)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

private theorem edge_body (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest) (before : Caller width) :
    Grows before.checked.operations (edgeBody fuel g s r e p h m c n budget request before).state.checked.operations := by
  have first := SourceCurrentWorkerOperationGrowth.parent g s r e p h m c n budget request.value.entry.key.symbol
    request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge
  unfold edgeBody
  cases actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget request.value.entry.key.symbol
      request.value.entry.key.constraint request.inherited request.value.children before.checked before.fourth before.merge <;>
    (rw [actual] at first; exact first)

private theorem edge_call (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest) (before : Caller width) :
    Grows before.checked.operations (edgeCall fuel g s r e p h m c n budget request before).state.checked.operations := by
  rcases started : beginEdge request before with ⟨handle,action,running⟩
  have same := (beginEdge_components request before).1
  rw [started] at same
  cases action <;> simp only [edgeCall,started]
  · rw [← same]; exact SourceEqualityConstraintMemoAllocation.grows_refl _
  · rw [← same]
    exact bind _ _ (edge_body fuel g s r e p h m c n budget _ running)
      (fun _value _middle => SourceEqualityConstraintMemoAllocation.grows_refl _)
  · rw [← same]; exact SourceEqualityConstraintMemoAllocation.grows_refl _
  · rw [← same]; exact SourceEqualityConstraintMemoAllocation.grows_refl _

private def NodeAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget request (before : Caller width),
  Grows before.checked.operations (nodeCall fuel g s r e p h m c n budget request before).state.checked.operations
private def BodyAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget request (before : Caller width),
  Grows before.checked.operations (nodeBody fuel g s r e p h m c n budget request before).state.checked.operations
private def RowsAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget inherited values (before : Caller width),
  Grows before.checked.operations (rows fuel g s r e p h m c n budget inherited values before).state.checked.operations
private def DescendantsAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget inherited value (before : Caller width),
  Grows before.checked.operations (descendants fuel g s r e p h m c n budget inherited value before).state.checked.operations
private def ChildrenAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget inherited values (before : Caller width),
  Grows before.checked.operations (children fuel g s r e p h m c n budget inherited values before).state.checked.operations
private def WalkAt (fuel : Nat) : Prop := ∀ g s r e p h m c n budget inherited index values (before : Caller width),
  Grows before.checked.operations (walk fuel g s r e p h m c n budget inherited index values before).state.checked.operations

private theorem all_growth (fuel : Nat) :
    NodeAt (width := width) fuel ∧ BodyAt (width := width) fuel ∧ RowsAt (width := width) fuel ∧
      DescendantsAt (width := width) fuel ∧ ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    have walkAt : WalkAt (width := width) fuel := by
      intro g s r e p h m c n budget combined index values before
      cases values with
      | nil => simpa only [walk,rows,Outcome.state] using SourceEqualityConstraintMemoAllocation.grows_refl before.checked.operations
      | cons value rest =>
        cases fuel with
        | zero => simpa only [walk,rows,nodeBody,Outcome.state] using SourceEqualityConstraintMemoAllocation.grows_refl before.checked.operations
        | succ fuel =>
          simp only [walk]
          have descent := SourceCurrentOperationGrowth.descend combined index before.checked.operations
          have first := (ih fuel (Nat.lt_succ_self _)).1 g s r e p h m c n budget
            ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1,value⟩
            (SourceCurrentAllocatedPartialGraph.descend before combined index).2
          apply bind _ _ (trans descent first)
          intro result middle
          apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.2.2.2 g s r e p h m c n budget combined (index+1) rest middle)
          intros
          exact SourceEqualityConstraintMemoAllocation.grows_refl _
    have childrenAt : ChildrenAt (width := width) fuel := by
      intro g s r e p h m c n budget combined values before
      cases combined with
      | contradiction => simpa only [children,Outcome.state] using SourceEqualityConstraintMemoAllocation.grows_refl before.checked.operations
      | live identity records => simpa only [children] using walkAt g s r e p h m c n budget (.live identity records) 0 values before
    have descendantsAt : DescendantsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited value before
      have first := SourceCurrentOperationGrowth.inherited value.entry.key.constraint inherited before.checked.operations
      unfold descendants
      dsimp only
      split
      · exact first
      · exact first
      · apply bind _ _ (trans first (childrenAt g s r e p h m c n budget _ value.children
          (SourceCurrentAllocatedPartialGraph.prefixState before value inherited)))
        intros
        exact SourceEqualityConstraintMemoAllocation.grows_refl _
    have rowsAt : RowsAt (width := width) fuel := by
      intro g s r e p h m c n budget inherited values before
      cases values with
      | nil => simpa only [walk,rows,Outcome.state] using SourceEqualityConstraintMemoAllocation.grows_refl before.checked.operations
      | cons value rest =>
        cases fuel with
        | zero => simpa only [walk,rows,nodeBody,Outcome.state] using SourceEqualityConstraintMemoAllocation.grows_refl before.checked.operations
        | succ fuel =>
          simp only [rows]
          apply bind _ _ (edge_call fuel g s r e p h m c n budget ⟨inherited,value⟩ before)
          intro value middle
          apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.2.1 g s r e p h m c n budget inherited value middle)
          intro value after
          apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.1 g s r e p h m c n budget inherited rest after)
          intros
          exact SourceEqualityConstraintMemoAllocation.grows_refl _
    have bodyAt : BodyAt (width := width) fuel := by
      intro g s r e p h m c n budget request before
      rcases request with ⟨inherited,value⟩
      cases value with
      | empty | reference | union => simpa only [nodeBody,Outcome.state] using SourceEqualityConstraintMemoAllocation.grows_refl before.checked.operations
      | mu entry body depth ordinary =>
        unfold nodeBody
        split <;> exact SourceEqualityConstraintMemoAllocation.grows_refl _
      | node entry original depth free =>
        cases fuel with
        | zero => simpa only [walk,rows,nodeBody,Outcome.state] using SourceEqualityConstraintMemoAllocation.grows_refl before.checked.operations
        | succ fuel =>
          simp only [nodeBody]
          apply bind _ _ ((ih fuel (Nat.lt_succ_self _)).2.2.1 g s r e p h m c n budget inherited original before)
          intros
          exact SourceEqualityConstraintMemoAllocation.grows_refl _
    have nodeAt : NodeAt (width := width) fuel := by
      intro g s r e p h m c n budget request before
      rcases started : beginNode request before with ⟨handle,action,running⟩
      have same := (beginNode_components request before).1
      rw [started] at same
      cases action <;> simp only [nodeCall,started]
      · rw [← same]; exact SourceEqualityConstraintMemoAllocation.grows_refl _
      · rw [← same]
        exact bind _ _ (bodyAt g s r e p h m c n budget _ running)
          (fun _value _middle => SourceEqualityConstraintMemoAllocation.grows_refl _)
      · rw [← same]; exact SourceEqualityConstraintMemoAllocation.grows_refl _
      · rw [← same]; exact SourceEqualityConstraintMemoAllocation.grows_refl _
    exact ⟨nodeAt,bodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

private theorem edge_done (actual : edgeCall fuel g s r e p h m c n budget request before = .done result after) :
    Grows before.checked.operations after.checked.operations := by
  have growth := edge_call fuel g s r e p h m c n budget request before
  rw [actual] at growth
  exact growth

private theorem node_done (actual : nodeCall fuel g s r e p h m c n budget request before = .done result after) :
    Grows before.checked.operations after.checked.operations := by
  have growth := (all_growth fuel).1 g s r e p h m c n budget request before
  rw [actual] at growth
  exact growth

private theorem descendants_done (actual : descendants fuel g s r e p h m c n budget inherited value before = .done result after) :
    Grows before.checked.operations after.checked.operations := by
  have growth := (all_growth fuel).2.2.2.1 g s r e p h m c n budget inherited value before
  rw [actual] at growth
  exact growth

/-- Every actual outer phase outcome retains all earlier equality-operation entries. -/
theorem phase (value : Phase width) :
    Grows (caller value).checked.operations (run g s r e p h m c n budget value).state.checked.operations := by
  cases value with
  | node fuel request before =>
    apply bind _ _ ((all_growth fuel).1 g s r e p h m c n budget request before)
    intros
    exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | body fuel request before =>
    apply bind _ _ ((all_growth fuel).2.1 g s r e p h m c n budget request before)
    intros
    exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | rows fuel inherited values before =>
    apply bind _ _ ((all_growth fuel).2.2.1 g s r e p h m c n budget inherited values before)
    intros
    exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | descendants fuel inherited value before =>
    apply bind _ _ ((all_growth fuel).2.2.2.1 g s r e p h m c n budget inherited value before)
    intros
    exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | children fuel inherited values before =>
    apply bind _ _ ((all_growth fuel).2.2.2.2.1 g s r e p h m c n budget inherited values before)
    intros
    exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | walk fuel inherited index values before =>
    apply bind _ _ ((all_growth fuel).2.2.2.2.2 g s r e p h m c n budget inherited index values before)
    intros
    exact SourceEqualityConstraintMemoAllocation.grows_refl _

/-- A literal prefix step derives operation growth from its actual earlier returns. -/
theorem step (actual : Step g s r e p h m c n budget first last) :
    Grows (caller first).checked.operations (caller last).checked.operations := by
  cases actual with
  | @node_evaluate request before handle running original fuel started =>
    have same := (beginNode_components request before).1
    rw [started] at same
    simp only [SourceCurrentOuterActiveAncestry.caller]
    rw [same]
    exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | body_rows | children_walk => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | rows_edge actual => exact edge_done actual
  | rows_tail edge actual => exact trans (edge_done edge) (descendants_done actual)
  | descendants_children => exact SourceCurrentOperationGrowth.inherited _ _ _
  | walk_head => exact SourceCurrentOperationGrowth.descend _ _ _
  | walk_tail actual =>
    apply trans ?_ (node_done actual)
    exact SourceCurrentOperationGrowth.descend _ _ _

/-- Every actual finite prefix derives growth without per-prefix invariants. -/
theorem reached (actual : Reached g s r e p h m c n budget first last) :
    Grows (caller first).checked.operations (caller last).checked.operations := by
  induction actual with
  | refl => exact SourceEqualityConstraintMemoAllocation.grows_refl _
  | snoc earlier last ih => exact trans ih (step last)

/-- A ready activation value remains the same complete value at its exact reached reader. -/
theorem ready (actual : Reached g s r e p h m c n budget first last)
    (value : SourceEqualityConstraintAllocation.Value)
    (initial : SourceEqualityConstraintAllocation.Ready (caller first).checked.operations.constraints value) :
    SourceEqualityConstraintAllocation.Ready (caller last).checked.operations.constraints value :=
  initial.grows (reached actual).constraint_growth

/-- Every successful original field load remains literal at the reached current operations. -/
theorem field (actual : Reached g s r e p h m c n budget first last) (original : Guard)
    (value : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (loaded : SourceEqualityConstraintFieldLookup.load original (caller first).checked.operations.constraints = .ok (some value)) :
    SourceEqualityConstraintFieldLookup.load original (caller last).checked.operations.constraints = .ok (some value) :=
  SourceCurrentConjunctionEquality.load_grows original _ _ (reached actual) value loaded

/-- Actual cache steps preserve initial constraint-cache validity. Operation memo validity is separate. -/
theorem cache_valid (actual : Reached g s r e p h m c n budget first last)
    (valid : Cache.Valid (caller first).checked.operations.constraints) :
    Cache.Valid (caller last).checked.operations.constraints :=
  Cache.steps_valid valid (reached actual).constraints

/-- Ready values with the same identity are equal at the derived reached reader. -/
theorem identity (actual : Reached g s r e p h m c n budget first last)
    (valid : Cache.Valid (caller first).checked.operations.constraints)
    (left right : SourceEqualityConstraintAllocation.Value)
    (leftReady : SourceEqualityConstraintAllocation.Ready (caller first).checked.operations.constraints left)
    (rightReady : SourceEqualityConstraintAllocation.Ready (caller last).checked.operations.constraints right)
    (same : left.identity = right.identity) : left = right :=
  SourceEqualityConstraintMemoAllocation.ready_eq_of_identity _ (cache_valid actual valid)
    left right (ready actual left leftReady) rightReady same

/-- An actual enclosing activation retains its full request and derived growth to the reader. -/
def GrowingAncestor (g s r e p h m c n budget : Nat) (entryPhase current : Phase width)
    (handle : Nat) (owner : NodeRequest) : Prop :=
  ∃ fuel request before running,
    Reached g s r e p h m c n budget entryPhase (.node fuel request before) ∧
    beginNode request before = (handle, .evaluate owner, running) ∧
    owner.key = request.key ∧ SourceCurrentOuterExecutionAncestry.NodeValid running ∧
    running.nodeResults.cells handle = some ⟨owner, .evaluating⟩ ∧
    Reached g s r e p h m c n budget (.body fuel owner running) current ∧
    Grows running.checked.operations (caller current).checked.operations

/-- The original exact activation witness derives growth without a per-prefix validity premise. -/
theorem ancestor (actual : Ancestor g s r e p h m c n budget entryPhase current handle owner) :
    GrowingAncestor g s r e p h m c n budget entryPhase current handle owner := by
  obtain ⟨fuel,request,before,running,earlier,started,key,valid,present,later⟩ := actual
  exact ⟨fuel,request,before,running,earlier,started,key,valid,present,later,reached later⟩

/-- A literal initial node-busy failure derives every active ancestor and its operation growth. -/
theorem initial (checked : SourceEqualityNativeDemand.State width)
    (merge : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (fuel : Nat) (request : NodeRequest)
    (actual : nodeCall fuel g s r e p h m c n budget request
      (SourceCurrentAllocatedPartialState.initial checked merge fourth) = .failed (.nodeMemo handle .busy) after) :
    ∃ next candidate,
      Reached g s r e p h m c n budget
        (.node fuel request (SourceCurrentAllocatedPartialState.initial checked merge fourth)) (.node next candidate after) ∧
      beginNode candidate after = (handle,.busy,after) ∧
      ∃ owner, after.nodeResults.cells handle = some ⟨owner,.evaluating⟩ ∧ owner.key = candidate.key ∧
        GrowingAncestor g s r e p h m c n budget
          (.node fuel request (SourceCurrentAllocatedPartialState.initial checked merge fourth)) (.node next candidate after) handle owner ∧
        (∀ other captured, after.nodeResults.cells other = some ⟨captured,.evaluating⟩ →
          GrowingAncestor g s r e p h m c n budget
            (.node fuel request (SourceCurrentAllocatedPartialState.initial checked merge fourth)) (.node next candidate after) other captured) := by
  obtain ⟨next,candidate,past,busy,owner,present,key,earlier,allOwners⟩ :=
    SourceCurrentOuterExecutionAncestry.initial checked merge fourth fuel request actual
  exact ⟨next,candidate,past,busy,owner,present,key,ancestor earlier,
    fun other captured present => ancestor (allOwners other captured present)⟩

end MicroCFTA.SourceCurrentOuterExecutionGrowth
