import MicroCFTA.SourceCurrentAllocatedPartialWorker

/-!
# Ordered Parent entries in the bounded outer worker

The replay records only Parent calls that the literal execution enters.
It retains every failure prefix and the complete caller at each entry.
The outer fuel bounds the entry count without a source height bound.
No semantic domain, reached range, or completion premise is required.
This count excludes Mu reconstruction, raw rebuild, and descent allocations.
-/
namespace MicroCFTA.SourceCurrentOuterCallBudget
open InternedConstructorTemplates SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialWorker (Outcome)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

/-- A replay retains the exact worker outcome and the entered Parent sites. -/
structure Execution (Output : Type) (width : Nat) : Type 1 where
  /-- The full literal return or stopping diagnostic. -/
  outcome : Outcome Output width
  /-- Each entry retains the stored owner request and its full entry caller. -/
  calls : List (EdgeRequest × Caller width)

/-- A ternary call tree envelope includes every same-fuel phase chain. -/
def budget : Nat → Nat
  | 0 => 1
  | fuel + 1 => 3 * budget fuel + 1

private def pure (outcome : Outcome A width) : Execution A width := ⟨outcome, []⟩

private def bind (first : Execution A width) (next : A → Caller width → Execution B width) : Execution B width :=
  match first.outcome with
  | .failed fault after => ⟨.failed fault after, first.calls⟩
  | .done value after =>
      let last := next value after
      ⟨last.outcome, first.calls ++ last.calls⟩

variable {width : Nat}

private def Checked (replay : Execution A width) (actual : Outcome A width) (bound : Nat) : Prop :=
  replay.outcome = actual ∧ replay.calls.length ≤ bound

private theorem pure_checked (actual : Outcome A width) : Checked (pure actual) actual 0 :=
  ⟨rfl, Nat.le_refl _⟩

private theorem widen {replay : Execution A width} {actual : Outcome A width} {first last : Nat}
    (checked : Checked replay actual first) (increase : first ≤ last) : Checked replay actual last :=
  ⟨checked.1, Nat.le_trans checked.2 increase⟩

private theorem bind_checked (first : Execution A width) (next : A → Caller width → Execution B width)
    (actual : Outcome A width) (continued : A → Caller width → Outcome B width) (one two : Nat)
    (checked : Checked first actual one)
    (later : ∀ value after, Checked (next value after) (continued value after) two) :
    Checked (bind first next) (actual.bind continued) (one + two) := by
  rcases first with ⟨outcome, calls⟩
  rcases checked with ⟨rfl,bounded⟩
  cases outcome with
  | failed fault after => exact ⟨rfl, by simpa only [bind, List.length] using Nat.le_trans bounded (Nat.le_add_right one two)⟩
  | done value after =>
    exact ⟨(later value after).1, by simpa only [bind, List.length_append] using Nat.add_le_add bounded (later value after).2⟩

private theorem positive (fuel : Nat) : 1 ≤ budget fuel := by
  cases fuel <;> simp only [budget] <;> omega

private theorem post_checked (first : Execution A width) (next : A → Caller width → Outcome B width)
    (actual : Outcome A width) (bound : Nat) (checked : Checked first actual bound) :
    Checked (bind first (fun value after => pure (next value after))) (actual.bind next) bound := by
  simpa only [Nat.add_zero] using bind_checked first (fun value after => pure (next value after))
    actual next bound 0 checked (fun value after => pure_checked (next value after))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

mutual
private noncomputable def nodeCall (fuel g s r e p h m c n limit : Nat) (request : NodeRequest)
    (before : Caller width) : Execution Node width :=
  let actual := beginNode request before
  match actual.2.1 with
  | .ready result => pure (.done result actual.2.2)
  | .evaluate original =>
      bind (nodeBody fuel g s r e p h m c n limit original actual.2.2) fun result after =>
        pure (.done result (finishNode actual.1 result after))
  | .busy => pure (.failed (.nodeMemo actual.1 .busy) actual.2.2)
  | .absent => pure (.failed (.nodeMemo actual.1 .absent) actual.2.2)
termination_by (fuel, 3)

private noncomputable def nodeBody (fuel g s r e p h m c n limit : Nat) (request : NodeRequest)
    (before : Caller width) : Execution Node width :=
  match request.value with
  | .empty => pure (.done .empty before)
  | value@(.union ..) => pure (.done value before)
  | .reference name => pure (.failed (.unexpectedReference name) before)
  | .mu entry body depth ordinary =>
      match SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap with
      | .done result heap => pure (.done result (advance before
          (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩)
          before.fourth before.merge))
      | observation@(.pending _ heap) => pure (.failed (.binder observation) (advance before
          (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩)
          before.fourth before.merge))
  | value@(.node _ original _ _) =>
      match fuel with
      | 0 => pure (.failed (.exhausted .nodeBody) before)
      | next + 1 =>
          bind (rows next g s r e p h m c n limit request.inherited original before) fun results after =>
            let rebuilt := SourceCurrentAllocatedRawRebuild.modify value original results after.checked
            pure (.done rebuilt.1 (advance after rebuilt.2 after.fourth after.merge))
termination_by (fuel, 2)

private noncomputable def edgeCall (fuel g s r e p h m c n limit : Nat) (request : EdgeRequest)
    (before : Caller width) : Execution Edge width :=
  let actual := beginEdge request before
  match actual.2.1 with
  | .ready result => pure (.done result actual.2.2)
  | .evaluate original =>
      bind (edgeBody fuel g s r e p h m c n limit original actual.2.2) fun result after =>
        pure (.done result (finishEdge actual.1 result after))
  | .busy => pure (.failed (.edgeMemo actual.1 .busy) actual.2.2)
  | .absent => pure (.failed (.edgeMemo actual.1 .absent) actual.2.2)

private noncomputable def edgeBody (fuel g s r e p h m c n limit : Nat) (request : EdgeRequest)
    (before : Caller width) : Execution Edge width :=
  ⟨SourceCurrentAllocatedPartialWorker.edgeBody fuel g s r e p h m c n limit request before,
    [(request, before)]⟩

private noncomputable def rows (fuel g s r e p h m c n limit : Nat) (inherited : EqValue)
    (originals : List Edge) (before : Caller width) : Execution (List Edge) width :=
  match originals with
  | [] => pure (.done [] before)
  | original :: rest =>
      match fuel with
      | 0 => pure (.failed (.exhausted .rows) before)
      | next + 1 =>
          bind (edgeCall next g s r e p h m c n limit ⟨inherited, original⟩ before) fun narrowed middle =>
            bind (descendants next g s r e p h m c n limit inherited narrowed middle) fun result after =>
              bind (rows next g s r e p h m c n limit inherited rest after) fun results final =>
                pure (.done (result :: results) final)
termination_by (fuel, 2)

private noncomputable def descendants (fuel g s r e p h m c n limit : Nat) (inherited : EqValue)
    (edge : Edge) (before : Caller width) : Execution Edge width :=
  let actual := SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations
  let middle := advance before
    (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨before.checked.native.machine.heap, actual.2⟩)
    before.fourth before.merge
  match actual.1 with
  | .error message => pure (.failed (.inherited message) middle)
  | .ok none => pure (.failed .missingInherited middle)
  | .ok (some combined) =>
      bind (children fuel g s r e p h m c n limit combined edge.children middle) fun results after =>
        let rebuilt := SourceCurrentAllocatedRawRebuild.edge edge results after.checked
        pure (.done rebuilt.1 (advance after rebuilt.2 after.fourth after.merge))
termination_by (fuel, 2)

private noncomputable def children (fuel g s r e p h m c n limit : Nat) (combined : EqValue)
    (values : List Node) (before : Caller width) : Execution (List Node) width :=
  match combined with
  | .contradiction => pure (.done (EqualityLeafProjectionRuntimeEmpty.erase values) before)
  | .live _ _ => walk fuel g s r e p h m c n limit combined 0 values before
termination_by (fuel, 1)

private noncomputable def walk (fuel g s r e p h m c n limit : Nat) (combined : EqValue) (index : Nat)
    (values : List Node) (before : Caller width) : Execution (List Node) width :=
  match values with
  | [] => pure (.done [] before)
  | value :: rest =>
      match fuel with
      | 0 => pure (.failed (.exhausted .walk) before)
      | next + 1 =>
          let actual := SourceCurrentAllocatedPartialGraph.descend before combined index
          bind (nodeCall next g s r e p h m c n limit ⟨actual.1, value⟩ actual.2) fun result middle =>
            bind (walk next g s r e p h m c n limit combined (index + 1) rest middle) fun results after =>
              pure (.done (result :: results) after)
termination_by (fuel, 0)
end

private def NodeAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n limit (request : NodeRequest) (before : Caller width),
    Checked (nodeCall fuel g s r e p h m c n limit request before)
      (SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n limit request before) (budget fuel)

private def BodyAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n limit (request : NodeRequest) (before : Caller width),
    Checked (nodeBody fuel g s r e p h m c n limit request before)
      (SourceCurrentAllocatedPartialWorker.nodeBody fuel g s r e p h m c n limit request before) (budget fuel)

private def EdgeAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n limit (request : EdgeRequest) (before : Caller width),
    Checked (edgeCall fuel g s r e p h m c n limit request before)
      (SourceCurrentAllocatedPartialWorker.edgeCall fuel g s r e p h m c n limit request before) (budget fuel)

private def EdgeBodyAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n limit (request : EdgeRequest) (before : Caller width),
    Checked (edgeBody fuel g s r e p h m c n limit request before)
      (SourceCurrentAllocatedPartialWorker.edgeBody fuel g s r e p h m c n limit request before) (budget fuel)

private def RowsAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n limit (inherited : EqValue) (values : List Edge) (before : Caller width),
    Checked (rows fuel g s r e p h m c n limit inherited values before)
      (SourceCurrentAllocatedPartialWorker.rows fuel g s r e p h m c n limit inherited values before) (budget fuel)

private def DescendantsAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n limit (inherited : EqValue) (value : Edge) (before : Caller width),
    Checked (descendants fuel g s r e p h m c n limit inherited value before)
      (SourceCurrentAllocatedPartialWorker.descendants fuel g s r e p h m c n limit inherited value before) (budget fuel)

private def ChildrenAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n limit (combined : EqValue) (values : List Node) (before : Caller width),
    Checked (children fuel g s r e p h m c n limit combined values before)
      (SourceCurrentAllocatedPartialWorker.children fuel g s r e p h m c n limit combined values before) (budget fuel)

private def WalkAt (fuel : Nat) : Prop :=
  ∀ g s r e p h m c n limit (combined : EqValue) (index : Nat) (values : List Node) (before : Caller width),
    Checked (walk fuel g s r e p h m c n limit combined index values before)
      (SourceCurrentAllocatedPartialWorker.walk fuel g s r e p h m c n limit combined index values before) (budget fuel)

private theorem all_checked (fuel : Nat) :
    NodeAt (width := width) fuel ∧ BodyAt (width := width) fuel ∧ EdgeAt (width := width) fuel ∧
    EdgeBodyAt (width := width) fuel ∧ RowsAt (width := width) fuel ∧ DescendantsAt (width := width) fuel ∧
    ChildrenAt (width := width) fuel ∧ WalkAt (width := width) fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    have edgeBodyAt : EdgeBodyAt (width := width) fuel := by
      intro g s r e p h m c n limit request before
      exact ⟨rfl, positive fuel⟩
    have edgeAt : EdgeAt (width := width) fuel := by
      intro g s r e p h m c n limit request before
      rcases started : beginEdge request before with ⟨handle,action,running⟩
      cases action with
      | ready value | busy | absent =>
        simp only [edgeCall, SourceCurrentAllocatedPartialWorker.edgeCall, started]
        exact widen (pure_checked _) (by omega)
      | evaluate original =>
        simpa only [edgeCall,SourceCurrentAllocatedPartialWorker.edgeCall,started] using
          post_checked _ (fun result after => .done result (finishEdge handle result after)) _ _
            (edgeBodyAt g s r e p h m c n limit original running)
    have walkAt : WalkAt (width := width) fuel := by
      intro g s r e p h m c n limit combined index values before
      cases values with
      | nil =>
        simp only [walk,SourceCurrentAllocatedPartialWorker.walk]
        exact widen (pure_checked _) (by omega)
      | cons value rest =>
        cases fuel with
        | zero =>
          simp only [walk,SourceCurrentAllocatedPartialWorker.walk]
          exact widen (pure_checked _) (by omega)
        | succ fuel =>
          have first := (ih fuel (Nat.lt_succ_self _)).1 g s r e p h m c n limit
            ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1,value⟩
            (SourceCurrentAllocatedPartialGraph.descend before combined index).2
          have tails := (ih fuel (Nat.lt_succ_self _)).2.2.2.2.2.2.2
          have result := bind_checked _ _ _ _ (budget fuel) (budget fuel) first
            (fun result middle => post_checked _ (fun results after => .done (result :: results) after) _ _
              (tails g s r e p h m c n limit combined (index+1) rest middle))
          simpa only [walk,SourceCurrentAllocatedPartialWorker.walk] using
            widen result (by simp only [budget]; omega)
    have childrenAt : ChildrenAt (width := width) fuel := by
      intro g s r e p h m c n limit combined values before
      cases combined with
      | contradiction =>
        simp only [children,SourceCurrentAllocatedPartialWorker.children]
        exact widen (pure_checked _) (by omega)
      | live identity records =>
        simpa only [children,SourceCurrentAllocatedPartialWorker.children] using
          walkAt g s r e p h m c n limit (.live identity records) 0 values before
    have descendantsAt : DescendantsAt (width := width) fuel := by
      intro g s r e p h m c n limit inherited value before
      cases observed : (SourceCurrentAllocatedInheritedPrefix.run value.entry.key.constraint inherited before.checked.operations).1 with
      | error message =>
        simp only [descendants,SourceCurrentAllocatedPartialWorker.descendants,observed]
        exact widen (pure_checked _) (by omega)
      | ok answer =>
        cases answer with
        | none =>
          simp only [descendants,SourceCurrentAllocatedPartialWorker.descendants,observed]
          exact widen (pure_checked _) (by omega)
        | some combined =>
          simp only [descendants,SourceCurrentAllocatedPartialWorker.descendants,observed]
          exact post_checked _ _ _ _ (childrenAt g s r e p h m c n limit combined value.children _)
    have rowsAt : RowsAt (width := width) fuel := by
      intro g s r e p h m c n limit inherited values before
      cases values with
      | nil =>
        simp only [rows,SourceCurrentAllocatedPartialWorker.rows]
        exact widen (pure_checked _) (by omega)
      | cons value rest =>
        cases fuel with
        | zero =>
          simp only [rows,SourceCurrentAllocatedPartialWorker.rows]
          exact widen (pure_checked _) (by omega)
        | succ fuel =>
          have first := (ih fuel (Nat.lt_succ_self _)).2.2.1 g s r e p h m c n limit ⟨inherited,value⟩ before
          have below := (ih fuel (Nat.lt_succ_self _)).2.2.2.2.2.1
          have tails := (ih fuel (Nat.lt_succ_self _)).2.2.2.2.1
          have result := bind_checked _ _ _ _ (budget fuel) (budget fuel + budget fuel) first
            (fun narrowed middle => bind_checked _ _ _ _ (budget fuel) (budget fuel)
              (below g s r e p h m c n limit inherited narrowed middle)
              (fun result after => post_checked _ (fun results final => .done (result::results) final) _ _
                (tails g s r e p h m c n limit inherited rest after)))
          simpa only [rows,SourceCurrentAllocatedPartialWorker.rows] using
            widen result (by simp only [budget]; omega)
    have bodyAt : BodyAt (width := width) fuel := by
      intro g s r e p h m c n limit request before
      rcases request with ⟨inherited,value⟩
      cases value with
      | empty | union | reference =>
        simp only [nodeBody,SourceCurrentAllocatedPartialWorker.nodeBody]
        exact widen (pure_checked _) (by omega)
      | mu entry body depth ordinary =>
        cases observed : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap with
        | done result heap =>
          simp only [nodeBody,SourceCurrentAllocatedPartialWorker.nodeBody,observed]
          exact widen (pure_checked _) (by omega)
        | pending reason heap =>
          simp only [nodeBody,SourceCurrentAllocatedPartialWorker.nodeBody,observed]
          exact widen (pure_checked _) (by omega)
      | node entry original depth free =>
        cases fuel with
        | zero =>
          simp only [nodeBody,SourceCurrentAllocatedPartialWorker.nodeBody]
          exact widen (pure_checked _) (by omega)
        | succ fuel =>
          have first := (ih fuel (Nat.lt_succ_self _)).2.2.2.2.1 g s r e p h m c n limit inherited original before
          have result := post_checked _ (fun results after =>
            let rebuilt := SourceCurrentAllocatedRawRebuild.modify (.node entry original depth free) original results after.checked
            .done rebuilt.1 (advance after rebuilt.2 after.fourth after.merge)) _ _ first
          simpa only [nodeBody,SourceCurrentAllocatedPartialWorker.nodeBody] using
            widen result (by simp only [budget]; omega)
    have nodeAt : NodeAt (width := width) fuel := by
      intro g s r e p h m c n limit request before
      rcases started : beginNode request before with ⟨handle,action,running⟩
      cases action with
      | ready value | busy | absent =>
        simp only [nodeCall, SourceCurrentAllocatedPartialWorker.nodeCall, started]
        exact widen (pure_checked _) (by omega)
      | evaluate original =>
        simpa only [nodeCall,SourceCurrentAllocatedPartialWorker.nodeCall,started] using
          post_checked _ (fun result after => .done result (finishNode handle result after)) _ _
            (bodyAt g s r e p h m c n limit original running)
    exact ⟨nodeAt,bodyAt,edgeAt,edgeBodyAt,rowsAt,descendantsAt,childrenAt,walkAt⟩

/-- Replay a literal node call and retain only entered Parent sites. -/
noncomputable def node (fuel g s r e p h m c n limit : Nat) (request : NodeRequest)
    (before : Caller width) : Execution Node width := nodeCall fuel g s r e p h m c n limit request before

/-- Replay a literal edge call, including the stored winner and ready-hit branch. -/
noncomputable def edge (fuel g s r e p h m c n limit : Nat) (request : EdgeRequest)
    (before : Caller width) : Execution Edge width := edgeCall fuel g s r e p h m c n limit request before

/-- Every node outcome has its exact ordered Parent entries and a fuel-only count bound. -/
theorem node_budget (fuel g s r e p h m c n limit : Nat) (request : NodeRequest) (before : Caller width) :
    (node fuel g s r e p h m c n limit request before).outcome =
      SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n limit request before ∧
    (node fuel g s r e p h m c n limit request before).calls.length ≤ budget fuel :=
  (all_checked fuel).1 g s r e p h m c n limit request before

/-- Every edge outcome retains its exact Parent entry or skips the body on a ready hit. -/
theorem edge_budget (fuel g s r e p h m c n limit : Nat) (request : EdgeRequest) (before : Caller width) :
    (edge fuel g s r e p h m c n limit request before).outcome =
      SourceCurrentAllocatedPartialWorker.edgeCall fuel g s r e p h m c n limit request before ∧
    (edge fuel g s r e p h m c n limit request before).calls.length ≤ budget fuel :=
  (all_checked fuel).2.2.1 g s r e p h m c n limit request before

end MicroCFTA.SourceCurrentOuterCallBudget
