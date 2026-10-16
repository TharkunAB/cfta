import MicroCFTA.SourceCurrentAllocatedParentWorker
import MicroCFTA.SourceCurrentAllocatedPartialGraph

/-!
# Literal mutual outer equality worker

The two result families publish and demand before body execution. Ready
hits need no outer recursion bound. Evaluation uses the stored original
request and finishes only its exact handle after success. Every incomplete
observation retains the reached full caller, including evaluating owners.
The outer bound limits ordinary rows and indexed child recursion. The nine
lower bounds and conjunction budget have separate roles. This definition
does not establish general constrained completion or host demand order.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialWorker
open Language InternedConstructorTemplates
open SourceCurrentAllocatedPartialState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

/-- Only recursive ordinary rows and indexed walks consume the outer bound. -/
inductive Limit where
  | nodeBody
  | rows
  | walk
  deriving DecidableEq, Repr

/-- Every incomplete outer observation retains its phase and full underlying diagnostic. -/
inductive Fault (width : Nat) : Type 1 where
  | exhausted (phase : Limit)
  | nodeMemo (handle : Nat) (observation : FlatMemoThunk.Observation NodeRequest Node)
  | edgeMemo (handle : Nat) (observation : FlatMemoThunk.Observation EdgeRequest Edge)
  | unexpectedReference (name : InternedBinderProtocol.Reference)
  | binder (observation : InternedNestedConstruction.Outcome Symbol Guard Node)
  | parent (observation : SourceCurrentAllocatedParentWorker.Fault width)
  | inherited (message : String)
  | missingInherited

/-- Every outer return retains both complete result tables and all lower-stage state. -/
inductive Outcome (Output : Type) (width : Nat) : Type 1 where
  | done (value : Output) (state : Caller width)
  | failed (fault : Fault width) (state : Caller width)

def Outcome.state : Outcome Output width → Caller width
  | .done _ state | .failed _ state => state

/-- A failed body retains its evaluating owner and never enters a finish continuation. -/
def Outcome.bind (first : Outcome A width) (next : A → Caller width → Outcome B width) : Outcome B width :=
  match first with
  | .done value state => next value state
  | .failed fault state => .failed fault state

variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
  [DecidableEq Node] {width : Nat}

mutual
/-- The node family demands its cell before inspecting the body recursion bound. -/
noncomputable def nodeCall (fuel g s r e p h m c n budget : Nat) (request : NodeRequest)
    (before : Caller width) : Outcome Node width :=
  let actual := beginNode request before
  match actual.2.1 with
  | .ready result => .done result actual.2.2
  | .evaluate original =>
      (nodeBody fuel g s r e p h m c n budget original actual.2.2).bind fun result after =>
        .done result (finishNode actual.1 result after)
  | .busy => .failed (.nodeMemo actual.1 .busy) actual.2.2
  | .absent => .failed (.nodeMemo actual.1 .absent) actual.2.2
termination_by (fuel, 3)

/-- Source terminal and binder branches run literally; ordinary rows consume one recursion step. -/
noncomputable def nodeBody (fuel g s r e p h m c n budget : Nat) (request : NodeRequest)
    (before : Caller width) : Outcome Node width :=
  match request.value with
  | .empty => .done .empty before
  | value@(.union ..) => .done value before
  | .reference name => .failed (.unexpectedReference name) before
  | .mu entry body depth ordinary =>
      match SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap with
      | .done result heap => .done result (advance before
          (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩)
          before.fourth before.merge)
      | observation@(.pending _ heap) => .failed (.binder observation) (advance before
          (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩)
          before.fourth before.merge)
  | value@(.node _ original _ _) =>
      match fuel with
      | 0 => .failed (.exhausted .nodeBody) before
      | next + 1 =>
          (rows next g s r e p h m c n budget request.inherited original before).bind fun results after =>
            let rebuilt := SourceCurrentAllocatedRawRebuild.modify value original results after.checked
            .done rebuilt.1 (advance after rebuilt.2 after.fourth after.merge)
termination_by (fuel, 2)

/-- The edge family evaluates its stored winner and completes only the selected handle. -/
noncomputable def edgeCall (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before : Caller width) : Outcome Edge width :=
  let actual := beginEdge request before
  match actual.2.1 with
  | .ready result => .done result actual.2.2
  | .evaluate original =>
      (edgeBody fuel g s r e p h m c n budget original actual.2.2).bind fun result after =>
        .done result (finishEdge actual.1 result after)
  | .busy => .failed (.edgeMemo actual.1 .busy) actual.2.2
  | .absent => .failed (.edgeMemo actual.1 .absent) actual.2.2

/-- A parent return advances checked state and warm memos without changing either outer result table. -/
noncomputable def edgeBody (_fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before : Caller width) : Outcome Edge width :=
  match SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited
      request.value.children before.checked before.fourth before.merge with
  | .done result checked fourth memo => .done result (advance before checked fourth memo)
  | .failed fault checked fourth memo => .failed (.parent fault) (advance before checked fourth memo)

/-- Each original row uses its returned parent edge for descendants before entering the suffix. -/
noncomputable def rows (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (originals : List Edge) (before : Caller width) : Outcome (List Edge) width :=
  match originals with
  | [] => .done [] before
  | original :: rest =>
      match fuel with
      | 0 => .failed (.exhausted .rows) before
      | next + 1 =>
          (edgeCall next g s r e p h m c n budget ⟨inherited, original⟩ before).bind fun narrowed middle =>
            (descendants next g s r e p h m c n budget inherited narrowed middle).bind fun result after =>
              (rows next g s r e p h m c n budget inherited rest after).bind fun results final =>
                .done (result :: results) final
termination_by (fuel, 2)

/-- The inherited prefix runs once and passes its actual operation return into indexed children. -/
noncomputable def descendants (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (edge : Edge) (before : Caller width) : Outcome Edge width :=
  let actual := SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations
  let middle := advance before
    (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨before.checked.native.machine.heap, actual.2⟩)
    before.fourth before.merge
  match actual.1 with
  | .error message => .failed (.inherited message) middle
  | .ok none => .failed .missingInherited middle
  | .ok (some combined) =>
      (children fuel g s r e p h m c n budget combined edge.children middle).bind fun results after =>
        let rebuilt := SourceCurrentAllocatedRawRebuild.edge edge results after.checked
        .done rebuilt.1 (advance after rebuilt.2 after.fourth after.merge)
termination_by (fuel, 2)

/-- Contradictory inherited constraints erase slots without invoking a child request. -/
noncomputable def children (fuel g s r e p h m c n budget : Nat) (combined : EqValue)
    (values : List Node) (before : Caller width) : Outcome (List Node) width :=
  match combined with
  | .contradiction => .done (EqualityLeafProjectionRuntimeEmpty.erase values) before
  | .live _ _ => walk fuel g s r e p h m c n budget combined 0 values before
termination_by (fuel, 1)

/-- Indexed child calls use each actual descent at the current operation state. -/
noncomputable def walk (fuel g s r e p h m c n budget : Nat) (combined : EqValue) (index : Nat)
    (values : List Node) (before : Caller width) : Outcome (List Node) width :=
  match values with
  | [] => .done [] before
  | value :: rest =>
      match fuel with
      | 0 => .failed (.exhausted .walk) before
      | next + 1 =>
          let actual := SourceCurrentAllocatedPartialGraph.descend before combined index
          (nodeCall next g s r e p h m c n budget ⟨actual.1, value⟩ actual.2).bind fun result middle =>
            (walk next g s r e p h m c n budget combined (index + 1) rest middle).bind fun results after =>
              .done (result :: results) after
termination_by (fuel, 0)
end

/-- A ready node cell skips every body and lower bound at its exact post-demand state. -/
theorem nodeCall_ready (fuel g s r e p h m c n budget : Nat) (request : NodeRequest)
    (before after : Caller width) (handle : Nat) (result : Node)
    (actual : beginNode request before = (handle, .ready result, after)) :
    nodeCall fuel g s r e p h m c n budget request before = .done result after := by
  simp only [nodeCall, actual]

/-- A ready edge cell does not run the parent worker or finish a different owner. -/
theorem edgeCall_ready (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before after : Caller width) (handle : Nat) (result : Edge)
    (actual : beginEdge request before = (handle, .ready result, after)) :
    edgeCall fuel g s r e p h m c n budget request before = .done result after := by
  simp only [edgeCall, actual]

/-- A busy node remains incomplete at its actual published caller state. -/
theorem nodeCall_busy (fuel g s r e p h m c n budget : Nat) (request : NodeRequest)
    (before after : Caller width) (handle : Nat)
    (actual : beginNode request before = (handle, .busy, after)) :
    nodeCall fuel g s r e p h m c n budget request before = .failed (.nodeMemo handle .busy) after := by
  simp only [nodeCall, actual]

/-- An absent node observation remains distinct from busy and successful return. -/
theorem nodeCall_absent (fuel g s r e p h m c n budget : Nat) (request : NodeRequest)
    (before after : Caller width) (handle : Nat)
    (actual : beginNode request before = (handle, .absent, after)) :
    nodeCall fuel g s r e p h m c n budget request before = .failed (.nodeMemo handle .absent) after := by
  simp only [nodeCall, actual]

/-- A busy edge retains its own complete result-family state. -/
theorem edgeCall_busy (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before after : Caller width) (handle : Nat)
    (actual : beginEdge request before = (handle, .busy, after)) :
    edgeCall fuel g s r e p h m c n budget request before = .failed (.edgeMemo handle .busy) after := by
  simp only [edgeCall, actual]

/-- An absent edge is an incomplete observation rather than an empty-language result. -/
theorem edgeCall_absent (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before after : Caller width) (handle : Nat)
    (actual : beginEdge request before = (handle, .absent, after)) :
    edgeCall fuel g s r e p h m c n budget request before = .failed (.edgeMemo handle .absent) after := by
  simp only [edgeCall, actual]

/-- A failed stored node body returns without completing its evaluating owner. -/
theorem nodeCall_body_failed (fuel g s r e p h m c n budget : Nat) (request original : NodeRequest)
    (before running after : Caller width) (handle : Nat) (fault : Fault width)
    (started : beginNode request before = (handle, .evaluate original, running))
    (actual : nodeBody fuel g s r e p h m c n budget original running = .failed fault after) :
    nodeCall fuel g s r e p h m c n budget request before = .failed fault after := by
  simp only [nodeCall, started, actual, Outcome.bind]

/-- A failed stored edge body retains its reached state and never calls finish. -/
theorem edgeCall_body_failed (fuel g s r e p h m c n budget : Nat) (request original : EdgeRequest)
    (before running after : Caller width) (handle : Nat) (fault : Fault width)
    (started : beginEdge request before = (handle, .evaluate original, running))
    (actual : edgeBody fuel g s r e p h m c n budget original running = .failed fault after) :
    edgeCall fuel g s r e p h m c n budget request before = .failed fault after := by
  simp only [edgeCall, started, actual, Outcome.bind]

/-- Node evaluation executes the stored original and finishes that same selected handle. -/
theorem nodeCall_body_done (fuel g s r e p h m c n budget : Nat) (request original : NodeRequest)
    (before running after : Caller width) (handle : Nat) (result : Node)
    (started : beginNode request before = (handle, .evaluate original, running))
    (actual : nodeBody fuel g s r e p h m c n budget original running = .done result after) :
    nodeCall fuel g s r e p h m c n budget request before = .done result (finishNode handle result after) := by
  simp only [nodeCall, started, actual, Outcome.bind]

/-- Edge evaluation installs only the successful stored owner's result at its selected handle. -/
theorem edgeCall_body_done (fuel g s r e p h m c n budget : Nat) (request original : EdgeRequest)
    (before running after : Caller width) (handle : Nat) (result : Edge)
    (started : beginEdge request before = (handle, .evaluate original, running))
    (actual : edgeBody fuel g s r e p h m c n budget original running = .done result after) :
    edgeCall fuel g s r e p h m c n budget request before = .done result (finishEdge handle result after) := by
  simp only [edgeCall, started, actual, Outcome.bind]

end MicroCFTA.SourceCurrentAllocatedPartialWorker
