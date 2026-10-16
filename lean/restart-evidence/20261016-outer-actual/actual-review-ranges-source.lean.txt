import MicroCFTA.SourceCurrentAllocatedPartialWorker
import MicroCFTA.SourceCurrentAllocatedParentWorkerActual

/-!
# Machine range checks on actual outer worker prefixes

Each predicate follows the literal worker branch at the supplied bounds.
Only successful prefixes inspect a continuation at their exact return.
Incomplete observations impose no continuation check. These predicates
do not assert execution completion or a future physical or semantic law.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges
open Language InternedConstructorTemplates SourceCurrentAllocatedPartialState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value

/-- Check a continuation only at the observed successful value and complete caller state. -/
def After (observed : SourceCurrentAllocatedPartialWorker.Outcome A width)
    (next : A → Caller width → Prop) : Prop :=
  match observed with
  | .done value after => next value after
  | .failed _ _ => True

/-- A supplied success exposes its actual continuation check. -/
theorem after_of_done {observed : SourceCurrentAllocatedPartialWorker.Outcome A width}
    {next : A → Caller width → Prop} {value : A} {after : Caller width}
    (ranges : After observed next) (done : observed = .done value after) : next value after := by
  simpa only [done, After] using ranges

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

mutual
/-- Node hits and incomplete demands require no body checks; evaluation uses its stored owner. -/
noncomputable def nodeCall (fuel g s r e p h m c n budget : Nat) (request : NodeRequest)
    (before : Caller width) : Prop :=
  let actual := beginNode request before
  match actual.2.1 with
  | .evaluate original => nodeBody fuel g s r e p h m c n budget original actual.2.2
  | .ready _ | .busy | .absent => True
termination_by (fuel, 3)

/-- Only a reached ordinary node with remaining outer fuel checks its row traversal. -/
noncomputable def nodeBody (fuel g s r e p h m c n budget : Nat) (request : NodeRequest)
    (before : Caller width) : Prop :=
  match request.value with
  | .node _ original _ _ => match fuel with
      | 0 => True
      | next + 1 => rows next g s r e p h m c n budget request.inherited original before
  | .empty | .union .. | .reference _ | .mu .. => True
termination_by (fuel, 2)

/-- Edge evaluation checks the stored owner at the actual post-demand caller state. -/
noncomputable def edgeCall (fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before : Caller width) : Prop :=
  let actual := beginEdge request before
  match actual.2.1 with
  | .evaluate original => edgeBody fuel g s r e p h m c n budget original actual.2.2
  | .ready _ | .busy | .absent => True

/-- A completed parent demands its live machine checks; a failed parent adds no condition. -/
noncomputable def edgeBody (_fuel g s r e p h m c n budget : Nat) (request : EdgeRequest)
    (before : Caller width) : Prop :=
  match SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited
      request.value.children before.checked before.fourth before.merge with
  | .done _ _ _ _ => SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before
  | .failed _ _ _ _ => True

/-- Row checks follow edge, returned-edge descendants, and suffix only at actual successful returns. -/
noncomputable def rows (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (originals : List Edge) (before : Caller width) : Prop :=
  match originals with
  | [] => True
  | original :: rest => match fuel with
      | 0 => True
      | next + 1 =>
          edgeCall next g s r e p h m c n budget ⟨inherited, original⟩ before ∧
          After (SourceCurrentAllocatedPartialWorker.edgeCall next g s r e p h m c n budget ⟨inherited, original⟩ before)
            (fun narrowed middle =>
              descendants next g s r e p h m c n budget inherited narrowed middle ∧
              After (SourceCurrentAllocatedPartialWorker.descendants next g s r e p h m c n budget inherited narrowed middle)
                (fun _ after => rows next g s r e p h m c n budget inherited rest after))
termination_by (fuel, 2)

/-- A successful inherited prefix checks children at its literal returned operation state. -/
noncomputable def descendants (fuel g s r e p h m c n budget : Nat) (inherited : EqValue)
    (edge : Edge) (before : Caller width) : Prop :=
  let actual := SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations
  match actual.1 with
  | .error _ | .ok none => True
  | .ok (some combined) => children fuel g s r e p h m c n budget combined edge.children
      (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited)
termination_by (fuel, 2)

/-- Contradiction skips all child checks; a live payload checks the actual indexed walk. -/
noncomputable def children (fuel g s r e p h m c n budget : Nat) (combined : EqValue)
    (values : List Node) (before : Caller width) : Prop :=
  match combined with
  | .contradiction => True
  | .live _ _ => walk fuel g s r e p h m c n budget combined 0 values before
termination_by (fuel, 1)

/-- Each reached child check uses its actual indexed descent and successful caller return. -/
noncomputable def walk (fuel g s r e p h m c n budget : Nat) (combined : EqValue) (index : Nat)
    (values : List Node) (before : Caller width) : Prop :=
  match values with
  | [] => True
  | value :: rest => match fuel with
      | 0 => True
      | next + 1 =>
          let actual := SourceCurrentAllocatedPartialGraph.descend before combined index
          nodeCall next g s r e p h m c n budget ⟨actual.1, value⟩ actual.2 ∧
          After (SourceCurrentAllocatedPartialWorker.nodeCall next g s r e p h m c n budget ⟨actual.1, value⟩ actual.2)
            (fun _ middle => walk next g s r e p h m c n budget combined (index + 1) rest middle)
termination_by (fuel, 0)
end

/-- Successful literal edge-body execution exposes only its actual parent's reached checks. -/
theorem edgeBody_of_done {fuel g s r e p h m c n budget : Nat} {request : EdgeRequest}
    {before after : Caller width} {result : Edge}
    (ranges : edgeBody fuel g s r e p h m c n budget request before)
    (done : SourceCurrentAllocatedPartialWorker.edgeBody fuel g s r e p h m c n budget request before = .done result after) :
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before := by
  cases observed : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      request.value.entry.key.symbol request.value.entry.key.constraint request.inherited
      request.value.children before.checked before.fourth before.merge with
  | done => simpa only [edgeBody, observed] using ranges
  | failed =>
      simp only [SourceCurrentAllocatedPartialWorker.edgeBody, observed] at done
      cases done

/-- Node evaluation exposes the exact stored owner and post-demand body checks. -/
theorem nodeCall_of_evaluate {fuel g s r e p h m c n budget : Nat} {request original : NodeRequest}
    {before running : Caller width} {handle : Nat}
    (ranges : nodeCall fuel g s r e p h m c n budget request before)
    (started : beginNode request before = (handle, .evaluate original, running)) :
    nodeBody fuel g s r e p h m c n budget original running := by
  simpa only [nodeCall, started] using ranges

/-- Edge evaluation exposes the exact stored owner and post-demand parent checks. -/
theorem edgeCall_of_evaluate {fuel g s r e p h m c n budget : Nat} {request original : EdgeRequest}
    {before running : Caller width} {handle : Nat}
    (ranges : edgeCall fuel g s r e p h m c n budget request before)
    (started : beginEdge request before = (handle, .evaluate original, running)) :
    edgeBody fuel g s r e p h m c n budget original running := by
  simpa only [edgeCall, started] using ranges

end MicroCFTA.SourceCurrentAllocatedPartialWorkerRanges
