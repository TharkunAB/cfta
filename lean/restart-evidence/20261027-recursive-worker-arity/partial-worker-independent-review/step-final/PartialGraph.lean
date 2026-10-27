import MicroCFTA.SourceCurrentAllocatedPartialState
import MicroCFTA.SourceCurrentAllocatedInheritedPrefix
import MicroCFTA.SourceCurrentAllocatedRawRebuild
import MicroCFTA.SourceCurrentAllocatedParentEdge
import MicroCFTA.SourceEqualityMuReconstruction

/-!
# Current recursive requests with separate node and edge result thunks

Each request publishes and demands its own result cell before its body.
The body uses the current checked parent reduction. Inherited combination
occurs once before actual indexed descent and recursive node requests.
Busy and absent observations have no successful graph constructor. The
graph describes completed serial calls, not general caller termination,
host forcing, or concurrent publication.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialGraph
open Cache Language InternedConstructorTemplates
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "NodeReq" => SourceCurrentAllocatedPartialState.NodeRequest
local notation "EdgeReq" => SourceCurrentAllocatedPartialState.EdgeRequest
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "advanceCaller" => SourceCurrentAllocatedPartialState.advance
local notation "beginNode" => SourceCurrentAllocatedPartialState.beginNode
local notation "beginEdge" => SourceCurrentAllocatedPartialState.beginEdge
local notation "finishNode" => SourceCurrentAllocatedPartialState.finishNode
local notation "finishEdge" => SourceCurrentAllocatedPartialState.finishEdge
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- An indexed descent retains every other caller table at its literal operation return. -/
def descend (before : Caller width) (combined : EqValue) (index : Nat) : EqValue × Caller width :=
  let actual := SourceEqualityConstraintMemoAllocation.descend combined index before.checked.operations
  (actual.1, advanceCaller before
    (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨before.checked.native.machine.heap, actual.2⟩)
    before.fourth before.merge)

/-- The single inherited prefix uses the actual returned edge field. -/
noncomputable def prefixState (before : Caller width) (edge : EdgeValue Symbol Guard) (inherited : EqValue) : Caller width :=
  advanceCaller before (SourceCurrentAllocatedInheritedPrefix.state before.checked edge.entry.key.constraint inherited)
    before.fourth before.merge

mutual
/-- The outer result thunk retains the actual first published node request. -/
inductive NodeCall (budget : Nat) : NodeReq → Caller width → Value Symbol Guard → Caller width → Prop where
  | hit (started : beginNode request before = (handle, (.ready result, running))) :
      NodeCall budget request before result running
  | evaluate (started : beginNode request before = (handle, (.evaluate original, running)))
      (body : NodeBody budget original running result middle) :
      NodeCall budget request before result (finishNode handle result middle)

/-- Source node bodies retain empty, union, binder reconstruction, and ordered ordinary rows. -/
inductive NodeBody (budget : Nat) : NodeReq → Caller width → Value Symbol Guard → Caller width → Prop where
  | empty : NodeBody budget ⟨inherited, .empty⟩ before .empty before
  | union : NodeBody budget ⟨inherited, .union entry members depth free⟩ before (.union entry members depth free) before
  | binder (actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.checked.native.machine.heap = .done result heap) :
      NodeBody budget ⟨inherited, .mu entry body depth ordinary⟩ before result
        (advanceCaller before
          (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap, before.checked.operations⟩)
          before.fourth before.merge)
  | ordinary (rows : Rows budget inherited edges before results middle) :
      NodeBody budget ⟨inherited, .node entry edges depth free⟩ before
        (SourceCurrentAllocatedRawRebuild.modify (.node entry edges depth free) edges results middle.checked).1
        (advanceCaller middle
          (SourceCurrentAllocatedRawRebuild.modify (.node entry edges depth free) edges results middle.checked).2
          middle.fourth middle.merge)

/-- The edge result table is separate and retains its own published original edge. -/
inductive EdgeCall (budget : Nat) : EdgeReq → Caller width → EdgeValue Symbol Guard → Caller width → Prop where
  | hit (started : beginEdge request before = (handle, (.ready result, running))) :
      EdgeCall budget request before result running
  | evaluate (started : beginEdge request before = (handle, (.evaluate original, running)))
      (body : EdgeBody budget original running result middle) :
      EdgeCall budget request before result (finishEdge handle result middle)

/-- The current parent body loads its field only after raw contradiction is excluded. -/
inductive EdgeBody (budget : Nat) : EdgeReq → Caller width → EdgeValue Symbol Guard → Caller width → Prop where
  | parent (field : SourceEqualityMkEdgeAllocation.contradictory edge.entry.key.constraint = false →
        SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint before.checked.operations.constraints = .ok (some loaded))
      (actual : SourceCurrentAllocatedParentEdge.Edge budget edge.entry.key.symbol edge.entry.key.constraint loaded inherited
        edge.children before.checked before.fourth before.merge result checked fourth merge) :
      EdgeBody budget ⟨inherited, edge⟩ before result (advanceCaller before checked fourth merge)

/-- Each ordered row runs its edge request, returned-edge descendants, and then its tail. -/
inductive Rows (budget : Nat) :
    EqValue → List (EdgeValue Symbol Guard) → Caller width → List (EdgeValue Symbol Guard) → Caller width → Prop where
  | nil : Rows budget inherited [] before [] before
  | cons (edge : EdgeCall budget ⟨inherited, original⟩ before narrowed middle)
      (children : Descendants budget inherited narrowed middle result afterChildren)
      (rest : Rows budget inherited originals afterChildren results after) :
      Rows budget inherited (original :: originals) before (result :: results) after

/-- Inherited combination occurs once, then same-arity rebuilding retains the returned raw field. -/
inductive Descendants (budget : Nat) :
    EqValue → EdgeValue Symbol Guard → Caller width → EdgeValue Symbol Guard → Caller width → Prop where
  | run (combined : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited before.checked.operations).1 = .ok (some payload))
      (children : Children budget payload edge.children (prefixState before edge inherited) results middle) :
      Descendants budget inherited edge before
        (SourceCurrentAllocatedRawRebuild.edge edge results middle.checked).1
        (advanceCaller middle (SourceCurrentAllocatedRawRebuild.edge edge results middle.checked).2 middle.fourth middle.merge)

/-- Contradiction skips every child request; a live payload starts the indexed walk. -/
inductive Children (budget : Nat) :
    EqValue → List (Value Symbol Guard) → Caller width → List (Value Symbol Guard) → Caller width → Prop where
  | contradiction : Children budget .contradiction values before (EqualityLeafProjectionRuntimeEmpty.erase values) before
  | live (actual : Walk budget (.live identity records) 0 values before results after) :
      Children budget (.live identity records) values before results after

/-- Each actual descended value is the next recursive request's stored inherited argument. -/
inductive Walk (budget : Nat) :
    EqValue → Nat → List (Value Symbol Guard) → Caller width → List (Value Symbol Guard) → Caller width → Prop where
  | nil : Walk budget combined index [] before [] before
  | cons (head : NodeCall budget ⟨(descend before combined index).1, value⟩
        (descend before combined index).2 result middle)
      (rest : Walk budget combined (index + 1) values middle results after) :
      Walk budget combined index (value :: values) before (result :: results) after
end

/-- A finite indexed graph replaces one output value per original child slot. -/
theorem Walk.length {budget : Nat} {combined : EqValue} {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : Caller width}
    (actual : Walk budget combined index values before results after) : results.length = values.length := by
  apply Walk.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ values _ results _ _ => results.length = values.length) (t := actual)
  all_goals intros <;> simp_all

/-- Both actual child branches retain the original number of slots. -/
theorem Children.length {budget : Nat} {combined : EqValue}
    {values results : List (Value Symbol Guard)} {before after : Caller width}
    (actual : Children budget combined values before results after) : results.length = values.length := by
  cases actual with
  | contradiction => exact List.length_map _
  | live trace => exact trace.length

/-- Ordinary row traversal returns exactly one row per original source row. -/
theorem Rows.length {budget : Nat} {inherited : EqValue}
    {values results : List (EdgeValue Symbol Guard)} {before after : Caller width}
    (actual : Rows budget inherited values before results after) : results.length = values.length := by
  apply Rows.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ values _ results _ _ => results.length = values.length)
    (motive_6 := fun _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ _ => True) (t := actual)
  all_goals intros <;> simp_all

/-- An observed running node result cell cannot be used as a successful completed call. -/
theorem NodeCall.not_busy {budget : Nat} {request : NodeReq} {before after running : Caller width}
    {result : Value Symbol Guard} {handle : Nat} (actual : NodeCall budget request before result after)
    (blocked : beginNode request before = (handle, (.busy, running))) : False := by
  cases actual with
  | hit started => rw [started] at blocked; cases blocked
  | evaluate started _ => rw [started] at blocked; cases blocked

/-- An observed running edge result cell cannot be used as a successful completed call. -/
theorem EdgeCall.not_busy {budget : Nat} {request : EdgeReq} {before after running : Caller width}
    {result : EdgeValue Symbol Guard} {handle : Nat} (actual : EdgeCall budget request before result after)
    (blocked : beginEdge request before = (handle, (.busy, running))) : False := by
  cases actual with
  | hit started => rw [started] at blocked; cases blocked
  | evaluate started _ => rw [started] at blocked; cases blocked

/-- A raw Rec input has no successful source body; the source reports its explicit error. -/
theorem NodeBody.reference_error {budget : Nat} {inherited : EqValue} {name : InternedBinderProtocol.Reference}
    {before after : Caller width} {result : Value Symbol Guard} :
    ¬ NodeBody budget ⟨inherited, .reference name⟩ before result after := by intro actual; cases actual

end MicroCFTA.SourceCurrentAllocatedPartialGraph
