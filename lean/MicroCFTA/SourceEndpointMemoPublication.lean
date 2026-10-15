import MicroCFTA.SourceEndpointMemoCorrect
import MicroCFTA.SourceEndpointMemoAncestry

/-!
# Active descendant queries before completed memo storage

A miss makes its original input active before the helper body runs. A
recursive query of an active physical key blocks. Completed keys bypass the
body. The active stack represents unfinished calls of this sequential
traversal. The constraint-predicate memo call is still a completed operation.
Native thunk insertion, concurrency, and typed cache selection remain separate.
-/
namespace MicroCFTA.SourceEndpointMemoPublication
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEndpointMemo
open SourceEndpointMemoAncestry
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula

/-- A blocked query retains the exact completed memos reached before its demand. -/
inductive Outcome where
  | done (answer : Bool) (memos : Memos)
  | blocked (key : InternedBinderProtocol.NodeRef) (memos : Memos)

/-- Test the exact tagged physical key of each active original query. -/
def busy (value : Value Symbol Guard) (active : List (Value Symbol Guard)) : Bool :=
  active.any (fun ancestor => ancestor.referenceOf == value.referenceOf)

/-- Current inputs are smaller than every available active ancestor. -/
def Active (heap : State Symbol Guard) (value : Value Symbol Guard)
    (active : List (Value Symbol Guard)) : Prop :=
  ∀ ancestor ∈ active, Available heap ancestor ∧ sizeOf value < sizeOf ancestor

/-- A coherent smaller resident input cannot have an active ancestor's physical key. -/
theorem not_busy (value : Value Symbol Guard) (active : List (Value Symbol Guard))
    (heap : State Symbol Guard) (coherent : Coherent heap) (available : Available heap value)
    (ordered : Active heap value active) : busy value active = false := by
  apply List.any_eq_false.mpr
  intro ancestor member
  obtain ⟨resident, smaller⟩ := ordered ancestor member
  rw [beq_iff_eq]
  intro same
  have equal := InternedFreshProbeKeys.resident_reference_injective heap coherent ancestor value
    resident.resident available.resident same
  subst ancestor
  exact Nat.lt_irrefl _ smaller

/-- Every possible recursive helper call stays below the current published input and all older inputs. -/
theorem active_child (heap : State Symbol Guard) (value child : Value Symbol Guard)
    (available : Available heap value) (active : List (Value Symbol Guard))
    (ordered : Active heap value active) (step : Step child value) : Active heap child (value :: active) := by
  intro ancestor member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨available, step.smaller⟩
  · obtain ⟨resident, smaller⟩ := ordered ancestor member
    exact ⟨resident, Nat.lt_trans step.smaller smaller⟩

mutual
/-- Publish the active miss before child demand and store the completed root after its body. -/
noncomputable def run (value : Value Symbol Guard) (active : List (Value Symbol Guard)) (memos : Memos) : Outcome :=
  match memos.descendants value.referenceOf with
  | some (_, answer) => .done answer memos
  | none =>
      if busy value active then .blocked value.referenceOf memos else
        let result : Outcome :=
          if value.depth == 0 then .done false memos else
            match value with
            | .mu .. =>
                let predicate := SourceUnconstrainedMemo.run value memos.predicate
                .done (!predicate.1) {memos with predicate := predicate.2}
            | .union _ members _ _ => many members (value :: active) memos
            | .node _ edges _ _ => rows edges (value :: active) memos
            | _ => .done false memos
        match result with
        | .blocked key after => .blocked key after
        | .done answer after => .done answer {after with descendants := save after.descendants value answer}
termination_by sizeOf value

/-- A blocked child retains its actual memo state. False children continue in original order. -/
noncomputable def many (values : List (Value Symbol Guard)) (active : List (Value Symbol Guard)) (memos : Memos) : Outcome :=
  match values with
  | [] => .done false memos
  | first :: rest => match run first active memos with
      | .blocked key after => .blocked key after
      | .done true after => .done true after
      | .done false after => many rest active after
termination_by sizeOf values

/-- Ordered rows share the active ancestor stack and both completed memo families. -/
noncomputable def rows (edges : List (EdgeValue Symbol Guard)) (active : List (Value Symbol Guard)) (memos : Memos) : Outcome :=
  match edges with
  | [] => .done false memos
  | .mk _ children :: rest => match many children active memos with
      | .blocked key after => .blocked key after
      | .done true after => .done true after
      | .done false after => rows rest active after
termination_by sizeOf edges
end

end MicroCFTA.SourceEndpointMemoPublication
