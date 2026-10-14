import MicroCFTA.IntersectMuCalls
import MicroCFTA.SourceRecursiveIntersectionStep

/-!
# One exact semantic body action for all Mu branches

Actual Mu payload tags determine the common body request and extension.
The equation retains both original bindings and their source order.
-/
namespace MicroCFTA.IntersectSchedule
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionEnvironment
open SourceRecursiveIntersectionSchedule

/-- Every selected Mu payload has the same exact common semantic body action. -/
theorem mu_schedule_action [DecidableEq Symbol] (view : View Symbol) (fuel : Nat) (domain : Domain)
    (left right : Input) (branch : Branch)
    (selected : referencePayload (IntersectionFlatMemoKey.source left) (IntersectionFlatMemoKey.source right) = branch)
    (recursive : branch = .bothMu ∨ branch = .leftMu ∨ branch = .rightMu) :
    SourceRecursiveIntersectionStep.action view fuel domain left right branch =
      some ((run view fuel (extend domain ((muNames left ++ muNames right).map (fun name => (name, Input.mu name)))
        (pair left right)) (bodyInput view left) (bodyInput view right)).map (maybeMu (pair left right))) := by
  rcases recursive with rfl | rfl | rfl
  all_goals cases left <;> cases right <;>
    simp only [referencePayload, IntersectionFlatMemoKey.source, reduceCtorEq] at selected <;> try contradiction
  all_goals simp only [SourceRecursiveIntersectionStep.action, muNames, List.nil_append, List.append_nil,
    List.cons_append, List.map_cons, List.map_nil, bodyInput]

end MicroCFTA.IntersectSchedule
