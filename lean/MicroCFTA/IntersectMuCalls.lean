import MicroCFTA.IntersectImmediateCalls
import MicroCFTA.SourceRecursiveIntersectionEnvironment

/-!
# Complete Mu child requests

All three Mu branches enter the same semantic domain construction for their
actual operands. Earlier guards cannot select a Mu branch. The selected
payload tags determine the original bodies and exact new bindings.
-/
namespace MicroCFTA.IntersectSchedule
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionSchedule SourceRecursiveIntersectionEnvironment

/-- A semantic Mu operand selects its original body; other operands remain literal. -/
def bodyInput (view : View Symbol) : Input → Input
  | .mu name => view.body name
  | input => input

/-- Read the common exact recursive request of all three semantic Mu branches. -/
def muChild (view : View Symbol) (domain : Domain) (left right : Input) : Call Symbol :=
  .node (extend domain ((muNames left ++ muNames right).map (fun name => (name, Input.mu name))) (pair left right))
    (bodyInput view left) (bodyInput view right)

/-- A selected Mu branch comes from the actual payload tags after all earlier source guards. -/
theorem mu_payload [DecidableEq Symbol] (view : View Symbol) (domain : Domain) (left right : Input) (branch : Branch)
    (selected : inputDecision domain (closed view left) (closed view right) left right = branch)
    (recursive : branch = .bothMu ∨ branch = .leftMu ∨ branch = .rightMu) :
    referencePayload (IntersectionFlatMemoKey.source left) (IntersectionFlatMemoKey.source right) = branch := by
  unfold inputDecision at selected
  split at selected
  · rcases recursive with rfl | rfl | rfl <;> cases selected
  · split at selected
    · rcases recursive with rfl | rfl | rfl <;> cases selected
    · split at selected
      · rcases recursive with rfl | rfl | rfl <;> cases selected
      · split at selected
        · rcases recursive with rfl | rfl | rfl <;> cases selected
        · split at selected
          · rcases recursive with rfl | rfl | rfl <;> cases selected
          · exact selected

/-- Actual complete payload tags select the common exact Mu child. -/
theorem mu_payload_child [DecidableEq Symbol] (view : View Symbol) (domain : Domain) (left right : Input) (branch : Branch)
    (selected : referencePayload (IntersectionFlatMemoKey.source left) (IntersectionFlatMemoKey.source right) = branch)
    (recursive : branch = .bothMu ∨ branch = .leftMu ∨ branch = .rightMu) :
    muChild view domain left right ∈ branchCalls view domain left right branch := by
  rcases recursive with rfl | rfl | rfl
  all_goals cases left <;> cases right <;>
    simp only [referencePayload, IntersectionFlatMemoKey.source, reduceCtorEq] at selected <;> try contradiction
  all_goals simp [muChild, muNames, bodyInput, branchCalls]

/-- Every actual selected Mu branch issues the common original body request. -/
theorem mu_child_member [DecidableEq Symbol] (view : View Symbol) (domain : Domain) (left right : Input) (branch : Branch)
    (selected : inputDecision domain (closed view left) (closed view right) left right = branch)
    (recursive : branch = .bothMu ∨ branch = .leftMu ∨ branch = .rightMu) :
    muChild view domain left right ∈ branchCalls view domain left right branch :=
  mu_payload_child view domain left right branch (mu_payload view domain left right branch selected recursive) recursive

end MicroCFTA.IntersectSchedule
