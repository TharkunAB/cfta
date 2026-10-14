import MicroCFTA.IntersectSchedule

/-!
# Ordered semantic results from corresponding actual requests

Each request occurrence supplies one semantic result and a relation to
its actual result. The semantic walk retains that order and all duplicates.
-/
namespace MicroCFTA.IntersectSchedule
open Language

/-- Translating request payloads retains the complete ordered semantic traversal. -/
theorem walk_map (action : B → Except Error C) (convert : A → B) (requests : List A) :
    walk action (requests.map convert) = walk (fun request => action (convert request)) requests := by
  induction requests with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, walk, ih]

/-- Pointwise successful semantic requests give one ordered walk with corresponding results. -/
theorem walk_related (action : A → Except Error B) (relation : C → B → Prop)
    (requests : List A) (values : List C)
    (related : All₂ (fun request value => ∃ shape, action request = .ok shape ∧ relation value shape) requests values) :
    ∃ shapes, walk action requests = .ok shapes ∧ All₂ relation values shapes := by
  induction related with
  | nil => exact ⟨[], rfl, .nil⟩
  | @cons request value requests values head tail ih =>
      obtain ⟨shape, completed, same⟩ := head
      obtain ⟨shapes, walked, paired⟩ := ih
      exact ⟨shape :: shapes, by simp only [walk, completed, walked, Bind.bind, Except.bind, Pure.pure, Except.pure],
        .cons same paired⟩

end MicroCFTA.IntersectSchedule
