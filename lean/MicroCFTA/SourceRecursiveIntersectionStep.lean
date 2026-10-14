import MicroCFTA.SourceRecursiveIntersectionSchedule

/-!
# The semantic step selected by physical recursive control

Each physical branch selects the corresponding next computation of the
proved recursive schedule. The branch retains domain extension, ordered
union requests, free lookup errors, and recursive cutoff names. Physical
constructor execution and memo publication remain separate obligations.
-/
namespace MicroCFTA.SourceRecursiveIntersectionStep
open Binding BinderLanguage
open InternedConstructorTemplates IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionSchedule
open IntersectSchedule (Input View Error)

/-- Read the exact next schedule computation, or reject an incompatible branch and payload. -/
def action [DecidableEq Symbol] (view : View Symbol) (fuel : Nat) (domain : IntersectSchedule.Domain)
    (left right : Input) : Branch → Option (Except Error (Shape (Payload Symbol)))
  | .empty => some (.ok .empty)
  | .reset => some (IntersectSchedule.run view fuel {} left right)
  | .self => some (.ok (view.copy left))
  | .swap => some (IntersectSchedule.run view fuel domain right left)
  | .repeated key => some (.ok (.ref (IntersectSchedule.pairName key)))
  | .bothMu => match left, right with
    | .mu first, .mu second =>
        some ((IntersectSchedule.run view fuel
          (IntersectSchedule.extend domain [(first, left), (second, right)] (IntersectSchedule.pair left right))
          (view.body first) (view.body second)).map (IntersectSchedule.maybeMu (IntersectSchedule.pair left right)))
    | _, _ => none
  | .leftMu => match left with
    | .mu first =>
        some ((IntersectSchedule.run view fuel
          (IntersectSchedule.extend domain [(first, left)] (IntersectSchedule.pair left right))
          (view.body first) right).map (IntersectSchedule.maybeMu (IntersectSchedule.pair left right)))
    | _ => none
  | .rightMu => match right with
    | .mu second =>
        some ((IntersectSchedule.run view fuel
          (IntersectSchedule.extend domain [(second, right)] (IntersectSchedule.pair left right))
          left (view.body second)).map (IntersectSchedule.maybeMu (IntersectSchedule.pair left right)))
    | _ => none
  | .leftUnion => match left with
    | .union first => some ((IntersectSchedule.walk (fun member => IntersectSchedule.run view fuel domain member right)
        (view.members first)).map Shape.alternatives)
    | _ => none
  | .rightUnion => match right with
    | .union second => some ((IntersectSchedule.walk (fun member => IntersectSchedule.run view fuel domain left member)
        (view.members second)).map Shape.alternatives)
    | _ => none
  | .leftReference => match left with
    | .ref name => some (match IntersectSchedule.lookup domain name with
        | none => .error (.missingBinder name)
        | some binder => IntersectSchedule.run view fuel domain binder right)
    | _ => none
  | .rightReference => match right with
    | .ref name => some (match IntersectSchedule.lookup domain name with
        | none => .error (.missingBinder name)
        | some binder => IntersectSchedule.run view fuel domain left binder)
    | _ => none
  | .ordinary => match left, right with
    | .node first, .node second =>
        some ((IntersectSchedule.walk (fun rows => IntersectSchedule.edge view fuel domain rows.1 rows.2)
          (IntersectSchedule.joined (view.rows first) (view.rows second))).map Shape.alternatives)
    | _, _ => none
  | .unsupported => none

/-- Every complete-input decision selects exactly the next step of the existing semantic executor. -/
theorem run_selected [DecidableEq Symbol] (view : View Symbol) (fuel : Nat) (domain : IntersectSchedule.Domain)
    (left right : Input) :
    action view fuel domain left right
        (inputDecision domain (IntersectSchedule.closed view left) (IntersectSchedule.closed view right) left right) =
      some (IntersectSchedule.run view (fuel + 1) domain left right) := by
  unfold inputDecision
  rw [IntersectSchedule.run.eq_def]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  by_cases empty : left = .empty ∨ right = .empty
  · simp only [empty, ite_true, action]
  · simp only [empty, ite_false]
    by_cases reset : (IntersectSchedule.closed view left = true ∧ IntersectSchedule.closed view right = true) ∧
        (!domain.free.isEmpty) = true
    · simp only [reset, true_and, ite_true, action]
    · simp only [reset, ite_false]
      by_cases same : left = right ∧ IntersectSchedule.closed view left = true
      · obtain ⟨rfl, closed⟩ := same
        simp [closed, action]
      · simp only [same, ite_false]
        by_cases swap : IntersectSchedule.greater left right = true
        · simp only [swap, ite_true, action]
        · simp only [swap, Bool.false_eq_true, ite_false]
          by_cases seen : IntersectSchedule.pair left right ∈ domain.seen
          · simp only [seen, ite_true, action]
          · simp only [seen, ite_false]
            cases left <;> cases right <;>
              simp_all [referencePayload, IntersectionFlatMemoKey.source, action] <;> rfl

/-- Actual physical control selects the same semantic computation, using the actual cached closedness fields. -/
theorem physical_step [DecidableEq Symbol] (view : View Symbol) (fuel : Nat) (source : DomainKey)
    (left right : Value Symbol Guard) (first second : Input)
    (leftInput : IntersectionFlatMemoKey.input left.referenceOf = some first)
    (rightInput : IntersectionFlatMemoKey.input right.referenceOf = some second)
    (leftClosed : IntersectSchedule.closed view first = left.free.isEmpty)
    (rightClosed : IntersectSchedule.closed view second = right.free.isEmpty) :
    action view fuel (domain source) first second (decision source left right) =
      some (IntersectSchedule.run view (fuel + 1) (domain source) first second) := by
  rw [decision_encoded source left right first second leftInput rightInput, ← leftClosed, ← rightClosed]
  exact run_selected view fuel (domain source) first second

end MicroCFTA.SourceRecursiveIntersectionStep
