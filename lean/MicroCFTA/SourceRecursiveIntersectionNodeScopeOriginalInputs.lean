import MicroCFTA.SourceRecursiveIntersectionInputInventory
import MicroCFTA.SourceRecursiveIntersectionRequestScope

namespace MicroCFTA.SourceRecursiveIntersectionInputView

theorem nodeScope_originalInputs {Symbol Guard : Type}
    {source : MicroCFTA.InternedConstructorTemplates.State Symbol Guard} {request}
    (_facts : MicroCFTA.InternedNestedFacts.Facts source)
    (scope : MicroCFTA.SourceRecursiveIntersectionCode.NodeScope source request) :
    MicroCFTA.SourceRecursiveIntersectionInputView.OriginalInput source
      (MicroCFTA.SourceRecursiveIntersectionInputView.inputOf request.left) ∧
    MicroCFTA.SourceRecursiveIntersectionInputView.OriginalInput source
      (MicroCFTA.SourceRecursiveIntersectionInputView.inputOf request.right) := by
  have complete : ∀ (value : MicroCFTA.InternedConstructorTemplates.Value Symbol Guard),
      Original value → ∃ input : MicroCFTA.IntersectSchedule.Input,
        MicroCFTA.IntersectionFlatMemoKey.input
          (MicroCFTA.InternedConstructorTemplates.Value.referenceOf value) = some input := by
    intro value original
    refine @Original.rec Symbol Guard
      (fun value _ => ∃ input : MicroCFTA.IntersectSchedule.Input,
        MicroCFTA.IntersectionFlatMemoKey.input
          (MicroCFTA.InternedConstructorTemplates.Value.referenceOf value) = some input)
      ?_ ?_ ?_ ?_ ?_ value original
    · exact ⟨.empty, by rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_1,
        MicroCFTA.IntersectionFlatMemoKey.input.eq_1]⟩
    · intro name
      exact ⟨.ref name, by rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_2,
        MicroCFTA.IntersectionFlatMemoKey.input.eq_5]⟩
    · intro entry edges depth free children children_ih
      exact ⟨.node entry.identity, by rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_3,
        MicroCFTA.IntersectionFlatMemoKey.input.eq_2]⟩
    · intro entry members depth free children children_ih
      exact ⟨.union entry.identity, by rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_4,
        MicroCFTA.IntersectionFlatMemoKey.input.eq_4]⟩
    · intro entry body depth ordinary original original_ih
      exact ⟨.mu entry.identity, by rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_5,
        MicroCFTA.IntersectionFlatMemoKey.input.eq_3]⟩
  obtain ⟨left, completeLeft⟩ := complete request.left scope.left
  obtain ⟨right, completeRight⟩ := complete request.right scope.right
  constructor
  · refine ⟨request.left, scope.left, scope.leftAvailable, ?_⟩
    unfold inputOf
    rw [completeLeft, Option.getD_some]
  · refine ⟨request.right, scope.right, scope.rightAvailable, ?_⟩
    unfold inputOf
    rw [completeRight, Option.getD_some]

end MicroCFTA.SourceRecursiveIntersectionInputView
