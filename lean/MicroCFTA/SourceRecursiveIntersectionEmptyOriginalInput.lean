import MicroCFTA.SourceRecursiveIntersectionInputOfInventory

namespace MicroCFTA.SourceRecursiveIntersectionInputView

theorem empty_originalInput {Symbol Guard : Type}
    (source : MicroCFTA.InternedConstructorTemplates.State Symbol Guard) :
    MicroCFTA.SourceRecursiveIntersectionInputView.OriginalInput source
      MicroCFTA.IntersectSchedule.Input.empty := by
  refine ⟨.empty, Original.empty, ?_, ?_⟩
  · refine MicroCFTA.InternedProbeProvenance.Available.intro .empty ?_ ?_ ?_
    · intro entry impossible
      rw [MicroCFTA.InternedRecordCoherence.entryOf.eq_4] at impossible
      have contradiction : False :=
        Eq.rec (motive := fun option _ =>
          Option.rec (motive := fun _ => Prop) True (fun _ => False) option)
          True.intro impossible
      exact False.elim contradiction
    · intro identity member
      rw [MicroCFTA.InternedConstructorTemplates.Value.free.eq_1] at member
      exact False.elim ((List.mem_nil_iff _).mp member)
    · intro child member
      have emptyChildren :
          MicroCFTA.InternedProbeProvenance.children
            (.empty : MicroCFTA.InternedConstructorTemplates.Value Symbol Guard) = [] := by
        rfl
      rw [emptyChildren] at member
      exact False.elim ((List.mem_nil_iff _).mp member)
  · rw [MicroCFTA.InternedConstructorTemplates.Value.referenceOf.eq_1,
      MicroCFTA.IntersectionFlatMemoKey.input.eq_1]

end MicroCFTA.SourceRecursiveIntersectionInputView
