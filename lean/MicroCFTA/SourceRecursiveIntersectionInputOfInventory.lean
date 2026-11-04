import Init.Data.Option.Basic
import MicroCFTA.SourceRecursiveIntersectionInputInventory

namespace MicroCFTA.SourceRecursiveIntersectionInputView

theorem inputOf_mem_inventory {Symbol Guard : Type}
    (state : MicroCFTA.InternedConstructorTemplates.State Symbol Guard)
    (facts : MicroCFTA.InternedNestedFacts.Facts state)
    (value : MicroCFTA.InternedConstructorTemplates.Value Symbol Guard)
    (available : MicroCFTA.InternedProbeProvenance.Available state value) :
    inputOf value ∈ inventory state := by
  unfold inputOf
  generalize complete : MicroCFTA.IntersectionFlatMemoKey.input
      (MicroCFTA.InternedConstructorTemplates.Value.referenceOf value) = option
  revert complete
  refine Option.rec ?_ ?_ option
  · intro complete
    rw [Option.getD_none]
    exact List.mem_cons.mpr (Or.inl rfl)
  · intro input complete
    rw [Option.getD_some]
    exact inventory_available state facts value available input complete

end MicroCFTA.SourceRecursiveIntersectionInputView
