import MicroCFTA.SourceRecursiveIntersectionInputInventory
import Init.Data.List.Lemmas

namespace MicroCFTA.SourceRecursiveIntersectionInputView

/-- An original Mu input uses a name from the initial inventory. -/
theorem OriginalInput.mu_inventory_name
    {Symbol Guard : Type}
    (state : MicroCFTA.InternedConstructorTemplates.State Symbol Guard)
    (facts : MicroCFTA.InternedNestedFacts.Facts state)
    (name : Nat)
    (original : OriginalInput state (MicroCFTA.IntersectSchedule.Input.mu name)) :
    name ∈ List.range state.nodes.next := by
  have member := OriginalInput.inventory state facts (.mu name) original
  unfold inventory at member
  rcases List.mem_cons.mp member with emptyEq | remaining
  · cases emptyEq
  · obtain ⟨issued, inRange, inTags⟩ := List.mem_flatMap.mp remaining
    rcases List.mem_cons.mp inTags with nodeEq | remaining
    · cases nodeEq
    · rcases List.mem_cons.mp remaining with muEq | remaining
      · injection muEq with nameEq
        subst issued
        exact inRange
      · rcases List.mem_cons.mp remaining with unionEq | remaining
        · cases unionEq
        · rcases List.mem_cons.mp remaining with refEq | remaining
          · cases refEq
          · exact False.elim ((List.mem_nil_iff _).mp remaining)

end MicroCFTA.SourceRecursiveIntersectionInputView
