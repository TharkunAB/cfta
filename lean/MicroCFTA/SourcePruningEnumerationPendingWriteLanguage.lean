import MicroCFTA.EnumerationCorrectness

/-!
# Assignment meaning of a concrete pending-slot write

The replacement adds one incoming domain and its suspended constraints.
The local language equivalence describes only the replacement handle.
The forest, other slots and residual obligations retain their exact values.
No graph operation or satisfying final assignment is an input.
-/
namespace MicroCFTA.SourcePruningEnumerationPendingWriteLanguage
open Language Fragments EnumerationState EnumerationCorrectness
variable {Symbol EnumGuard : Type}

/-- A concrete pending write adds exactly its incoming domain and suspended constraints. -/
theorem pending_write
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before after : State Symbol EnumGuard)
    (uv newHandle : Nat) (oldNode : Option Nat) (oldScs incomingScs : List Suspended)
    (incomingDomain : Term Symbol → Prop)
    (stored : before.values[uv]? = some (.unenumerated oldNode oldScs))
    (representatives : after.representatives = before.representatives)
    (values : after.values = before.values.set uv (.unenumerated (some newHandle) (incomingScs ++ oldScs)))
    (obligations : after.obligations = before.obligations)
    (replacement : ∀ term, language newHandle term ↔
      incomingDomain term ∧ permits (oldNode.map language) term) :
    Satisfies language meaning assignment after ↔
      Satisfies language meaning assignment before ∧ incomingDomain (assignment uv) ∧
        ∀ sc ∈ incomingScs, Suspended.Holds assignment (assignment uv) sc := by
  have bound : uv < before.values.length := (List.getElem?_eq_some_iff.mp stored).1
  have oldSlot : heap language before.values uv = slot language (.unenumerated oldNode oldScs) := by
    simp only [heap, stored, Option.getD_some]
  have pendingMeaning (node : Option Nat) (scs : List Suspended) :
      slotSatisfies assignment uv (slot language (.unenumerated node scs)) ↔
        permits (node.map language) (assignment uv) ∧
          ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
    simp only [slot, slotSatisfies, List.forall_mem_map]
  have localMeaning :
      slotSatisfies assignment uv (slot language (.unenumerated (some newHandle) (incomingScs ++ oldScs))) ↔
        slotSatisfies assignment uv (slot language (.unenumerated oldNode oldScs)) ∧
          incomingDomain (assignment uv) ∧
            ∀ sc ∈ incomingScs, Suspended.Holds assignment (assignment uv) sc := by
    rw [pendingMeaning, pendingMeaning]
    change (language newHandle (assignment uv) ∧
        ∀ sc ∈ incomingScs ++ oldScs, Suspended.Holds assignment (assignment uv) sc) ↔
      (permits (oldNode.map language) (assignment uv) ∧
        ∀ sc ∈ oldScs, Suspended.Holds assignment (assignment uv) sc) ∧
      incomingDomain (assignment uv) ∧
        ∀ sc ∈ incomingScs, Suspended.Holds assignment (assignment uv) sc
    constructor
    · rintro ⟨domain, suspended⟩
      obtain ⟨incoming, old⟩ := (replacement (assignment uv)).mp domain
      exact ⟨⟨old, fun sc member => suspended sc (List.mem_append.mpr (Or.inr member))⟩,
        incoming, fun sc member => suspended sc (List.mem_append.mpr (Or.inl member))⟩
    · rintro ⟨⟨old, previous⟩, incoming, added⟩
      refine ⟨(replacement (assignment uv)).mpr ⟨incoming, old⟩, ?_⟩
      intro sc member
      rcases List.mem_append.mp member with current | earlier
      · exact added sc current
      · exact previous sc earlier
  have heapMeaning :
      heapSatisfies (heap language after.values) assignment ↔
        heapSatisfies (heap language before.values) assignment ∧ incomingDomain (assignment uv) ∧
          ∀ sc ∈ incomingScs, Suspended.Holds assignment (assignment uv) sc := by
    rw [values, heap_set language before.values uv _ bound]
    constructor
    · intro afterHeap
      have updated : slotSatisfies assignment uv
          (slot language (.unenumerated (some newHandle) (incomingScs ++ oldScs))) := by
        simpa [setSlot] using afterHeap uv
      obtain ⟨previous, incoming, added⟩ := localMeaning.mp updated
      refine ⟨?_, incoming, added⟩
      intro other
      by_cases same : other = uv
      · subst other
        rw [oldSlot]
        exact previous
      · simpa only [setSlot, ite_eq_right same] using afterHeap other
    · rintro ⟨beforeHeap, incoming, added⟩ other
      by_cases same : other = uv
      · subst other
        simp only [setSlot]
        apply localMeaning.mpr
        exact ⟨by simpa only [oldSlot] using beforeHeap uv, incoming, added⟩
      · simpa only [setSlot, ite_eq_right same] using beforeHeap other
  simp only [Satisfies, Fragments.stateSatisfies, representatives, obligations]
  rw [heapMeaning]
  constructor
  · rintro ⟨⟨forest, previous, incoming, added⟩, guarded⟩
    exact ⟨⟨⟨forest, previous⟩, guarded⟩, incoming, added⟩
  · rintro ⟨⟨⟨forest, previous⟩, guarded⟩, incoming, added⟩
    exact ⟨⟨forest, previous, incoming, added⟩, guarded⟩

end MicroCFTA.SourcePruningEnumerationPendingWriteLanguage
