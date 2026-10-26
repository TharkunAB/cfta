import MicroCFTA.EnumerationCorrectness

/-!
# Assignment meaning of a concrete two-slot assimilation

The target receives both pending domains and both suspended lists.
The source then becomes eliminated. The forest already relates the two
variables. Each direction derives their assigned-term equality from its
own forest satisfaction. No graph operation or final solution is an input.
-/
namespace MicroCFTA.SourcePruningEnumerationAssimilationLanguage
open Language Fragments EnumerationState EnumerationCorrectness
variable {Symbol EnumGuard : Type}

/-- Assimilation preserves assignments when the forest already equates its distinct pending slots. -/
theorem assimilated_semantics
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before : State Symbol EnumGuard)
    (source target : Nat) (sourceNode targetNode merged : Option Nat)
    (sourceScs targetScs : List Suspended)
    (sourceStored : before.values[source]? = some (.unenumerated sourceNode sourceScs))
    (targetStored : before.values[target]? = some (.unenumerated targetNode targetScs))
    (different : source ≠ target)
    (sameClass : UnionFind.SameClass before.representatives source target)
    (replacement : ∀ term, permits (merged.map language) term ↔
      permits (sourceNode.map language) term ∧ permits (targetNode.map language) term) :
    Satisfies language meaning assignment
      (assimilated before target source (.unenumerated merged (sourceScs ++ targetScs))) ↔
    Satisfies language meaning assignment before := by
  have sourceBound : source < before.values.length := (List.getElem?_eq_some_iff.mp sourceStored).1
  have targetBound : target < before.values.length := (List.getElem?_eq_some_iff.mp targetStored).1
  have sourceAfter : source < (before.values.set target
      (.unenumerated merged (sourceScs ++ targetScs))).length := by
    simpa only [List.length_set] using sourceBound
  have sourceHeap : heap language before.values source = slot language (.unenumerated sourceNode sourceScs) := by
    simp only [heap, sourceStored, Option.getD_some]
  have targetHeap : heap language before.values target = slot language (.unenumerated targetNode targetScs) := by
    simp only [heap, targetStored, Option.getD_some]
  have pendingMeaning (uv : Nat) (node : Option Nat) (scs : List Suspended) :
      slotSatisfies assignment uv (slot language (.unenumerated node scs)) ↔
        permits (node.map language) (assignment uv) ∧
          ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
    simp only [slot, slotSatisfies, List.forall_mem_map]
  have localMeaning (equal : assignment source = assignment target) :
      slotSatisfies assignment target (slot language (.unenumerated merged (sourceScs ++ targetScs))) ↔
        slotSatisfies assignment source (slot language (.unenumerated sourceNode sourceScs)) ∧
          slotSatisfies assignment target (slot language (.unenumerated targetNode targetScs)) := by
    rw [pendingMeaning, pendingMeaning, pendingMeaning, equal, replacement]
    constructor
    · rintro ⟨⟨sourceDomain, targetDomain⟩, suspended⟩
      exact ⟨⟨sourceDomain, fun sc member => suspended sc (List.mem_append.mpr (Or.inl member))⟩,
        targetDomain, fun sc member => suspended sc (List.mem_append.mpr (Or.inr member))⟩
    · rintro ⟨⟨sourceDomain, sourceSuspended⟩, targetDomain, targetSuspended⟩
      refine ⟨⟨sourceDomain, targetDomain⟩, ?_⟩
      intro sc member
      rcases List.mem_append.mp member with atSource | atTarget
      · exact sourceSuspended sc atSource
      · exact targetSuspended sc atTarget
  have updatedHeap :
      heap language (assimilated before target source
        (.unenumerated merged (sourceScs ++ targetScs))).values =
      setSlot (setSlot (heap language before.values) target
        (slot language (.unenumerated merged (sourceScs ++ targetScs)))) source .eliminated := by
    simp only [assimilated, heap_set language _ source .eliminated sourceAfter,
      heap_set language _ target _ targetBound, slot]
  have heapMeaning (equal : assignment source = assignment target) :
      heapSatisfies (heap language (assimilated before target source
        (.unenumerated merged (sourceScs ++ targetScs))).values) assignment ↔
      heapSatisfies (heap language before.values) assignment := by
    rw [updatedHeap]
    constructor
    · intro afterHeap uv
      have mergedHolds : slotSatisfies assignment target
          (slot language (.unenumerated merged (sourceScs ++ targetScs))) := by
        simpa [setSlot, Ne.symm different] using afterHeap target
      obtain ⟨sourceHolds, targetHolds⟩ := (localMeaning equal).mp mergedHolds
      by_cases atSource : uv = source
      · subst uv
        rw [sourceHeap]
        exact sourceHolds
      · by_cases atTarget : uv = target
        · subst uv
          rw [targetHeap]
          exact targetHolds
        · simpa only [setSlot, ite_eq_right atSource, ite_eq_right atTarget] using afterHeap uv
    · intro beforeHeap uv
      by_cases atSource : uv = source
      · subst uv
        simp [setSlot, slotSatisfies]
      · by_cases atTarget : uv = target
        · subst uv
          simp only [setSlot, ite_eq_right (Ne.symm different)]
          apply (localMeaning equal).mpr
          exact ⟨by simpa only [sourceHeap] using beforeHeap source,
            by simpa only [targetHeap] using beforeHeap target⟩
        · simpa only [setSlot, ite_eq_right atSource, ite_eq_right atTarget] using beforeHeap uv
  constructor
  · intro satisfied
    have equal : assignment source = assignment target := satisfied.1.1 source target sameClass
    exact ⟨⟨satisfied.1.1, (heapMeaning equal).mp satisfied.1.2⟩, satisfied.2⟩
  · intro satisfied
    have equal : assignment source = assignment target := satisfied.1.1 source target sameClass
    exact ⟨⟨satisfied.1.1, (heapMeaning equal).mpr satisfied.1.2⟩, satisfied.2⟩

end MicroCFTA.SourcePruningEnumerationAssimilationLanguage
