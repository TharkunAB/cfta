import MicroCFTA.SourceEqualityAnnotationStoredSyntax

/-!
# Physical annotations through actual repaired stored unfolding

Stored-body encoding copies only original complete guards. The actual source
executor therefore retains the physical annotation heap in complete and
pending outcomes. This proof does not require a complete unfolding result.
-/
namespace MicroCFTA.SourceEqualityAnnotationUnfold
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceEqualityAnnotationHeap SourceEqualityAnnotationStoredSyntax

/-- Actual repaired stored substitution retains original physical edge annotation checks. -/
theorem execute [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (value : Value Symbol Guard)
    (environment : InternedStoredSubstitution.Environment Symbol Guard) (state : State Symbol Guard)
    (heap : Heap annotation state) (facts : Facts state) (available : Available state value) :
    Heap annotation (InternedFreshOrdinaryStoredSubstitution.execute value environment state).state :=
  SourceEqualityAnnotationConstruction.build annotation _
    (encode_allowed annotation value (SourceEqualityAnnotationHeap.available annotation state heap facts.linked value available)
      (InternedStoredSubstitution.leaves value) []) _ state heap

/-- Actual repaired Mu unfolding retains annotation heaps through its original stored body. -/
theorem unfold [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (value : Value Symbol Guard)
    (state : State Symbol Guard) (heap : Heap annotation state) (facts : Facts state) (available : Available state value) :
    Heap annotation (InternedFreshOrdinaryStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact heap
  | mu entry body depth ordinary =>
      exact execute annotation body _ state heap facts (available.children body (by simp [InternedProbeProvenance.children]))

end MicroCFTA.SourceEqualityAnnotationUnfold
