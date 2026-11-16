import MicroCFTA.SourcePruningEnumerationParametricArrowBucketWitness
import MicroCFTA.EnumerationPendingRecompletion

namespace MicroCFTA.SourcePruningEnumerationArrowBucketRecompletion
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Guard : Type}
set_option autoImplicit false

/-- Recomplete one arrow bucket and all stored equations at the same final snapshot. -/
theorem recomplete_arrow_bucket_at_snapshot
    (catalog : List (String × Nat)) (state : EnumerationState.State Symbol Guard) (safe : Safe state)
    (roots : Nat → Nat) (paths : Roots state.representatives roots)
    (level : Nat → Nat) (frontier : Nat) (stratified : EnumerationOrder.Stratified state level frontier)
    (current : Nat → Term Symbol)
    (currentAliases : UnionFind.Satisfies state.representatives current)
    (currentEquations : ∀ slot fragment, state.values[slot]? = some (.enumerated fragment) →
      fill current fragment = current slot)
    (owner : Nat) (node : Option Nat) (pendingBucket removedBucket : List Suspended)
    (ownerPending : state.values[owner]? = some (.unenumerated node pendingBucket))
    (arrowPaths : ∀ sc ∈ removedBucket, ∀ path ∈ EqualityTrie.fromPathTrie sc.trie,
      path = [1] ∨ path = [2])
    (targetTypes : ∀ sc ∈ removedBucket, ∀ (position : Nat),
      [position] ∈ EqualityTrie.fromPathTrie sc.trie → TypeIn catalog (current sc.var))
    (compatible : ∀ (firstIndex secondIndex : Nat) (first second : Suspended) (position : Nat),
      removedBucket[firstIndex]? = some first → removedBucket[secondIndex]? = some second →
      [position] ∈ EqualityTrie.fromPathTrie first.trie →
      [position] ∈ EqualityTrie.fromPathTrie second.trie → current first.var = current second.var)
    (kept : Nat → Prop)
    (dependencies : ∀ uv, kept uv → ∀ fragment,
      state.values[roots uv]? = some (.enumerated fragment) →
      ∀ hole, EnumerationDependencies.HasHole fragment hole → kept hole)
    (targetsKept : ∀ sc ∈ removedBucket, kept sc.var)
    (keptSeparate : ∀ slot, kept slot → ¬UnionFind.SameClass state.representatives owner slot) :
    ∃ (argument result : Term Symbol) (assignment : Nat → Term Symbol),
      TypeIn catalog argument ∧ TypeIn catalog result ∧
      assignment owner = .node (literal "->") [.node (literal "(->)") [], argument, result] ∧
      TypeIn catalog (assignment owner) ∧ UnionFind.Satisfies state.representatives assignment ∧
      (∀ slot fragment, state.values[slot]? = some (.enumerated fragment) →
        assignment slot = fill assignment fragment) ∧
      (∀ slot, kept slot → assignment slot = current slot) ∧
      (∀ sc ∈ removedBucket, assignment sc.var = current sc.var) ∧
      (∀ sc ∈ removedBucket, Suspended.Holds assignment (assignment owner) sc) ∧
      (∀ (occurrence : Nat) (sc : Suspended), removedBucket[occurrence]? = some sc →
        Suspended.Holds assignment (assignment owner) sc) ∧
      ∀ slot otherNode otherBucket,
        state.values[slot]? = some (.unenumerated otherNode otherBucket) →
        ¬UnionFind.SameClass state.representatives owner slot → assignment slot = current slot
 := by
  have root : IsRoot state.representatives owner :=
    (safe.2 owner (.unenumerated node pendingBucket) ownerPending).mp
      (by intro impossible; cases impossible)
  have separate : Avoids state.representatives owner removedBucket := by
    intro sc member
    exact keptSeparate sc.var (targetsKept sc member)
  obtain ⟨argument, result, base, argumentTyped, resultTyped, baseOwner, baseTyped,
      baseAliases, baseOutside, baseTargets, baseHeld, _baseIndexed⟩ :=
    SourcePruningEnumerationParametricArrowBucketWitness.parametric_arrow_bucket_recompletion
      catalog state.representatives owner removedBucket current root currentAliases separate
      arrowPaths targetTypes compatible
  have baseAgree : ∀ slot, kept slot → base slot = current slot := by
    intro slot supported
    exact baseOutside slot (keptSeparate slot supported)
  let assignment := EnumerationPendingAssignment.evaluateSlotsWith state.values roots base (frontier + 1)
  have completed := EnumerationPendingAssignment.recomplete_with_base_on
    state safe roots paths level frontier stratified current base currentAliases currentEquations
    baseAliases kept dependencies baseAgree
  dsimp only at completed
  have ownerSame : assignment owner = base owner :=
    completed.2.2.1 owner node pendingBucket ownerPending
  have ownerTyped : TypeIn catalog (assignment owner) := by
    rw [ownerSame]
    exact baseTyped
  have targets : ∀ sc ∈ removedBucket, assignment sc.var = current sc.var := by
    intro sc member
    exact completed.2.2.2 sc.var (targetsKept sc member)
  have held : ∀ sc ∈ removedBucket, Suspended.Holds assignment (assignment owner) sc := by
    intro sc member path represented
    have sameTarget : assignment sc.var = base sc.var :=
      (targets sc member).trans (baseTargets sc member).symm
    simpa only [ownerSame, sameTarget] using baseHeld sc member path represented
  refine ⟨argument, result, assignment, argumentTyped, resultTyped, ownerSame.trans baseOwner,
    ownerTyped, completed.1, completed.2.1, completed.2.2.2, targets, held, ?_, ?_⟩
  · intro occurrence sc indexed
    exact held sc (List.mem_iff_getElem?.mpr ⟨occurrence, indexed⟩)
  · intro slot otherNode otherBucket stored different
    exact (completed.2.2.1 slot otherNode otherBucket stored).trans (baseOutside slot different)

end MicroCFTA.SourcePruningEnumerationArrowBucketRecompletion

#check @MicroCFTA.SourcePruningEnumerationArrowBucketRecompletion.recomplete_arrow_bucket_at_snapshot
#print axioms MicroCFTA.SourcePruningEnumerationArrowBucketRecompletion.recomplete_arrow_bucket_at_snapshot
