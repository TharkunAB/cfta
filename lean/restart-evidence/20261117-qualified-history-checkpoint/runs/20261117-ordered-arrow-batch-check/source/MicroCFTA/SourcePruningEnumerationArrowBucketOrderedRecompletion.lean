import MicroCFTA.SourcePruningEnumerationArrowBucketRecompletion

namespace MicroCFTA.SourcePruningEnumerationArrowBucketOrderedRecompletion
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
open SourcePruningEnumerationArrowBucketRecompletion
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Guard : Type}
set_option autoImplicit false

/- Note [Ordered pending arrow owners]
Each bucket can refer to kept values or an earlier owner class.
The finite induction adds each completed owner class to the kept set.
Pending owners have no stored fragment dependencies at the fixed snapshot.
Same-position targets must share a union-find class.
This fact gives compatibility under every assignment that satisfies the forest.
The result constructs one assignment for all buckets and stored equations.
It does not derive this dependency order from a source execution.
It does not prove native-domain membership or residual guard truth.
-/

/-- Require each target to be kept or to belong to an earlier owner class. -/
def TargetsEarlier (forest : UnionFind.Forest) (kept : Nat → Prop) :
    List (Nat × List Suspended) → Prop
  | [] => True
  | event :: tail =>
      (∀ sc ∈ event.2, kept sc.var) ∧
      TargetsEarlier forest (fun uv => kept uv ∨ UnionFind.SameClass forest event.1 uv) tail

/-- Recomplete ordered arrow owners, including targets in earlier owner classes. -/
theorem recomplete_ordered_arrow_buckets_at_snapshot
    (catalog : List (String × Nat)) (state : EnumerationState.State Symbol Guard) (safe : Safe state)
    (roots : Nat → Nat) (paths : Roots state.representatives roots)
    (level : Nat → Nat) (frontier : Nat) (stratified : EnumerationOrder.Stratified state level frontier)
    (current : Nat → Term Symbol)
    (currentAliases : UnionFind.Satisfies state.representatives current)
    (currentEquations : ∀ slot fragment, state.values[slot]? = some (.enumerated fragment) →
      fill current fragment = current slot)
    (events : List (Nat × List Suspended))
    (pendingOwners : ∀ event ∈ events, ∃ (node : Option Nat) (bucket : List Suspended),
      state.values[event.1]? = some (.unenumerated node bucket))
    (distinctOwners : events.Pairwise (fun first second =>
      ¬UnionFind.SameClass state.representatives first.1 second.1))
    (arrowPaths : ∀ event ∈ events, ∀ sc ∈ event.2,
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, path = [1] ∨ path = [2])
    (compatibleClasses : ∀ event ∈ events,
      ∀ (firstIndex secondIndex : Nat) (first second : Suspended) (position : Nat),
      event.2[firstIndex]? = some first → event.2[secondIndex]? = some second →
      [position] ∈ EqualityTrie.fromPathTrie first.trie →
      [position] ∈ EqualityTrie.fromPathTrie second.trie →
      UnionFind.SameClass state.representatives first.var second.var)
    (kept : Nat → Prop)
    (dependencies : ∀ uv, kept uv → ∀ fragment,
      state.values[roots uv]? = some (.enumerated fragment) →
      ∀ hole, EnumerationDependencies.HasHole fragment hole → kept hole)
    (targetTypes : ∀ event ∈ events, ∀ sc ∈ event.2, kept sc.var →
      TypeIn catalog (current sc.var))
    (targetOrder : TargetsEarlier state.representatives kept events)
    (keptSeparate : ∀ event ∈ events, ∀ slot, kept slot →
      ¬UnionFind.SameClass state.representatives event.1 slot) :
    ∃ assignment : Nat → Term Symbol,
      UnionFind.Satisfies state.representatives assignment ∧
      (∀ slot fragment, state.values[slot]? = some (.enumerated fragment) →
        assignment slot = fill assignment fragment) ∧
      (∀ slot, kept slot → assignment slot = current slot) ∧
      (∀ event ∈ events, ∃ (argument result : Term Symbol),
        TypeIn catalog argument ∧ TypeIn catalog result ∧
        assignment event.1 = .node (literal "->") [.node (literal "(->)") [], argument, result] ∧
        TypeIn catalog (assignment event.1) ∧
        ∀ sc ∈ event.2, Suspended.Holds assignment (assignment event.1) sc) ∧
      ∀ slot node bucket, state.values[slot]? = some (.unenumerated node bucket) →
        (∀ event ∈ events, ¬UnionFind.SameClass state.representatives event.1 slot) →
        assignment slot = current slot
 := by
  revert pendingOwners distinctOwners arrowPaths compatibleClasses dependencies targetTypes targetOrder keptSeparate
  induction events generalizing current kept with
  | nil =>
      intro _pendingOwners _distinctOwners _arrowPaths _compatibleClasses _dependencies _targetTypes _targetOrder _keptSeparate
      refine ⟨current, currentAliases, ?_, ?_, ?_, ?_⟩
      · intro slot fragment stored
        exact (currentEquations slot fragment stored).symm
      · intro _slot _supported
        rfl
      · intro event member
        cases member
      · intro _slot _node _bucket _stored _separate
        rfl
  | cons event tail ih =>
      intro pendingOwners distinctOwners arrowPaths compatibleClasses dependencies targetTypes targetOrder keptSeparate
      have headMember : event ∈ event :: tail := List.mem_cons_self
      obtain ⟨node, pendingBucket, stored⟩ := pendingOwners event headMember
      obtain ⟨headSeparate, tailSeparate⟩ := List.pairwise_cons.mp distinctOwners
      obtain ⟨headTargets, tailOrder⟩ := targetOrder
      obtain ⟨argument, result, next, argumentTyped, resultTyped, nextOwner, nextTyped,
        nextAliases, nextEquations, nextKept, _nextTargets, nextHolds, _nextIndexed,
        nextPending⟩ :=
        recomplete_arrow_bucket_at_snapshot catalog state safe roots paths level frontier stratified
          current currentAliases currentEquations event.1 node pendingBucket event.2 stored
          (arrowPaths event headMember)
          (fun sc listed _position _represented => targetTypes event headMember sc listed (headTargets sc listed))
          (fun firstIndex secondIndex first second position firstAt secondAt firstPath secondPath =>
            currentAliases first.var second.var
              (compatibleClasses event headMember firstIndex secondIndex first second position
                firstAt secondAt firstPath secondPath))
          kept dependencies headTargets (keptSeparate event headMember)
      let nextKeptSet := fun uv => kept uv ∨ UnionFind.SameClass state.representatives event.1 uv
      have ownerRoot : IsRoot state.representatives event.1 :=
        (safe.2 event.1 (.unenumerated node pendingBucket) stored).mp
          (by intro impossible; cases impossible)
      have ownerFixed := (root_iff state.representatives roots paths event.1).mp ownerRoot
      have nextDependencies : ∀ uv, nextKeptSet uv → ∀ fragment,
          state.values[roots uv]? = some (.enumerated fragment) →
          ∀ hole, EnumerationDependencies.HasHole fragment hole → nextKeptSet hole := by
        intro uv supported fragment present hole referenced
        rcases supported with original | previous
        · exact Or.inl (dependencies uv original fragment present hole referenced)
        · have same : roots uv = event.1 :=
            ((class_iff state.representatives roots paths event.1 uv).mp previous).symm.trans ownerFixed
          rw [same, stored] at present
          cases present
      have nextTypes : ∀ later ∈ tail, ∀ sc ∈ later.2, nextKeptSet sc.var →
          TypeIn catalog (next sc.var) := by
        intro later member sc listed supported
        rcases supported with original | previous
        · rw [nextKept sc.var original]
          exact targetTypes later (List.mem_cons_of_mem event member) sc listed original
        · rw [← nextAliases event.1 sc.var previous]
          exact nextTyped
      have nextSeparate : ∀ later ∈ tail, ∀ slot, nextKeptSet slot →
          ¬UnionFind.SameClass state.representatives later.1 slot := by
        intro later member slot supported
        rcases supported with original | previous
        · exact keptSeparate later (List.mem_cons_of_mem event member) slot original
        · intro joined
          exact headSeparate later member
            (UnionFind.sameClass_trans previous (UnionFind.sameClass_symm joined))
      obtain ⟨assignment, finalAliases, finalEquations, finalKept, finalEvents, finalPending⟩ :=
        ih next nextAliases (fun slot fragment present => (nextEquations slot fragment present).symm)
          nextKeptSet
          (fun later member => pendingOwners later (List.mem_cons_of_mem event member))
          tailSeparate
          (fun later member => arrowPaths later (List.mem_cons_of_mem event member))
          (fun later member => compatibleClasses later (List.mem_cons_of_mem event member))
          nextDependencies nextTypes tailOrder nextSeparate
      have headSame : assignment event.1 = next event.1 := by
        apply finalKept event.1
        exact Or.inr ((class_iff state.representatives roots paths event.1 event.1).mpr rfl)
      have headTargetsSame : ∀ sc ∈ event.2, assignment sc.var = next sc.var := by
        intro sc member
        exact finalKept sc.var (Or.inl (headTargets sc member))
      refine ⟨assignment, finalAliases, finalEquations, ?_, ?_, ?_⟩
      · intro slot supported
        exact (finalKept slot (Or.inl supported)).trans (nextKept slot supported)
      · intro later member
        rcases List.mem_cons.mp member with same | inTail
        · subst later
          refine ⟨argument, result, argumentTyped, resultTyped, headSame.trans nextOwner, ?_, ?_⟩
          · rw [headSame]
            exact nextTyped
          · intro sc listed path represented
            change (assignment event.1).atPath path = some (assignment sc.var)
            rw [headSame, headTargetsSame sc listed]
            exact nextHolds sc listed path represented
        · exact finalEvents later inTail
      · intro slot otherNode otherBucket atSlot separate
        have first := nextPending slot otherNode otherBucket atSlot (separate event headMember)
        have last := finalPending slot otherNode otherBucket atSlot
          (fun later member => separate later (List.mem_cons_of_mem event member))
        exact last.trans first

end MicroCFTA.SourcePruningEnumerationArrowBucketOrderedRecompletion

#check MicroCFTA.SourcePruningEnumerationArrowBucketOrderedRecompletion.TargetsEarlier
#print axioms MicroCFTA.SourcePruningEnumerationArrowBucketOrderedRecompletion.recomplete_ordered_arrow_buckets_at_snapshot
