/- Note [Independent arrow bucket batch]
The batch uses one fixed enum snapshot and one kept set.
Every raw target belongs to that set. Every owner class avoids it.
The finite induction preserves all earlier buckets under the same assignment.
Owners remain pending in the snapshot. A later patch retains earlier owners.
This result does not handle an owner that is another bucket's target.
It does not prove native-domain membership or guard truth.
The final two laws state mathematical finite-term boundaries only.
No accepted-source counterexample is asserted.
-/

import MicroCFTA.SourcePruningEnumerationArrowBucketRecompletion

namespace MicroCFTA.SourcePruningEnumerationArrowBucketRecompletion
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Guard : Type}
set_option autoImplicit false

/-- Recomplete an independent finite batch using one fixed dependency-closed kept set. -/
theorem recomplete_independent_arrow_buckets_at_snapshot
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
    (targetTypes : ∀ event ∈ events, ∀ sc ∈ event.2, ∀ (position : Nat),
      [position] ∈ EqualityTrie.fromPathTrie sc.trie → TypeIn catalog (current sc.var))
    (compatible : ∀ event ∈ events,
      ∀ (firstIndex secondIndex : Nat) (first second : Suspended) (position : Nat),
      event.2[firstIndex]? = some first → event.2[secondIndex]? = some second →
      [position] ∈ EqualityTrie.fromPathTrie first.trie →
      [position] ∈ EqualityTrie.fromPathTrie second.trie → current first.var = current second.var)
    (kept : Nat → Prop)
    (dependencies : ∀ uv, kept uv → ∀ fragment,
      state.values[roots uv]? = some (.enumerated fragment) →
      ∀ hole, EnumerationDependencies.HasHole fragment hole → kept hole)
    (targetsKept : ∀ event ∈ events, ∀ sc ∈ event.2, kept sc.var)
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
  revert pendingOwners distinctOwners arrowPaths targetTypes compatible targetsKept keptSeparate
  induction events generalizing current with
  | nil =>
      intro _pendingOwners _distinctOwners _arrowPaths _targetTypes _compatible _targetsKept _keptSeparate
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
      intro pendingOwners distinctOwners arrowPaths targetTypes compatible targetsKept keptSeparate
      have headMember : event ∈ event :: tail := List.mem_cons_self
      obtain ⟨node, pendingBucket, stored⟩ := pendingOwners event headMember
      obtain ⟨headSeparate, tailSeparate⟩ := List.pairwise_cons.mp distinctOwners
      obtain ⟨argument, result, next, argumentTyped, resultTyped, nextOwner, nextTyped,
        nextAliases, nextEquations, nextKept, _nextTargets, nextHolds, _nextIndexed,
        nextPending⟩ :=
        recomplete_arrow_bucket_at_snapshot catalog state safe roots paths level frontier stratified
          current currentAliases currentEquations event.1 node pendingBucket event.2 stored
          (arrowPaths event headMember) (targetTypes event headMember) (compatible event headMember)
          kept dependencies (targetsKept event headMember) (keptSeparate event headMember)
      have tailTypes : ∀ later ∈ tail, ∀ sc ∈ later.2, ∀ (position : Nat),
          [position] ∈ EqualityTrie.fromPathTrie sc.trie → TypeIn catalog (next sc.var) := by
        intro later member sc listed position represented
        rw [nextKept sc.var (targetsKept later (List.mem_cons_of_mem event member) sc listed)]
        exact targetTypes later (List.mem_cons_of_mem event member) sc listed position represented
      have tailCompatible : ∀ later ∈ tail,
          ∀ (firstIndex secondIndex : Nat) (first second : Suspended) (position : Nat),
          later.2[firstIndex]? = some first → later.2[secondIndex]? = some second →
          [position] ∈ EqualityTrie.fromPathTrie first.trie →
          [position] ∈ EqualityTrie.fromPathTrie second.trie → next first.var = next second.var := by
        intro later member firstIndex secondIndex first second position firstAt secondAt firstPath secondPath
        have firstMember := List.mem_of_getElem? firstAt
        have secondMember := List.mem_of_getElem? secondAt
        rw [nextKept first.var (targetsKept later (List.mem_cons_of_mem event member) first firstMember),
          nextKept second.var (targetsKept later (List.mem_cons_of_mem event member) second secondMember)]
        exact compatible later (List.mem_cons_of_mem event member)
          firstIndex secondIndex first second position firstAt secondAt firstPath secondPath
      obtain ⟨assignment, finalAliases, finalEquations, finalKept, finalEvents, finalPending⟩ :=
        ih next nextAliases (fun slot fragment present => (nextEquations slot fragment present).symm)
          (fun later member => pendingOwners later (List.mem_cons_of_mem event member))
          tailSeparate
          (fun later member => arrowPaths later (List.mem_cons_of_mem event member))
          tailTypes tailCompatible
          (fun later member => targetsKept later (List.mem_cons_of_mem event member))
          (fun later member => keptSeparate later (List.mem_cons_of_mem event member))
      have headSame : assignment event.1 = next event.1 := by
        apply finalPending event.1 node pendingBucket stored
        intro later member joined
        exact headSeparate later member (UnionFind.sameClass_symm joined)
      have headTargets : ∀ sc ∈ event.2, assignment sc.var = next sc.var := by
        intro sc member
        exact finalKept sc.var (targetsKept event headMember sc member)
      refine ⟨assignment, finalAliases, finalEquations, ?_, ?_, ?_⟩
      · intro slot supported
        exact (finalKept slot supported).trans (nextKept slot supported)
      · intro later member
        rcases List.mem_cons.mp member with same | inTail
        · subst later
          refine ⟨argument, result, argumentTyped, resultTyped, headSame.trans nextOwner, ?_, ?_⟩
          · rw [headSame]
            exact nextTyped
          · intro sc listed path represented
            change (assignment event.1).atPath path = some (assignment sc.var)
            rw [headSame, headTargets sc listed]
            exact nextHolds sc listed path represented
        · exact finalEvents later inTail
      · intro slot otherNode otherBucket atSlot separate
        have first := nextPending slot otherNode otherBucket atSlot (separate event headMember)
        have last := finalPending slot otherNode otherBucket atSlot
          (fun later member => separate later (List.mem_cons_of_mem event member))
        exact last.trans first

theorem two_owner_proper_arrow_cycle_impossible
    (assignment : Nat → Term Symbol) (first second : Nat)
    (forward : (assignment first).atPath [1] = some (assignment second))
    (backward : (assignment second).atPath [1] = some (assignment first)) : False := by
  have forwardBound := atPath_height_bound _ _ _ forward
  have backwardBound := atPath_height_bound _ _ _ backward
  simp only [List.length_cons, List.length_nil] at forwardBound backwardBound
  omega

theorem raw_dag_same_position_cycle_impossible
    (assignment : Nat → Term Symbol) (first second third : Nat)
    (firstTarget : (assignment first).atPath [1] = some (assignment second))
    (secondTarget : (assignment first).atPath [1] = some (assignment third))
    (nestedTarget : (assignment second).atPath [1] = some (assignment third)) : False := by
  have same : assignment second = assignment third :=
    Option.some.inj (firstTarget.symm.trans secondTarget)
  have bound := atPath_height_bound _ _ _ nestedTarget
  rw [same] at bound
  simp only [List.length_cons, List.length_nil] at bound
  omega

end MicroCFTA.SourcePruningEnumerationArrowBucketRecompletion
