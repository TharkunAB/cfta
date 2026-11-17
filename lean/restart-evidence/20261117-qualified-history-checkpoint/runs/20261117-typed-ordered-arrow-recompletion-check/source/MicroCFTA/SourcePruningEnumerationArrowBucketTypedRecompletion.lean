import MicroCFTA.SourcePruningEnumerationArrowBucketOrderedRecompletion
import MicroCFTA.SourceSynthesisTypeFragmentAssignment

namespace MicroCFTA.SourcePruningEnumerationArrowBucketTypedRecompletion
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
open SourceSynthesisTypeFragmentAssignment (TypeFragment)
open SourcePruningEnumerationArrowBucketOrderedRecompletion
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Guard : Type}
set_option autoImplicit false

/- Note [One ordered assignment from past fragment syntax]
The finite evaluator starts from the rigid var1 choice.
The marked fragment syntax derives target typing at that same evaluator.
The ordered recompletion proof then constructs one joint assignment.
No current assignment or target typing result is a caller premise.
The marked syntax and dependency order remain explicit snapshot premises.
Their preservation by actual source histories remains a separate proof.
-/

/-- Construct one ordered assignment from a fixed snapshot with marked Type fragments. -/
theorem recomplete_ordered_arrow_buckets_from_typed_fragments
    (catalog : List (String × Nat)) (state : EnumerationState.State Symbol Guard) (safe : Safe state)
    (roots : Nat → Nat) (paths : Roots state.representatives roots)
    (level : Nat → Nat) (frontier : Nat) (stratified : EnumerationOrder.Stratified state level frontier)
    (marked : Nat → Prop)
    (expanded : ∀ uv, marked uv → ∀ fragment,
      state.values[roots uv]? = some (.enumerated fragment) → TypeFragment catalog marked fragment)
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
    (targetsMarked : ∀ event ∈ events, ∀ sc ∈ event.2, kept sc.var → marked sc.var)
    (targetOrder : TargetsEarlier state.representatives kept events)
    (keptSeparate : ∀ event ∈ events, ∀ slot, kept slot →
      ¬UnionFind.SameClass state.representatives event.1 slot) :
    let current := EnumerationPendingAssignment.evaluateSlotsWith state.values roots
      (fun _ => .node (literal "var1") []) (frontier + 1)
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
  dsimp only
  let base : Nat → Term Symbol := fun _ => .node (literal "var1") []
  let current := EnumerationPendingAssignment.evaluateSlotsWith state.values roots base (frontier + 1)
  have baseAliases : UnionFind.Satisfies state.representatives base := by
    intro _left _right _same
    rfl
  have baseTyped : ∀ uv, marked uv → TypeIn catalog (base uv) := by
    intro _uv _marked
    exact TypeIn.leaf "var1" (by simp)
  obtain ⟨currentAliases, currentEquations, _currentPending⟩ :=
    EnumerationPendingAssignment.evaluateSlotsWith_witness
      state safe roots paths level frontier stratified base baseAliases
  have targetTypes : ∀ event ∈ events, ∀ sc ∈ event.2, kept sc.var →
      TypeIn catalog (current sc.var) := by
    intro event member sc listed supported
    exact SourceSynthesisTypeFragmentAssignment.evaluateSlotsWith_type
      catalog state.values roots marked base baseTyped expanded
      (frontier + 1) sc.var (targetsMarked event member sc listed supported)
  exact recomplete_ordered_arrow_buckets_at_snapshot
    catalog state safe roots paths level frontier stratified current currentAliases
    (fun slot fragment stored => (currentEquations slot fragment stored).symm)
    events pendingOwners distinctOwners arrowPaths compatibleClasses kept dependencies
    targetTypes targetOrder keptSeparate

end MicroCFTA.SourcePruningEnumerationArrowBucketTypedRecompletion

#print axioms MicroCFTA.SourcePruningEnumerationArrowBucketTypedRecompletion.recomplete_ordered_arrow_buckets_from_typed_fragments
