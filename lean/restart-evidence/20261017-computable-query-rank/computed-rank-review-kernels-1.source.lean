import MicroCFTA.IntersectNumericRank
import MicroCFTA.SourceRecursiveIntersectionComputedFuel
import MicroCFTA.SourceRecursiveIntersectionInstructionProfile
import MicroCFTA.InternedFreshOrdinaryAllocationBudget
import MicroCFTA.InternedFreshOrdinaryResultMass
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.ComputedRankReview
open Cache Language Binding BinderLanguage IntersectSchedule InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open SourceRecursiveIntersectionInputView

/-- Duplicate pair occurrences retain actual row and child rank descent without a distinctness premise. -/
theorem duplicate_pairs_rows {Symbol : Type} {view : View Symbol} {inputs : FiniteInput view}
    (bounds : InputBounds view inputs) (bound : Nat) (uniform : ∀ input, bounds.localWeight.value input ≤ bound)
    (roots : ClosedRoots view inputs) (domain : Domain) (first second : Nat) (left right : Row Symbol)
    (leftMember : left ∈ view.rows first) (rightMember : right ∈ view.rows second)
    (children : Input × Input) (member : children ∈ left.children.zip right.children) :
    let doubled : InputBounds view inputs := {bounds with
      pairs := bounds.pairs ++ bounds.pairs
      pair_mem := fun left right first second nonemptyLeft nonemptyRight => List.mem_append.mpr
        (Or.inl (bounds.pair_mem left right first second nonemptyLeft nonemptyRight))}
    (unseen doubled.pairs domain).length = 2 * (unseen bounds.pairs domain).length ∧
      IntersectNumericRank.rank doubled bound roots (.node domain children.1 children.2) <
        IntersectNumericRank.rank doubled bound roots (.edge domain left right) ∧
      IntersectNumericRank.rank doubled bound roots (.edge domain left right) <
        IntersectNumericRank.rank doubled bound roots (.node domain (.node first) (.node second)) := by
  dsimp only
  let doubled : InputBounds view inputs := {bounds with
    pairs := bounds.pairs ++ bounds.pairs
    pair_mem := fun left right first second nonemptyLeft nonemptyRight => List.mem_append.mpr
      (Or.inl (bounds.pair_mem left right first second nonemptyLeft nonemptyRight))}
  refine ⟨?_, ?_, ?_⟩
  · simp only [unseen, List.filter_append, List.length_append]
    omega
  · exact IntersectNumericRank.local_decrease doubled bound uniform roots roots _ _ rfl
      (.edgeChild domain left right children member)
  · exact IntersectNumericRank.local_decrease doubled bound uniform roots roots _ _ rfl
      (.nodeRows domain first second left right leftMember rightMember)

/-- A reached reset can restore the pair count, then canonical swapping decreases the same computed rank. -/
theorem reset_then_swap {Symbol : Type} {view : View Symbol} {inputs : FiniteInput view}
    (bounds : InputBounds view inputs) (bound : Nat) (uniform : ∀ input, bounds.localWeight.value input ≤ bound)
    (roots : ClosedRoots view inputs) (domain : Domain) (left right : Input)
    (ready : NodeReady roots domain left right)
    (reset : (closed view left && closed view right && !domain.free.isEmpty) = true)
    (swap : greater left right = true) :
    ∃ nextRoots : ClosedRoots view inputs,
      nextRoots.left = left ∧ nextRoots.right = right ∧
      IntersectNumericRank.rank bounds bound nextRoots (.node {} left right) <
        IntersectNumericRank.rank bounds bound roots (.node domain left right) ∧
      IntersectNumericRank.rank bounds bound nextRoots.swap (.node {} right left) <
        IntersectNumericRank.rank bounds bound nextRoots (.node {} left right) ∧
      (unseen bounds.pairs {}).length = bounds.pairs.length := by
  have isClosed : closed view left = true ∧ closed view right = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at reset
    exact reset.1
  let nextRoots : ClosedRoots view inputs := ⟨left, right,
    input_reach_valid view inputs roots.left left roots.left_valid ready.left_reach,
    input_reach_valid view inputs roots.right right roots.right_valid ready.right_reach,
    isClosed.1, isClosed.2⟩
  refine ⟨nextRoots, rfl, rfl, ?_, ?_, ?_⟩
  · exact IntersectNumericRank.root_decrease bounds bound uniform roots nextRoots _ _
      (reset_decreases bounds roots domain left right ready reset)
  · exact IntersectNumericRank.local_decrease bounds bound uniform nextRoots nextRoots.swap _ _
      (by simp only [IntersectNumericRank.rootSize, ClosedRoots.swap, Nat.add_comm]) (.swap {} left right swap)
  · simp [unseen]

private def plan : Syntax Nat Nat := .node [.mk 99 1000 [
  .node [.mk 7 17 [.node [.mk 3 3000 []]]],
  .node [.mk 7 29 [.node [.mk 3 3000 []]], .mk 8 5000 []]]]
private def built := InternedFreshOrdinaryConstruction.build plan [] empty
private def source := built.state
private def root : Value Nat Nat := match built with | .done value _ => value | .pending .. => .empty
private def left : Value Nat Nat := ((children root)[0]?).getD .empty
private def right : Value Nat Nat := ((children root)[1]?).getD .empty
private def holds (guard : Nat) (_ : Term Nat) := 0 < guard
private def initialMass := InternedFreshOrdinaryResultMass.transform plan 1
private def initialNodes := InternedFreshOrdinaryAllocationBudget.nodeBudget plan
private def fuelCeiling := SourceRecursiveIntersectionComputedFuel.ceiling initialNodes initialMass
private def request : SourceRecursiveIntersectionThunks.NodeRequest Nat Nat := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩

private theorem constructed : built = .done root source := by
  obtain ⟨value, final, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete plan
  simp only [built, root, source, done, Outcome.state]
private theorem facts : Facts source := (InternedFreshOrdinaryFacts.closed_verified plan).facts
private theorem root_available : Available source root := (InternedFreshOrdinaryFacts.closed_verified plan).result root source constructed
private theorem available : Available source left ∧ Available source right := by
  constructor
  · exact root_available.children left (by cbv; exact .head _)
  · exact root_available.children right (by cbv; exact .tail _ (.head _))
private theorem original : Original left ∧ Original right :=
  ⟨SourceRecursiveIntersectionOriginalOutput.closed_original left source facts.coherent available.1 (by cbv),
   SourceRecursiveIntersectionOriginalOutput.closed_original right source facts.coherent available.2 (by cbv)⟩
private theorem stored : InternedValueMassHeap.Stored initialMass source := by
  have produced := (InternedFreshOrdinaryResultMass.build_bound plan [] empty 1
    (InternedValueMassHeap.empty_stored (by decide)) (by intro value member; cases member)).1
  exact produced
private theorem nodes_bound : source.nodes.next ≤ initialNodes := by
  have produced := (InternedFreshOrdinaryAllocationBudget.build_bound plan [] empty).1
  simpa only [source, built, empty, Cache.emptyState, Nat.zero_add] using produced

/-- Own nonidentical guarded source roots give semantic success and least-fuel credit at a purely syntactic mass and allocation forecast. -/
theorem constructed_guarded_numeric :
    built = .done root source ∧ left ≠ right ∧
    InternedValueMassHeap.Stored initialMass source ∧ source.nodes.next ≤ initialNodes ∧
    ∃ result, (∀ fuel, fuelCeiling ≤ fuel → execute (view source holds) fuel
        (SourceRecursiveIntersectionNative.nodeSemantic request) = .ok result) ∧
      ∃ complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request),
        requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete ≤ fuelCeiling ∧
        SourceRecursiveIntersectionInstructionProfile.budget
            (SourceRecursiveIntersectionInstructionProfile.sourceBranching source)
            (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete) ≤
          SourceRecursiveIntersectionInstructionProfile.budget
            (SourceRecursiveIntersectionInstructionProfile.sourceBranching source) fuelCeiling := by
  obtain ⟨result, success⟩ := SourceRecursiveIntersectionComputedFuel.initial_numeric source facts holds left right
    original.1 original.2 available.1 available.2 (by cbv) (by cbv) stored
  have enough : SourceRecursiveIntersectionComputedFuel.ceiling source.nodes.next initialMass ≤ fuelCeiling :=
    SourceRecursiveIntersectionComputedFuel.ceiling_mono nodes_bound (Nat.le_refl _)
  have succeeded : ∀ fuel, fuelCeiling ≤ fuel → execute (view source holds) fuel
      (SourceRecursiveIntersectionNative.nodeSemantic request) = .ok result :=
    fun fuel room => success fuel (Nat.le_trans enough room)
  let complete : Completes (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) :=
    ⟨fuelCeiling, result, succeeded fuelCeiling (Nat.le_refl _)⟩
  have least := Nat.le_trans (SourceRecursiveIntersectionComputedFuel.initial_requiredFuel_le source facts holds
    left right original.1 original.2 available.1 available.2 (by cbv) (by cbv) stored complete) enough
  refine ⟨constructed, ?_, stored, nodes_bound, result, succeeded, complete, least,
    SourceRecursiveIntersectionInstructionProfile.budget_height_mono _ least⟩
  intro same
  have unequal : left.referenceOf ≠ right.referenceOf := by cbv; decide
  exact unequal (congrArg Value.referenceOf same)

end MicroCFTA.ComputedRankReview

#print axioms MicroCFTA.ComputedRankReview.duplicate_pairs_rows
#check @MicroCFTA.ComputedRankReview.duplicate_pairs_rows
#print axioms MicroCFTA.ComputedRankReview.reset_then_swap
#check @MicroCFTA.ComputedRankReview.reset_then_swap
#print axioms MicroCFTA.ComputedRankReview.constructed_guarded_numeric
#check @MicroCFTA.ComputedRankReview.constructed_guarded_numeric
