import MicroCFTA.IntersectNumericFuel
import MicroCFTA.SourceRecursiveIntersectionComputedFuel
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.NumericFuelResetKernel
open Language Binding BinderLanguage IntersectSchedule

/-- A literal ready reset and its new closed-root family have the same independently produced result. -/
theorem reset_same_result [DecidableEq Symbol] (view : View Symbol) (inputs : FiniteInput view)
    (freeCorrect : FreeCorrect view) (bounds : InputBounds view inputs)
    (rank : ClosedRoots view inputs → Call Symbol → Nat)
    (rootDecrease : ∀ (roots nextRoots : ClosedRoots view inputs) (parent child : Call Symbol),
      bounds.size nextRoots.left + bounds.size nextRoots.right < bounds.size roots.left + bounds.size roots.right →
      WorkReady bounds roots parent → WorkReady bounds nextRoots child → rank nextRoots child < rank roots parent)
    (localDecrease : ∀ (roots nextRoots : ClosedRoots view inputs) (parent child : Call Symbol),
      bounds.size nextRoots.left + bounds.size nextRoots.right = bounds.size roots.left + bounds.size roots.right →
      WorkReady bounds roots parent → WorkReady bounds nextRoots child → LocalStep view bounds.pairs child parent →
      rank nextRoots child < rank roots parent)
    (roots : ClosedRoots view inputs) (domain : Domain) (left right : Input)
    (ready : NodeReady roots domain left right) (nonempty : ¬(left = .empty ∨ right = .empty))
    (reset : (closed view left && closed view right && !domain.free.isEmpty) = true) :
    ∃ nextRoots : ClosedRoots view inputs,
      nextRoots.left = left ∧ nextRoots.right = right ∧
      rank nextRoots (.node {} left right) < rank roots (.node domain left right) ∧
      ∃ result,
        (∀ fuel, rank roots (.node domain left right) + 1 ≤ fuel → run view fuel domain left right = .ok result) ∧
        ∀ fuel, rank nextRoots (.node {} left right) + 1 ≤ fuel → run view fuel {} left right = .ok result := by
  have leftValid := input_reach_valid view inputs roots.left left roots.left_valid ready.left_reach
  have rightValid := input_reach_valid view inputs roots.right right roots.right_valid ready.right_reach
  have isClosed : closed view left = true ∧ closed view right = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at reset
    exact reset.1
  let nextRoots : ClosedRoots view inputs := ⟨left, right, leftValid, rightValid, isClosed.1, isClosed.2⟩
  have nextReady := roots_ready view inputs nextRoots
  have smaller := rootDecrease roots nextRoots (.node domain left right) (.node {} left right) (reset_decreases bounds roots domain left right ready reset) ready nextReady
  obtain ⟨parentResult, parentDone⟩ := call_numeric view inputs freeCorrect bounds rank rootDecrease localDecrease roots (.node domain left right) ready
  obtain ⟨childResult, childDone⟩ := call_numeric view inputs freeCorrect bounds rank rootDecrease localDecrease nextRoots (.node {} left right) nextReady
  let fuel := rank roots (.node domain left right) + rank nextRoots (.node {} left right) + 2
  have step : run view (fuel + 1) domain left right = run view fuel {} left right := by
    rw [run.eq_def]
    simp only [nonempty, ite_false, reset, ite_true]
  have same : parentResult = childResult := Except.ok.inj
    ((parentDone (fuel + 1) (by dsimp only [fuel]; omega)).symm.trans
      (step.trans (childDone fuel (by dsimp only [fuel]; omega))))
  subst parentResult
  exact ⟨nextRoots, rfl, rfl, smaller, childResult, parentDone, childDone⟩

end MicroCFTA.NumericFuelResetKernel

#print axioms MicroCFTA.NumericFuelResetKernel.reset_same_result
#check @MicroCFTA.NumericFuelResetKernel.reset_same_result

namespace MicroCFTA.NumericFuelSourceKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule

private def fixture : Syntax Nat Bool :=
  .node [.mk 99 true [
    .binder false (.union [.node [.mk 0 true []], .node [.mk 1 true [.var 0]]]),
    .binder false (.union [.node [.mk 0 false []], .node [.mk 1 true [.var 0]]]),
    .union [.node [.mk 2 true []], .node [.mk 3 false []]]]]
private def kind : Value Nat Bool → Nat
  | .empty => 0
  | .reference _ => 1
  | .node _ _ _ _ => 2
  | .union _ _ _ _ => 3
  | .mu _ _ _ _ => 4

/-- Own mixed recursive source construction gives stable semantic success at one computed initial bound. -/
theorem constructed_recursive_numeric :
    ∃ root heap,
      InternedFreshOrdinaryConstruction.build fixture [] empty = .done root heap ∧
      (children root).map kind = [4, 4, 3] ∧
      ∀ left ∈ children root, ∀ right ∈ children root,
        ∃ result,
          (∀ fuel,
            SourceRecursiveIntersectionComputedFuel.ceiling heap.nodes.next
                (InternedValueMassHeap.initialBound heap) ≤ fuel →
            execute (view heap (fun guard _ => guard)) fuel
              (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩) = .ok result) ∧
          ∃ complete : Completes (view heap (fun guard _ => guard))
              (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩),
            requiredFuel (view heap (fun guard _ => guard))
                (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩) complete ≤
              SourceRecursiveIntersectionComputedFuel.ceiling heap.nodes.next
                (InternedValueMassHeap.initialBound heap) := by
  obtain ⟨root, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete fixture
  have verified := InternedFreshOrdinaryFacts.closed_verified fixture
  have facts : Facts heap := by simpa only [built, InternedNestedConstruction.Outcome.state] using verified.facts
  have available := verified.result root heap built
  have sourceKinds : (match InternedFreshOrdinaryConstruction.build fixture [] empty with
    | .done value _ => decide ((children value).map kind = [4, 4, 3])
    | _ => false) = true := by cbv
  have sourceClosed : (match InternedFreshOrdinaryConstruction.build fixture [] empty with
    | .done value _ => decide ((children value).map Value.free = [[], [], []])
    | _ => false) = true := by cbv
  have kinds : (children root).map kind = [4, 4, 3] := by
    simpa only [built, decide_eq_true_eq] using sourceKinds
  have closed : (children root).map Value.free = List.replicate 3 [] := by
    change (children root).map Value.free = [[], [], []]
    simpa only [built, decide_eq_true_eq] using sourceClosed
  have allClosed : ∀ value ∈ children root, value.free = [] := by
    intro value member
    have inside : value.free ∈ (children root).map Value.free := List.mem_map.mpr ⟨value, member, rfl⟩
    rw [closed] at inside
    exact List.eq_of_mem_replicate inside
  have stored := InternedValueMassHeap.initial heap facts
  refine ⟨root, heap, built, kinds, ?_⟩
  intro left leftMember right rightMember
  have leftAvailable := available.children left leftMember
  have rightAvailable := available.children right rightMember
  have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original left heap facts.coherent leftAvailable (allClosed left leftMember)
  have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original right heap facts.coherent rightAvailable (allClosed right rightMember)
  obtain ⟨result, success⟩ := SourceRecursiveIntersectionComputedFuel.initial_numeric heap facts (fun guard _ => guard)
    left right leftOriginal rightOriginal leftAvailable rightAvailable (allClosed left leftMember) (allClosed right rightMember) stored
  let complete : Completes (view heap (fun guard _ => guard))
      (nodeSemantic ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩) :=
    ⟨_, result, success _ (Nat.le_refl _)⟩
  exact ⟨result, success, complete,
    SourceRecursiveIntersectionComputedFuel.initial_requiredFuel_le heap facts (fun guard _ => guard)
      left right leftOriginal rightOriginal leftAvailable rightAvailable (allClosed left leftMember)
      (allClosed right rightMember) stored complete⟩

end MicroCFTA.NumericFuelSourceKernel

#print axioms MicroCFTA.NumericFuelSourceKernel.constructed_recursive_numeric
#check @MicroCFTA.NumericFuelSourceKernel.constructed_recursive_numeric
