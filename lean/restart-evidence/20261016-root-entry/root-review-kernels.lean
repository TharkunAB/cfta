import MicroCFTA.SourceCurrentAllocatedPartialConstructedRoot

namespace MicroCFTA.ConstructedRootReview
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedPartialInitialization
open SourceCurrentAllocatedPartialState
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialSourceReads
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)] [DecidableEq Node]
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

-- Construction supplies every initial semantic and memo invariant; success supplies its own graph and reads.
theorem constructed_retention {width : Nat} {initial final : Cache.State Key} {originals : List Guard}
    (history : History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ originals)
    (value : Node) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    {f g s r e p h m c n budget : Nat} {result : Node} {after : Caller width}
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall f g s r e p h m c n budget
      ⟨emptyValue final, value⟩ (caller width final heap))
    (done : SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
      ⟨emptyValue final, value⟩ (caller width final heap) = .done result after) :
    ∃ next saved, ∃ actual : NodeCall budget ⟨emptyValue final, value⟩ (caller width final heap) result after,
      NodeCallReads formulas solver actual globals saved ∧ Checks (nodeCallTrace actual) ∧
      Post formulas solver next (caller width final heap) after saved ∧
      SourceCurrentAllocatedNativeInventoryState.At formulas solver next after.checked ∧
      InternedFreshOrdinaryProbeHeap.Heap after.checked.native.machine.heap ∧
      EndpointMemoGateTrace.Valid after.checked.native.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.checked.native.machine.heap after.fourth ∧
      Extends (caller width final heap).merge after.merge ∧
      SourceCurrentEmptinessMemo.Extends (caller width final heap).fourth after.fourth ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨next, saved, actual, reads, checks, post, _, law⟩ :=
    SourceCurrentAllocatedPartialConstructedRoot.constructed_root width history valid expression covered value heap built
      formulas solver ranges done
  exact ⟨next, saved, actual, reads, checks, post, post.context.admitted, post.context.probes,
    post.context.globals, post.context.correct, post.retained, post.fourthRetained, law⟩

-- Preparation retains its actual returned cache and previous canonical entries before root execution.
theorem prepared_retention {width : Nat} (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (cached : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, SourceEqualityGuardReadback.Cached guard.equalities)
    (value : Node) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    {f g s r e p h m c n budget : Nat} {result : Node} {after : Caller width}
    (ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall f g s r e p h m c n budget
      ⟨emptyValue (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initial).2, value⟩
      (caller width (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initial).2 heap))
    (done : SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
      ⟨emptyValue (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initial).2, value⟩
      (caller width (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initial).2 heap) = .done result after) :
    let cache := (SourceEqualityOriginalAllocationPreparation.prepare (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ fields next saved,
      SourceEqualityOriginalAllocationPreparation.Receipt (SourceEqualityConstraintOrigins.guards expression) initial fields cache ∧
      Extends initial.table cache.table ∧
      Post formulas solver next (caller width cache heap) after saved ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨fields, preparation, next, saved, _actual, _reads, _checks, post, _, law⟩ :=
    SourceCurrentAllocatedPartialConstructedRoot.prepared_root width initial valid expression cached value heap built
      formulas solver ranges done
  exact ⟨fields, next, saved, preparation, preparation.retained, post, law⟩

-- The second call consumes the first computed inventory and all warm tables without reinitialization.
theorem two_roots {width : Nat} {initial final : Cache.State Key} {originals : List Guard}
    (history : History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ originals)
    (value : Node) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    {f g s r e p h m c n F G S R E P H M C N budget : Nat} {middleValue result : Node}
    {middle after : Caller width}
    (firstRanges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall f g s r e p h m c n budget
      ⟨emptyValue final, value⟩ (caller width final heap))
    (first : SourceCurrentAllocatedPartialWorker.nodeCall f g s r e p h m c n budget
      ⟨emptyValue final, value⟩ (caller width final heap) = .done middleValue middle)
    (nextRanges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall F G S R E P H M C N budget
      ⟨emptyValue final, middleValue⟩ middle)
    (second : SourceCurrentAllocatedPartialWorker.nodeCall F G S R E P H M C N budget
      ⟨emptyValue final, middleValue⟩ middle = .done result after) :
    ∃ firstInventory firstMemos next saved,
      Post formulas solver firstInventory (caller width final heap) middle firstMemos ∧
      Post formulas solver next middle after saved ∧
      Post formulas solver next (caller width final heap) after saved ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨_, identity, same, inherited, _, _, _⟩ :=
    constructed width history valid expression covered value heap built formulas solver
  obtain ⟨firstInventory, firstMemos, _actual, _reads, _checks, firstPost, available, firstLaw⟩ :=
    SourceCurrentAllocatedPartialConstructedRoot.constructed_root width history valid expression covered value heap built
      formulas solver firstRanges first
  have nextInherited := inherited.grows firstPost.effects.grows.constraint_growth
  have secondRanges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall F G S R E P H M C N budget
      ⟨.live identity [], middleValue⟩ middle := by simpa only [same] using nextRanges
  have secondDone : SourceCurrentAllocatedPartialWorker.nodeCall F G S R E P H M C N budget
      ⟨.live identity [], middleValue⟩ middle = .done result after := by simpa only [same] using second
  obtain ⟨next, saved, _actual, _reads, _checks, lastPost, _, lastLaw⟩ :=
    SourceCurrentAllocatedPartialWorkerActual.root_exact formulas solver firstPost.context nextInherited available secondRanges secondDone
  exact ⟨firstInventory, firstMemos, next, saved, firstPost, lastPost, firstPost.trans lastPost,
    fun ambient term => (lastLaw ambient term).trans (firstLaw ambient term)⟩

-- The literal empty root completes with zero bounds; no success or graph premise is supplied.
theorem empty_root_completes (width : Nat) (cache : Cache.State Key) (valid : Cache.Valid cache) :
    ∃ after next saved, SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 0
      ⟨emptyValue cache, .empty⟩ (caller width cache empty) = .done .empty after ∧
      Post formulas solver next (caller width cache empty) after saved ∧
      after.checked = (caller width cache empty).checked ∧
      after.merge = (caller width cache empty).merge ∧ after.fourth = (caller width cache empty).fourth ∧
      after.nodeResults.cells 0 = some ⟨⟨emptyValue cache, .empty⟩, .returned .empty⟩ ∧
      ∀ ambient term, ¬ InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient (.empty : Node) term := by
  let request : NodeRequest := ⟨emptyValue cache, .empty⟩
  let before := caller width cache (empty : State Symbol Guard)
  let started := beginNode request before
  let after := finishNode started.1 .empty started.2.2
  have fresh := SourceCurrentAllocatedPartialMemoSound.beginNode_fresh request before rfl
  have zero : before.nodeResults.next = 0 := rfl
  have run : SourceCurrentAllocatedPartialWorker.nodeCall 0 0 0 0 0 0 0 0 0 0 0 request before = .done .empty after := by
    simp only [SourceCurrentAllocatedPartialWorker.nodeCall,
      SourceCurrentAllocatedPartialWorker.nodeBody, SourceCurrentAllocatedPartialWorker.Outcome.bind]
    rfl
  have ranges : SourceCurrentAllocatedPartialWorkerRanges.nodeCall 0 0 0 0 0 0 0 0 0 0 0 request before := by
    simp only [SourceCurrentAllocatedPartialWorkerRanges.nodeCall,
      SourceCurrentAllocatedPartialWorkerRanges.nodeBody]
    trivial
  obtain ⟨next, saved, _actual, _reads, _checks, post, _, _law⟩ :=
    SourceCurrentAllocatedPartialConstructedRoot.constructed_root width (.start cache) valid .empty
      (by intro guard member; cases member) .empty empty (by simp only [InternedFreshOrdinaryConstruction.build]) formulas solver ranges run
  have handle : started.1 = 0 := by simpa only [zero] using congrArg Prod.fst fresh.1
  have runningCell : started.2.2.nodeResults.cells started.1 = some ⟨request, .evaluating⟩ := by
    rw [handle]
    simpa only [zero] using fresh.2
  have returned := finishNode_returned started.1 request .empty started.2.2 runningCell
  refine ⟨after, next, saved, run, post, ?_, ?_, ?_, ?_, ?_⟩
  · exact (finishNode_components started.1 .empty started.2.2).1.trans (beginNode_components request before).1
  · exact (finishNode_components started.1 .empty started.2.2).2.1.trans (beginNode_components request before).2.1
  · exact (finishNode_components started.1 .empty started.2.2).2.2.1.trans (beginNode_components request before).2.2.1
  · simpa only [after, handle, request] using returned
  · intro ambient term impossible
    simp only [InternedGuardedLanguage.meaning] at impossible

end MicroCFTA.ConstructedRootReview
#print axioms MicroCFTA.ConstructedRootReview.constructed_retention
#print axioms MicroCFTA.ConstructedRootReview.prepared_retention
#print axioms MicroCFTA.ConstructedRootReview.two_roots
#print axioms MicroCFTA.ConstructedRootReview.empty_root_completes
