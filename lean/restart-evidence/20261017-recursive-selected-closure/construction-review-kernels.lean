import MicroCFTA.SourceCurrentHereditaryRequiredMerge
import MicroCFTA.InternedFreshOrdinaryCosts
import MicroCFTA.InternedFreshOrdinarySourceFreeNames

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.ConstructionReviewKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values)
open SourceEqualityAnnotationLanguage SourceEqualityAnnotationConstruction
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceCurrentHereditaryConstruction (MuStored)
variable {Symbol Guard : Type}

/-- Allowed source syntax constructs its own head and Required call at their actual returned heaps. -/
theorem constructed_head_required [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (expression : Syntax Symbol Guard) (allowed : Allowed valid expression) (needed : SourceEqualityNeeded.Needed) :
    ∃ value before exposed middle result after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value before ∧
      SourceEqualityRequiredHead.Head value before exposed middle ∧
      RequireNode needed exposed middle result after ∧
      MuStored valid after ∧ Annotated valid result ∧ SemanticReady after ∧
      InternedFreshOrdinaryCostHeap.Heap after ∧ Available after result ∧ result.free = [] ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel headFuel => SourceEqualityRequiredWorker.require fuel headFuel needed exposed middle) result after := by
  obtain ⟨value, before, built, stored, annotated⟩ := SourceCurrentHereditaryConstruction.closed valid expression allowed
  have semantic := SourceEqualityRequiredSemanticCache.constructed expression value before built
  have costs : InternedFreshOrdinaryCostHeap.Heap before := by
    simpa only [built, Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value before built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value before built
  obtain ⟨exposed, middle, head, _, exposedAvailable, exposedClosed, _⟩ :=
    SourceEqualityRequiredHead.complete value before semantic.ready available closed
  obtain ⟨middleStored, exposedAnnotated⟩ := SourceCurrentHereditaryExposure.head valid head semantic.ready available closed annotated stored
  have headEffects := SourceCurrentRequiredHeapEffects.head (fun _ => True) head semantic costs (by intro _ _ _; trivial) available
  obtain ⟨result, after, required, _, _, resultClosed⟩ := SourceEqualityRequiredComplete.complete needed exposed middle
    headEffects.1.ready exposedAvailable exposedClosed
  have annotations := SourceCurrentHereditaryRequiredMerge.node valid required headEffects.2.1 headEffects.2.2.1
    exposedAvailable exposedClosed middleStored exposedAnnotated
  have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) required headEffects.2.1 headEffects.2.2.1
    (by intro _ _ _; trivial) exposedAvailable
  exact ⟨value, before, exposed, middle, result, after, built, head, required, annotations.1, annotations.2,
    effects.2.1, effects.2.2.1, effects.2.2.2.2, resultClosed, SourceEqualityRequiredWorkerComplete.node_stable required⟩

/-- An earlier reserved binder with no complete payload retains its exact pending state. -/
theorem pending_identity_binder [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (state : State Symbol Guard) (facts : Facts state) (stored : MuStored valid state)
    (entry : Interned InternedBinderProtocol.NodeKey)
    (reserved : state.nodes.table (muKey (Symbol := Symbol) (Guard := Guard) (.reference .depth) (.reference (.uninterned 0))) = some entry)
    (unfinished : state.nodeRecords (muKey (Symbol := Symbol) (Guard := Guard) (.reference .depth) (.reference (.uninterned 0))) = none) :
    InternedFreshOrdinaryConstruction.build (.binder false (.var 0)) [] state =
      .pending (muKey (Symbol := Symbol) (Guard := Guard) (.reference .depth) (.reference (.uninterned 0))) state ∧
    MuStored valid state ∧ ∀ result after,
      InternedFreshOrdinaryConstruction.build (.binder false (.var 0)) [] state ≠ .done result after := by
  have checked := SourceCurrentHereditaryConstruction.build valid (.binder false (.var 0)) [] state facts
    (by intro _ impossible; cases impossible) (by simp [Allowed]) (by intro _ impossible; cases impossible) stored
  have pending : InternedFreshOrdinaryConstruction.build (.binder false (.var 0)) [] state =
      .pending (muKey (Symbol := Symbol) (Guard := Guard) (.reference .depth) (.reference (.uninterned 0))) state := by
    simp only [InternedFreshOrdinaryConstruction.build, List.getElem?_cons_zero, Option.getD_some,
      Outcome.bind, InternedNestedConstruction.work, withoutSelfReference, run,
      InternedFreshOrdinaryConstruction.ordinaryLevel, Value.depth, Value.free,
      InternedFreshOrdinaryConstruction.freeBound, Nat.max_self,
      InternedNestedConstruction.request, reserved, unfinished]
  refine ⟨pending, ?_, ?_⟩
  · simpa only [pending, Outcome.state] using checked.stored
  · intro result after done
    rw [pending] at done
    cases done

local notation "CurrentSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "CurrentGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Required results feed the exact next Merge reads without a global guard-heap premise. -/
theorem actual_required_then_merge [DecidableEq CurrentSymbol] [DecidableEq (EdgeKey CurrentSymbol CurrentGuard)]
    (valid : CurrentGuard → Prop) {clear : CurrentGuard → Bool} {top : CurrentGuard} (topValid : valid top)
    {paths : List (List Int)} {values results : List (Value CurrentSymbol CurrentGuard)}
    {input output : Value CurrentSymbol CurrentGuard} {before middle after : State CurrentSymbol CurrentGuard}
    {memo saved : SourceCurrentMemoMergeGraph.Memo CurrentSymbol CurrentGuard}
    {globals interim final : EndpointMemoGateTrace.Memos}
    (required : SourceCurrentRequiredQueryMemos.RequireAllReads paths values results before middle globals interim)
    (merged : SourceCurrentMemoMergeQueryMemos.CallReads clear top input middle memo output after saved interim final)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (available : Values before values) (closed : MergedColdReaderClosedInputs.ClosedValues values)
    (stored : MuStored valid before) (annotated : ∀ value ∈ values, Annotated valid value)
    (physical : SourceCurrentMemoMergeEffects.Stored before memo)
    (mergeStored : SourceCurrentHereditaryMerge.Stored valid memo) (selected : input ∈ results) :
    MuStored valid middle ∧ SourceCurrentMemoMergeEffects.Effect before after ∧
      SourceCurrentMemoMergeEffects.Stored after saved ∧ SourceCurrentHereditaryMerge.Stored valid saved ∧ Annotated valid output := by
  obtain ⟨middleStored, resultAnnotations⟩ := SourceCurrentHereditaryRequiredMerge.requireAll valid required semantic costs available closed stored annotated
  have physicalRequired : Keeps before middle ∧ SemanticReady middle ∧ InternedFreshOrdinaryCostHeap.Heap middle ∧
      SourceEqualityAnnotationHeap.Heap (fun _ => True) middle ∧ Values middle results := by
    cases compiled : SourceEqualityNeeded.build paths with
    | node entries =>
        simp only [SourceCurrentRequiredQueryMemos.RequireAllReads, compiled] at required
        obtain ⟨actual, _reads⟩ := required
        exact SourceCurrentRequiredHeapEffects.children (fun _ => True) actual semantic costs (by intro _ _ _; trivial) available
  obtain ⟨effect, physicalAfter, storedAfter, outputAnnotated⟩ := SourceCurrentHereditaryRequiredMerge.merge valid topValid merged
    physicalRequired.2.1 physicalRequired.2.2.1 (physical.grows physicalRequired.1) mergeStored
    (physicalRequired.2.2.2.2 input selected) (resultAnnotations input selected)
  have prefixEffect : SourceCurrentMemoMergeEffects.Effect before middle :=
    ⟨physicalRequired.1, physicalRequired.2.1, physicalRequired.2.2.1⟩
  exact ⟨middleStored, prefixEffect.trans effect, physicalAfter, storedAfter, outputAnnotated⟩

#print axioms constructed_head_required
#check @constructed_head_required
#print axioms pending_identity_binder
#check @pending_identity_binder
#print axioms actual_required_then_merge
#check @actual_required_then_merge
end MicroCFTA.ConstructionReviewKernels
