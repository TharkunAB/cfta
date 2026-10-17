import MicroCFTA.SourceCurrentConstrainedCapRequired
import MicroCFTA.InternedFreshOrdinaryCosts
import MicroCFTA.InternedFreshOrdinarySourceFreeNames

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.ConstrainedCapRequiredKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values)
open SourceEqualityAnnotationLanguage SourceEqualityAnnotationConstruction
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityRequiredGraph
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentConstrainedCap (Cap Edge)
variable {Symbol Guard : Type}

/-- Closed hereditary syntax constructs its own actual head and required result at every cap depth. -/
theorem constructed_head_required [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (expression : Syntax Symbol Guard) (allowed : Allowed valid expression) (needed : SourceEqualityNeeded.Needed)
    (capDepth : Nat) :
    ∃ value before exposed middle result after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value before ∧
      SourceEqualityRequiredHead.Head value before exposed middle ∧
      RequireNode needed exposed middle result after ∧
      MuStored valid after ∧ Cap valid capDepth result ∧ SemanticReady after ∧
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
  obtain ⟨middleStored, exposedBound⟩ := SourceCurrentConstrainedCapExposure.head valid capDepth head semantic.ready
    available closed (Cap.plain capDepth annotated) stored
  have headEffects := SourceCurrentRequiredHeapEffects.head (fun _ => True) head semantic costs (by intro _ _ _; trivial) available
  obtain ⟨result, after, actual, _, _, resultClosed⟩ := SourceEqualityRequiredComplete.complete needed exposed middle
    headEffects.1.ready exposedAvailable exposedClosed
  have bounded := SourceCurrentConstrainedCapRequired.node valid capDepth actual headEffects.2.1 headEffects.2.2.1
    exposedAvailable exposedClosed middleStored exposedBound
  have effects := SourceCurrentRequiredHeapEffects.node (fun _ => True) actual headEffects.2.1 headEffects.2.2.1
    (by intro _ _ _; trivial) exposedAvailable
  exact ⟨value, before, exposed, middle, result, after, built, head, actual, bounded.1, bounded.2,
    effects.2.1, effects.2.2.1, effects.2.2.2.2, resultClosed, SourceEqualityRequiredWorkerComplete.node_stable actual⟩

/-- A second request uses the first actual returned cache and its derived cap and physical facts. -/
theorem two_required [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (capDepth : Nat)
    (firstNeeded secondNeeded : SourceEqualityNeeded.Needed) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (available : Available before value)
    (closed : value.free = []) (stored : MuStored valid before) (bounded : Cap valid capDepth value) :
    ∃ first middle second after,
      RequireNode firstNeeded value before first middle ∧ RequireNode secondNeeded first middle second after ∧
      MuStored valid middle ∧ Cap valid capDepth first ∧ MuStored valid after ∧ Cap valid capDepth second ∧
      Keeps before after ∧ Available after second ∧ second.free = [] ∧
      SourceEqualityRequiredWorkerComplete.StableRun
        (fun fuel headFuel => SourceEqualityRequiredWorker.require fuel headFuel secondNeeded first middle) second after := by
  obtain ⟨first, middle, firstActual, firstKeeps, firstAvailable, firstClosed⟩ :=
    SourceEqualityRequiredComplete.complete firstNeeded value before semantic.ready available closed
  obtain ⟨middleStored, firstBound⟩ := SourceCurrentConstrainedCapRequired.node valid capDepth firstActual
    semantic costs available closed stored bounded
  have firstEffects := SourceCurrentRequiredHeapEffects.node (fun _ => True) firstActual semantic costs
    (by intro _ _ _; trivial) available
  obtain ⟨second, after, secondActual, secondKeeps, secondAvailable, secondClosed⟩ :=
    SourceEqualityRequiredComplete.complete secondNeeded first middle firstKeeps.ready firstAvailable firstClosed
  obtain ⟨afterStored, secondBound⟩ := SourceCurrentConstrainedCapRequired.node valid capDepth secondActual
    firstEffects.2.1 firstEffects.2.2.1 firstAvailable firstClosed middleStored firstBound
  exact ⟨first, middle, second, after, firstActual, secondActual, middleStored, firstBound, afterStored, secondBound,
    firstKeeps.trans secondKeeps, secondAvailable, secondClosed, SourceEqualityRequiredWorkerComplete.node_stable secondActual⟩

private theorem identity_children [DecidableEq (EdgeKey Symbol Guard)] (index : Nat)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) :
    RequireChildren [] index values state values state := by
  induction values generalizing index with
  | nil => exact .nil
  | cons value rest ih => exact .unselected index rfl (ih (index + 1))

/-- A kept row can have an arbitrary guard above a hereditary frontier, including canonical hits. -/
theorem kept_arbitrary_guard [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (original : EdgeValue Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : InternedFreshOrdinaryCostHeap.Heap before) (resident : InternedEdgeResidency.EdgeResident before original)
    (closed : MergedColdReaderClosedInputs.ClosedValues original.children) (stored : MuStored valid before)
    (frontier : ∀ child ∈ original.children, Annotated valid child) :
    ∃ result after,
      RequireRows [] [original] before [result] after ∧ MuStored valid after ∧ Edge valid 1 result ∧
      result.entry.key.symbol = original.entry.key.symbol ∧ result.entry.key.constraint = original.entry.key.constraint ∧
      result.children = original.children := by
  let result := (run (makeEdge original.entry.key.symbol original.entry.key.constraint original.children) before).1
  let after := (run (makeEdge original.entry.key.symbol original.entry.key.constraint original.children) before).2
  have actual : RequireRows [] [original] before [result] after :=
    .kept (by simp [SourceEqualityNeeded.fits, SourceEqualityNeeded.maxIndex])
      (identity_children 0 original.children before) rfl .nil
  have preserved := SourceCurrentConstrainedCapRequired.rows valid 1 actual semantic costs
    (by intro edge member; exact (List.mem_singleton.mp member) ▸ resident)
    (by intro edge member; exact (List.mem_singleton.mp member) ▸ closed) stored
    (by intro edge member; cases List.mem_singleton.mp member; exact fun child present => Cap.plain 0 (frontier child present))
  have facts := semantic.ready.semantic.1.normal.facts
  have available := facts.cached.edges original.entry.key original resident
  have key := InternedOrdinaryAbsenceReplay.makeEdge_key original.entry.key.symbol original.entry.key.constraint original.children before facts.coherent
  have children := InternedShallowValues.makeEdge_children original.entry.key.symbol original.entry.key.constraint original.children before facts.coherent facts.cached available
  exact ⟨result, after, actual, preserved.1, preserved.2 result List.mem_cons_self,
    (by simpa only [result] using congrArg EdgeKey.symbol key),
    (by simpa only [result] using congrArg EdgeKey.constraint key), children⟩

#print axioms constructed_head_required
#check @constructed_head_required
#print axioms two_required
#check @two_required
#print axioms kept_arbitrary_guard
#check @kept_arbitrary_guard
end MicroCFTA.ConstrainedCapRequiredKernels
