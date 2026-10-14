import MicroCFTA.InternedPreparedCostRetention
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

/-!
# Strict rank decrease for actual repaired open Mu unfolding

The original minimum-cost witness loses its outer Mu frame. Prepared-plan
retention keeps its external occurrence at no greater remaining cost.
Exact execution costs transfer that bound to the actual returned value.
Finite unfolding retains every cache invariant for subsequent calls.
-/
namespace MicroCFTA.InternedFreshOrdinaryUnfoldRank
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreeOccurrenceRank
open InternedFreshOrdinaryContext
open InternedBinderProtocol (Reference NodeKey)

/-- Every completed actual repaired unfolding of an open Mu strictly decreases minimum occurrence rank. -/
theorem unfold_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state captures) (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (heap : InternedFreshOrdinaryCostHeap.Heap state)
    (available : Available state (.mu entry body depth ordinary))
    (opened : (Value.mu entry body depth ordinary).free ≠ [])
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done value after) :
    rank value < rank (.mu entry body depth ordinary) := by
  let environment : InternedStoredSubstitution.Environment Symbol Guard :=
    fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none
  have bodyAvailable := available.children body (by simp [children])
  have replacements : InternedStoredSubstitution.Replacements state environment := by
    intro name replacement found
    dsimp only [environment] at found
    split at found
    · cases found; exact available
    · contradiction
  have agrees := (InternedFreshOrdinaryStoredSubstitution.execute_costs body environment state context cached heap
    bodyAvailable replacements).result value after done
  obtain ⟨name, occurrence⟩ :=
    (rank_spec (.mu entry body depth ordinary) state context.normal.facts.coherent available opened).1
  obtain ⟨prior, ⟨present, different⟩, equal⟩ :=
    (InternedFreshOrdinaryCostHeap.mu_cost_iff entry body depth ordinary name _).mp occurrence
  obtain ⟨count, bound, retained⟩ := InternedPreparedCostRetention.unfold_retains body
    (.mu entry body depth ordinary) (.interned entry.identity) state context.normal bodyAvailable available opened
    name prior different present
  have actual := (agrees name count).mpr retained
  have minimum := InternedFreeOccurrenceNormalization.rank_le_cost value name count actual
  omega

/-- Actual open Mu unfolding completes, decreases rank, and retains all caches for the next call. -/
theorem unfold_complete_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state captures) (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (heap : InternedFreshOrdinaryCostHeap.Heap state) (covered : Covered [] state)
    (available : Available state (.mu entry body depth ordinary))
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ value after, InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done value after ∧
      Context after captures ∧ InternedFreshOrdinaryDepthHeap.Heap after ∧ Covered [] after ∧
      InternedFreshOrdinaryCostHeap.Heap after ∧ Available after value ∧ Grows state after ∧
      Extends state.nodes.issued after.nodes.issued ∧ rank value < rank (.mu entry body depth ordinary) := by
  obtain ⟨value, after, done, afterContext, afterCached, afterCovered, afterHeap, afterAvailable, growth, history⟩ :=
    InternedFreshOrdinaryStoredSubstitution.unfold_complete_costs (.mu entry body depth ordinary)
      state context cached heap covered available
  exact ⟨value, after, done, afterContext, afterCached, afterCovered, afterHeap, afterAvailable, growth, history,
    unfold_decreases entry body depth ordinary state context cached heap available opened value after done⟩

/-- Original empty-cache source execution derives every premise of general repaired open Mu progress. -/
theorem closed_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (InternedFreshOrdinaryConstruction.build expression [] empty).state.nodeRecords key =
      some (.mu entry body depth ordinary)) (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ value after, InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary)
        (InternedFreshOrdinaryConstruction.build expression [] empty).state = .done value after ∧
      Context after [] ∧ InternedFreshOrdinaryDepthHeap.Heap after ∧ Covered [] after ∧
      InternedFreshOrdinaryCostHeap.Heap after ∧ Available after value ∧
      rank value < rank (.mu entry body depth ordinary) := by
  obtain ⟨source, state, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have context : Context state [] := by simpa only [built, Outcome.state] using empty_context.build expression
  have cached : InternedFreshOrdinaryDepthHeap.Heap state := by
    simpa only [built, Outcome.state] using
      (InternedRecordDepthExecution.build_depth expression [] empty empty_context InternedFreshOrdinaryDepthHeap.empty_heap).heap
  have heap : InternedFreshOrdinaryCostHeap.Heap state := by
    simpa only [built, Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression
  have available : Available state (.mu entry body depth ordinary) :=
    context.normal.facts.cached.nodes key _ (by simpa only [built, Outcome.state] using stored)
  obtain ⟨value, after, done, afterContext, afterCached, afterCovered, afterHeap, afterAvailable, _, _, smaller⟩ :=
    unfold_complete_decreases entry body depth ordinary state context cached heap
      (InternedFreshOrdinaryCoverage.closed_covered expression source state built) available opened
  exact ⟨value, after, by simpa only [built, Outcome.state] using done,
    afterContext, afterCached, afterCovered, afterHeap, afterAvailable, smaller⟩

end MicroCFTA.InternedFreshOrdinaryUnfoldRank
