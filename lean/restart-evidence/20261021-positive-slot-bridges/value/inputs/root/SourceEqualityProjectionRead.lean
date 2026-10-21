import MicroCFTA.SourceEqualityRequiredHeadLanguage

/-!
# Actual row reads for closed path projection

A row read retains its actual returned cache. It does not construct a node.
A temporary node request is only a proof of the row language law.
-/
namespace MicroCFTA.SourceEqualityProjectionRead
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open InternedGuardedLanguage (meaning)
open MergedColdInterpretation (EdgeMeaning)

/-- A completed source nodeEdges request, without a node construction. -/
inductive Read [DecidableEq (EdgeKey Symbol Guard)] :
    Value Symbol Guard → State Symbol Guard → List (EdgeValue Symbol Guard) → State Symbol Guard → Prop where
  | done (fuel : Nat)
      (completed : MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done edges after) :
      Read value before edges after

/-- Complete row reads have the same edges and full cache at every successful bound. -/
theorem Read.unique [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before firstAfter secondAfter : State Symbol Guard}
    {first second : List (EdgeValue Symbol Guard)}
    (left : Read value before first firstAfter) (right : Read value before second secondAfter) :
    first = second ∧ firstAfter = secondAfter := by
  cases left with
  | done firstFuel firstDone =>
      cases right with
      | done secondFuel secondDone =>
          have firstStable := MergedFreshOrdinaryColdReplay.nodeEdges_stable firstFuel secondFuel value before
            (by simp only [firstDone, MergedSourceExposure.Finished])
          have secondStable := MergedFreshOrdinaryColdReplay.nodeEdges_stable secondFuel firstFuel value before
            (by simp only [secondDone, MergedSourceExposure.Finished])
          rw [Nat.add_comm secondFuel firstFuel] at secondStable
          exact MergedSourceExposure.Result.done.inj
            ((firstStable.trans firstDone).symm.trans (secondStable.trans secondDone))

/-- Every closed available operand has a finite row read with complete cache effects. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) :
    ∃ edges after, Read value before edges after ∧ Keeps before after ∧
      SemanticReady after ∧ Edges after edges ∧ ClosedEdges edges := by
  obtain ⟨fuel, edges, after, done, heap, covered, depth, growth, history, resident, closedEdges, _⟩ :=
    MergedFreshOrdinaryColdTermination.read_closed value before semantic.ready.semantic
      semantic.ready.covered semantic.ready.depth available closed
  refine ⟨edges, after, .done fuel done, ⟨⟨heap, covered, depth⟩, growth, history⟩,
    ⟨⟨heap, covered, depth⟩, ?_, ?_⟩, resident, closedEdges⟩
  · simpa only [done, MergedSourceExposure.Result.state] using
      MergedFreshOrdinaryGuardedEffects.nodeEdges_heap fuel value before semantic.ready.semantic
        semantic.ready.covered semantic.guarded available closed
  · simpa only [done, MergedSourceExposure.Result.state] using
      MergedFreshOrdinaryBudgetEffects.nodeEdges_heap fuel value before semantic.ready.semantic
        semantic.ready.covered semantic.budget available closed

/-- Any successful row graph derives all intermediate invariants. -/
theorem Read.verified [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : Read value before edges after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) :
    Keeps before after ∧ SemanticReady after ∧ Edges after edges ∧ ClosedEdges edges := by
  obtain ⟨actual, final, completed, keeps, ready, resident, closedEdges⟩ := complete value before semantic available closed
  obtain ⟨rfl, rfl⟩ := completed.unique trace
  exact ⟨keeps, ready, resident, closedEdges⟩

/-- The returned rows have exactly the operand's independent guarded language. -/
theorem Read.exact [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : Read value before edges after) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    (∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term) ↔ meaning holds ambient value term := by
  have checked := trace.verified semantic available closed
  cases trace with
  | done fuel completed =>
      have head : SourceEqualityRequiredHead.Head value before (run (makeNode edges) after).1
          (run (makeNode edges) after).2 := .read fuel edges after completed rfl
      have rebuilt := MergedColdInterpretation.makeNode_exact after checked.2.1.ready.semantic.1.normal.facts
        (meaning holds ambient) edges checked.2.2.1 holds (InternedGuardedLanguage.laws holds ambient) term
      exact rebuilt.symm.trans (SourceEqualityRequiredHeadLanguage.head_exact head semantic available closed holds ambient term)

end MicroCFTA.SourceEqualityProjectionRead
