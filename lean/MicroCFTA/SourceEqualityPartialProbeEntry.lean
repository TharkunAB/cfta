import MicroCFTA.SourceEqualityProbePass
import MicroCFTA.SourceEqualityPartialStepProofs

/-!
# Actual native pass outputs supply the outer Mu branch

Original source construction derives both filtered probes. The complete
guarded native equality pass retains them. Every available Mu at its returned
heap therefore executes the actual outer reconstruction with smart cleanup
and unchanged full native state.
-/
namespace MicroCFTA.SourceEqualityPartialProbeEntry
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedFreshOrdinaryProbeHeap (Heap)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialWorker
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin

/-- Original completed closed construction derives the probe invariant. -/
theorem constructed [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state) : Heap state := by
  simpa only [done, InternedNestedConstruction.Outcome.state] using InternedFreshOrdinaryProbeHeap.closed_heap expression

/-- The complete concrete native pass supplies exact outer Mu execution at its actual returned scope. -/
theorem guarded_mu [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {edge result : EdgeValue Symbol Guard} {inherited : SourceEqualityPrecheck.Constraint} {before after : NativeState width Symbol Guard}
    (trace : SourceEqualityPCSNativeEdge.Execution edge inherited before result after)
    (ready : IdleReady top conjoin before) (resident : InternedEdgeResidency.EdgeResident before.machine.heap edge)
    (closed : MergedColdReaderClosedInputs.ClosedValues edge.children) (heap : Heap before.machine.heap) :
    Heap after.machine.heap ∧ IdleReady top conjoin after ∧
      ∀ entry body depth ordinary, Available after.machine.heap (.mu entry body depth ordinary) →
        ∀ g e p h c n fuel payload,
          SourceEqualityPartialWorker.run g e p h c n (fuel + 1) payload (.mu entry body depth ordinary) after =
            .done (.ok (cleanup (.mu entry body depth ordinary))) after ∧
          Available after.machine.heap (cleanup (.mu entry body depth ordinary)) ∧
          ∀ (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol),
            InternedGuardedLanguage.meaning holds ambient (cleanup (.mu entry body depth ordinary)) =
              InternedGuardedLanguage.meaning holds ambient (.mu entry body depth ordinary) := by
  have finalHeap := SourceEqualityProbePass.guarded_edge_heap trace ready resident closed heap
  have final := SourceEqualityGuardedEdgeEffects.effects trace ready
    (ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident) closed
  refine ⟨finalHeap, final.1, ?_⟩
  intro entry body depth ordinary available g e p h c n fuel payload
  have clean := InternedFreshOrdinaryProbeHeap.resident after.machine.heap finalHeap entry body depth ordinary available
  have coherent := final.1.semantic.ready.semantic.1.normal.facts.coherent
  have done := SourceEqualityMuReconstruction.completed entry body depth ordinary after.machine.heap coherent available clean
  refine ⟨?_, InternedConstructionProvenance.cleanup_available _ available, ?_⟩
  · simp only [SourceEqualityPartialWorker.run, step, done, SourceEqualityPartialStepProofs.advance_self]
  · intro holds ambient
    exact InternedGuardedLanguage.cleanup_exact holds ambient _ after.machine.heap coherent available

end MicroCFTA.SourceEqualityPartialProbeEntry
