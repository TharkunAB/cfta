import MicroCFTA.SourceCurrentNativeBinderExecution
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
namespace MicroCFTA.NativeBinderExecutionKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open SourceCurrentConstrainedCapSourceHistory (Context)

/-- Closed source completion supplies the actual binder and raw ordinary callback without a future run premise. -/
theorem closed [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard) :
    ∃ value after depth afterDepth ordinary cut raw middle,
      build (.binder smart body) [] empty = .done value after ∧
      InternedFreshOrdinaryFacts.callback body [] .depth empty = .done depth afterDepth ∧
      InternedFreshOrdinaryFacts.callback body [] (.uninterned (ordinaryLevel depth)) afterDepth =
        .done ordinary cut ∧
      build body [.reference (.uninterned (ordinaryLevel depth))] afterDepth = .done raw middle ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) middle = (ordinary,cut) ∧
      Context after [] ∧ Grows middle after ∧ Extends middle.nodes.issued after.nodes.issued ∧
      Available after depth ∧ Available after ordinary := by
  obtain ⟨value, after, actual⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete (.binder smart body)
  obtain ⟨depth, afterDepth, ordinary, cut, raw, middle, depthDone, ordinaryDone, _requestDone,
    _depthContext, _cutContext, finalContext, rawDone, filtered, _rawContext, growth, history,
    depthAvailable, ordinaryAvailable⟩ := SourceCurrentNativeBinderExecution.decompose smart body [] empty
      value after SourceCurrentConstrainedCapSourceHistory.empty_context actual
  exact ⟨value, after, depth, afterDepth, ordinary, cut, raw, middle, actual, depthDone, ordinaryDone,
    rawDone, filtered, finalContext, growth, history, depthAvailable, ordinaryAvailable⟩
end MicroCFTA.NativeBinderExecutionKernels
#check @MicroCFTA.NativeBinderExecutionKernels.closed
#print MicroCFTA.NativeBinderExecutionKernels.closed
#print axioms MicroCFTA.NativeBinderExecutionKernels.closed
