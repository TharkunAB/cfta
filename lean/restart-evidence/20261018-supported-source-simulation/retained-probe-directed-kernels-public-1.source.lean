import MicroCFTA.SourceCurrentRetainedProbeSchedule
import MicroCFTA.SourceCurrentNativeMuGrowthExecution

namespace MicroCFTA.RetainedProbeDirectedKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuGrowthHistory (Path)

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def body : Syntax Nat Bool := .node [.mk 7 false []]
private def author : Syntax Nat Bool := .binder false body
private def requesterBody : Syntax Nat Bool := .union [body,.empty]
private def observed := build author [] empty
private def reader := observed.state
private def value : Value Nat Bool := match observed with | .done result _ => result | .pending .. => .empty
private theorem built : build author [] empty = .done value reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed author value reader built
private theorem initial : Context reader [] :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic [] (by intro input member; cases member),ready.semantic.2⟩
private theorem historical : Nonempty (Path empty reader) := by
  simpa only [built,Outcome.state] using SourceCurrentNativeMuGrowthExecution.build_path author [] empty
    SourceCurrentConstrainedCapSourceHistory.empty_context
private theorem actual : build (.binder false requesterBody) [] reader = .done value reader := by cbv
private theorem checked : requesterBody ≠ body ∧ Ready reader ∧
    build author [] empty = .done value reader ∧
    build (.binder false requesterBody) [] reader = .done value reader ∧
    SourceCurrentRetainedProbeSchedule.Seed false requesterBody [] reader value reader reader := by
  refine ⟨?_,ready,built,actual,?_⟩
  · intro impossible; cases impossible
  · exact SourceCurrentRetainedProbeSchedule.binder false requesterBody [] reader value reader initial actual
      reader (SourceEqualityRequiredCache.pure_keeps reader ready) (Classical.choice historical)

/-- A different warm requester recovers the older actual writer and constructs its seed schedule. -/
theorem witness : requesterBody ≠ body ∧ Ready reader ∧
    build author [] empty = .done value reader ∧
    build (.binder false requesterBody) [] reader = .done value reader ∧
    SourceCurrentRetainedProbeSchedule.Seed false requesterBody [] reader value reader reader := checked

end MicroCFTA.RetainedProbeDirectedKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.RetainedProbeDirectedKernels.witness
#print MicroCFTA.RetainedProbeDirectedKernels.witness
#print axioms MicroCFTA.RetainedProbeDirectedKernels.witness
