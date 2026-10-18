import MicroCFTA.SourceCurrentRetainedMuDirectedCase
import MicroCFTA.SourceCurrentNativeMuGrowthExecution

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.RetainedDirectedKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (unfold)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuGrowthHistory (Path)
open SourceCurrentRetainedMuDirectedCase (Generated)

private def body : Syntax Nat Bool := .node [.mk 7 false [.var 0]]
private def author : Syntax Nat Bool := .binder false body
private def requesterBody : Syntax Nat Bool := .union [body,.empty]
private def observed := build author [] empty
private def reader := observed.state
private def value : Value Nat Bool := match observed with | .done result _ => result | .pending .. => .empty
private def used : Value Nat Bool → Prop
  | .mu entry body _ _ => .interned entry.identity ∈ body.free
  | _ => False
private theorem built : build author [] empty = .done value reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed author value reader built
private theorem initial : Context reader [] :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic [] (by intro input member; cases member),ready.semantic.2⟩
private theorem historical : Nonempty (Path empty reader) := by
  simpa only [built,Outcome.state] using SourceCurrentNativeMuGrowthExecution.build_path author [] empty
    SourceCurrentConstrainedCapSourceHistory.empty_context
private theorem actual : build (.binder false requesterBody) [] reader = .done value reader := by cbv
private theorem checked : requesterBody ≠ body ∧ used value ∧ Ready reader ∧
    build author [] empty = .done value reader ∧
    build (.binder false requesterBody) [] reader = .done value reader ∧
    ∃ left middle right final,
      unfold value reader = .done left middle ∧ unfold value final = .done left final ∧
      Keeps reader middle ∧ Keeps middle final ∧
      Available final left ∧ Available final right ∧ Generated final left right ∧ Generated final right left := by
  refine ⟨?_,?_,ready,built,actual,?_⟩
  · intro impossible; cases impossible
  · cbv
    exact List.mem_cons_self
  · obtain ⟨depth,ordinary,entry,stored,event,left,middle,right,final,selected,returned,written,
      keySame,valueSame,missing,writerPrefix,depthPath,ordinaryPath,bodyPath,eventGrowth,
      firstDone,secondDone,firstWarm,secondWarm,epsilon,finalEpsilon,firstKept,secondKept,
      leftAvailable,rightAvailable,generated,reverse⟩ :=
      SourceCurrentRetainedMuDirectedCase.binder false requesterBody [] reader value reader initial actual
        reader (SourceEqualityRequiredCache.pure_keeps reader ready) (Classical.choice historical)
    have same : value = .mu entry stored depth ordinary := returned
    exact ⟨left,middle,right,final,same ▸ firstDone,same ▸ firstWarm,
      firstKept,secondKept,leftAvailable,rightAvailable,generated,reverse⟩

/-- A genuinely used earlier Mu writer supplies both source-generator directions for a different warm requester. -/
theorem witness : requesterBody ≠ body ∧ used value ∧ Ready reader ∧
    build author [] empty = .done value reader ∧
    build (.binder false requesterBody) [] reader = .done value reader ∧
    ∃ left middle right final,
      unfold value reader = .done left middle ∧ unfold value final = .done left final ∧
      Keeps reader middle ∧ Keeps middle final ∧
      Available final left ∧ Available final right ∧ Generated final left right ∧ Generated final right left := checked

end MicroCFTA.RetainedDirectedKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.RetainedDirectedKernels.witness
#print MicroCFTA.RetainedDirectedKernels.witness
#print axioms MicroCFTA.RetainedDirectedKernels.witness
