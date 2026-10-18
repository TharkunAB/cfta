import MicroCFTA.SourceCurrentZeroDepthReaderSupport

set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.ZeroDepthSupportReview
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (unfold)
open InternedStoredPlanBinderDepth (valueDepth)
open SourceCurrentObservationReaderSupport (WarmSupport Preparation)
open SourceEqualityRequiredCache (Ready Keeps)
open InternedFreshMuUnfoldBudget (Settled)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def nested : Syntax Nat Bool :=
  .binder true (.node [.mk 7 false [], .mk 8 false [.var 0]])
private def source : Syntax Nat Bool :=
  .binder false (.node [.mk 9 false [.union [nested, .var 0]]])
private def built := build source [] empty
private def root := value built
private def before := built.state
private def body : Value Nat Bool :=
  match root with | .mu _ body .. => body | _ => .empty
private def choice : Value Nat Bool := (children body)[0]?.getD .empty
private def recursive : Value Nat Bool :=
  match choice with | .union _ members .. => members[0]?.getD .empty | _ => .empty

private theorem actual : build source [] empty = .done root before := by cbv
private theorem ready : Ready before := SourceEqualityRequiredCache.constructed source root before actual
private theorem root_available : Available before root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result root before actual
private theorem body_available : Available before body := root_available.children body
  (List.mem_of_getElem? (show (children root)[0]? = some body by cbv))
private theorem choice_available : Available before choice := body_available.children choice
  (List.mem_of_getElem? (show (children body)[0]? = some choice by cbv))
private theorem recursive_available : Available before recursive := choice_available.children recursive
  (List.mem_of_getElem? (show (children choice)[0]? = some recursive by cbv))
private theorem cold : ¬ Settled before recursive := by
  rintro ⟨result, done⟩
  have next := congrArg (fun outcome => outcome.state.nodes.next) done
  have different : (unfold recursive before).state.nodes.next ≠ before.nodes.next := by
    cbv <;> intro impossible <;> cases impossible
  exact different next

/-- Actual preparation supports an open node and union that contain a cold closed recursive Mu. -/
theorem witness :
    build source [] empty = .done root before ∧ Ready before ∧
    Available before body ∧ body.free ≠ [] ∧ valueDepth body = 0 ∧
    Available before choice ∧ choice.free ≠ [] ∧ valueDepth choice = 0 ∧
    Available before recursive ∧ recursive.free = [] ∧ ¬ Settled before recursive ∧
    ∃ after, Preparation before after ∧ Keeps before after ∧ after ≠ before ∧
      WarmSupport after (fun value => Available after value ∧ valueDepth value = 0) ∧
      Available after body ∧ Available after choice ∧
      ∃ result, unfold recursive after = .done result after := by
  refine ⟨actual, ready, body_available, ?_, ?_, choice_available, ?_, ?_,
    recursive_available, ?_, cold, ?_⟩
  · cbv <;> intro impossible <;> cases impossible
  · cbv
  · cbv <;> intro impossible <;> cases impossible
  · cbv
  · cbv
  · obtain ⟨after, actual, kept, warm⟩ := SourceCurrentZeroDepthReaderSupport.prepare before ready
    have settled := warm.2.2 recursive ⟨kept.available recursive recursive_available, by cbv⟩
    refine ⟨after, actual, kept, ?_, warm, kept.available body body_available,
      kept.available choice choice_available, settled⟩
    intro same
    exact cold (same ▸ settled)

end MicroCFTA.ZeroDepthSupportReview

set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.ZeroDepthSupportReview.witness
#print MicroCFTA.ZeroDepthSupportReview.witness
#print axioms MicroCFTA.ZeroDepthSupportReview.witness
