import MicroCFTA.SourceCurrentTrackedFilteredNodeFusion
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.BinderContractCounterexample
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work finish)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceEqualityRequiredCache (Ready Keeps)
open InternedStoredMuOrigins (Normal)

private def value (call : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match call with | .done result _ => result | .pending .. => .empty
private def body : Syntax Nat Bool := .node [.mk 7 false [.var 1,.var 2]]
private def different : Syntax Nat Bool := .node [.mk 7 false [.var 1],.mk 7 false [.var 2]]
private def captures : List (Value Nat Bool) := [.reference (.uninterned 10),.reference (.uninterned 11)]
private def depthCall := callback body captures .depth empty
private def depth := value depthCall
private def cut := depthCall.state
private def ordinary := depth
private def key := muKey depth ordinary
private def reserved := Cache.intern cut.nodes key
private def entry := reserved.1
private def allocated := {cut with nodes := reserved.2}
private def bodyCall := callback different captures (.interned entry.identity) allocated
private def storedBody := value bodyCall
private def afterBody := bodyCall.state
private def candidate := Value.mu entry storedBody depth ordinary
private def reader := (InternedNestedRequestFacts.complete false entry storedBody depth ordinary afterBody).state
private theorem depth_done : callback body captures .depth empty = .done depth cut := by cbv
private theorem body_done : callback different captures (.interned entry.identity) allocated = .done storedBody afterBody := by cbv
private theorem complete_done : InternedNestedRequestFacts.complete false entry storedBody depth ordinary afterBody = .done candidate reader := by cbv

private theorem captures_available (state : State Nat Bool) : InternedNestedProvenance.Values state captures := by
  intro child member
  have choices : child = .reference (.uninterned 10) ∨ child = .reference (.uninterned 11) := by
    simpa only [captures,List.mem_cons,List.not_mem_nil,or_false] using member
  rcases choices with rfl | rfl <;> exact InternedNestedProvenance.ordinary_available state _
private theorem initial_context : Context empty captures :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap captures
    (captures_available empty),InternedFreshOrdinaryDepthHeap.empty_heap⟩
private theorem cut_context : Context cut captures := by
  simpa only [depth_done,Outcome.state] using initial_context.callback body .depth (InternedNestedProvenance.depth_available empty)
private theorem allocated_context : Context allocated captures := cut_context.reserve key
private theorem argument_available : Available allocated (.reference (.interned entry.identity)) :=
  (InternedConstructionProvenance.reserve_available key cut cut_context.base.normal.facts.coherent cut_context.base.normal.facts.cached).2
private theorem body_context : Context afterBody captures := by
  simpa only [body_done,Outcome.state] using allocated_context.callback different (.interned entry.identity) argument_available
private theorem body_available : Available afterBody storedBody :=
  (InternedFreshOrdinaryFacts.callback_verified different captures (.interned entry.identity) allocated
    allocated_context.base.normal.facts (allocated_context.local _ argument_available).base.inputs).result storedBody afterBody body_done
private theorem depth_available : Available afterBody depth := by
  have first := (InternedFreshOrdinaryFacts.callback_verified body captures .depth empty initial_context.base.normal.facts
    (initial_context.local _ (InternedNestedProvenance.depth_available empty)).base.inputs).result depth cut depth_done
  have reserveGrowth : Grows cut allocated := ⟨extends_refl _,InternedBinderProtocol.intern_grows _ _,extends_refl _,extends_refl _⟩
  have reserveIssued := InternedFreshProbeKeys.intern_issued_extends cut.nodes key cut_context.base.normal.facts.coherent.valid.2
  have allocatedValue := first.grows cut allocated reserveGrowth reserveIssued
  have checked := InternedFreshOrdinaryFacts.callback_verified different captures (.interned entry.identity) allocated
    allocated_context.base.normal.facts (allocated_context.local _ argument_available).base.inputs
  simpa only [body_done,Outcome.state] using checked.available depth allocatedValue
private theorem stored_entry : afterBody.nodes.table key = some entry := by cbv
private theorem verified := InternedNestedRequestFacts.complete_verified false entry storedBody depth ordinary afterBody
  body_context.base.normal.facts stored_entry body_available depth_available depth_available
private theorem final_normal : Normal reader := by
  have normal := body_context.base.normal
  exact ⟨(by simpa only [complete_done,Outcome.state] using verified.facts),
    (by simpa only [complete_done,Outcome.state] using InternedLiveEdges.complete_live false entry storedBody depth ordinary afterBody normal.live),
    (by simpa only [complete_done,Outcome.state] using InternedUnionNormalForm.complete_flat false entry storedBody depth ordinary afterBody normal.flat),
    (by simpa only [complete_done,Outcome.state] using InternedNonemptyRecords.complete_nonempty false entry storedBody depth ordinary afterBody normal.proper),
    (by simpa only [complete_done,Outcome.state] using InternedUnionNonemptyMembers.complete_membersNonempty false entry storedBody depth ordinary afterBody normal.members)⟩
private theorem profile_correct : InternedFreshOrdinaryProfileHeap.Correct entry storedBody depth ordinary := by
  cbv
  exact ⟨Iff.rfl,fun _ => Iff.rfl⟩
private theorem free_correct : InternedFreshOrdinaryFreeHeap.Correct entry storedBody depth ordinary := by
  intro name
  cbv
  exact Iff.rfl
private theorem depth_correct : InternedFreshOrdinaryDepthHeap.Correct entry storedBody depth ordinary := by
  intro smart
  cases smart <;> constructor
  all_goals try {cbv}
  all_goals intro name; cbv; exact Iff.rfl
private theorem final_semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap reader := by
  refine ⟨⟨final_normal,(by intro value member; cases member),?_,?_⟩,?_⟩
  · simpa only [complete_done,Outcome.state] using InternedFreshOrdinaryProfileHeap.complete_heap false entry storedBody depth ordinary
      afterBody body_context.base.profiles profile_correct
  · simpa only [complete_done,Outcome.state] using InternedFreshOrdinaryFreeHeap.complete_heap false entry storedBody depth ordinary
      afterBody body_context.base.freeNames free_correct
  · simpa only [complete_done,Outcome.state] using InternedFreshOrdinaryDepthHeap.complete_heap false entry storedBody depth ordinary
      afterBody body_context.depth depth_correct
private theorem cut_covered : Covered [] cut :=
  InternedFreshOrdinaryCoverage.callback_covered body captures .depth empty empty_valid empty_correct.2 depth cut depth_done
private theorem final_covered : Covered [] reader := by
  have reservedCoverage := InternedNestedCoverage.reserve_covered key cut cut_covered
  have covered := InternedFreshOrdinaryCoverage.callback_covered different captures (.interned entry.identity) allocated
    allocated_context.base.normal.facts.coherent.valid reservedCoverage storedBody afterBody body_done
  exact InternedNestedCoverage.complete_covered false entry storedBody depth ordinary afterBody covered candidate reader complete_done
private theorem cut_open : InternedOpenDepthReadback.Heap cut := by
  simpa only [depth_done,Outcome.state] using (InternedOpenDepthExecution.callback_depth body captures .depth empty
    initial_context.base (InternedNestedProvenance.depth_available empty) initial_context.depth InternedOpenDepthReadback.empty_heap).heap
private theorem allocated_open : InternedOpenDepthReadback.Heap allocated := cut_open
private theorem body_open : InternedOpenDepthReadback.Heap afterBody := by
  simpa only [body_done,Outcome.state] using (InternedOpenDepthExecution.callback_depth different captures (.interned entry.identity) allocated
    allocated_context.base argument_available allocated_context.depth allocated_open).heap
private theorem final_open : InternedOpenDepthReadback.Heap reader := by
  simpa only [complete_done,Outcome.state] using InternedOpenDepthReadback.complete_heap false entry storedBody depth ordinary afterBody body_open (by cbv)
private theorem ready : Ready reader := ⟨final_semantic,final_covered,final_open⟩

end MicroCFTA.BinderContractCounterexample
