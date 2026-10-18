import MicroCFTA.SourceCurrentStoredMuProfileContract
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
private theorem verified : InternedNestedFacts.Verified afterBody
    (InternedNestedRequestFacts.complete false entry storedBody depth ordinary afterBody) Available := InternedNestedRequestFacts.complete_verified false entry storedBody depth ordinary afterBody
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
private theorem duplicates (name : Reference) :
    List.Mem name [.uninterned 10,.uninterned 11] ↔
      List.Mem name [.uninterned 10,.uninterned 11,.uninterned 10,.uninterned 11] := by
  change name ∈ ([.uninterned 10,.uninterned 11] : List Reference) ↔
    name ∈ ([.uninterned 10,.uninterned 11] ++ [.uninterned 10,.uninterned 11] : List Reference)
  rw [List.mem_append]
  exact ⟨Or.inl,fun found => found.elim id id⟩
private theorem free_correct : InternedFreshOrdinaryFreeHeap.Correct entry storedBody depth ordinary := by
  intro name
  cbv
  exact duplicates name
private theorem depth_correct : InternedFreshOrdinaryDepthHeap.Correct entry storedBody depth ordinary := by
  intro smart
  cases smart <;> constructor
  all_goals try {cbv}
  all_goals intro name; cbv; exact duplicates name
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



private def source : Syntax Nat Bool := .binder true body
private def lexical : List (Sum (Value Nat Bool) Nat) := [.inr 0,.inr 1]
private def firstNames (index : Nat) : Reference := .uninterned (index+10)
private def secondNames (index : Nat) : Reference := .uninterned (index+20)
private def firstInputs := lexical.map (InternedFreshOrdinaryLiveInputs.input firstNames)
private def secondInputs := lexical.map (InternedFreshOrdinaryLiveInputs.input secondNames)
private def secondCall := build source secondInputs reader
private def secondRaw := value secondCall
private def secondHeap := secondCall.state
private def outputName : Reference := .uninterned 30
private def own : Reference := .uninterned 1000
private def firstMap : InternedStoredSubstitution.Environment Nat Bool := fun name =>
  if name = firstNames 0 then some .empty else if name = firstNames 1 then some (.reference outputName) else none
private def secondMap : InternedStoredSubstitution.Environment Nat Bool := fun name =>
  if name = secondNames 0 then some .empty else if name = secondNames 1 then some (.reference outputName) else none
private def firstExecution := InternedFreshOrdinaryStoredSubstitution.execute storedBody firstMap secondHeap
private def firstOutput := value firstExecution
private def firstAfter := firstExecution.state
private def secondExecution := InternedFreshOrdinaryStoredSubstitution.execute secondRaw secondMap firstAfter
private def final := secondExecution.state
open InternedStoredSubstitution (Replacements)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedFreshOrdinaryLiveInputs (input)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)

private theorem first_done : build source firstInputs reader = .done storedBody reader := by cbv
private theorem second_done : build source secondInputs reader = .done secondRaw secondHeap := by cbv
private theorem first_execute : execute storedBody firstMap secondHeap = .done firstOutput firstAfter := by cbv
private theorem second_execute : execute secondRaw secondMap firstAfter = .done .empty final := by cbv
private theorem first_values (state : State Nat Bool) : InternedNestedProvenance.Values state firstInputs := captures_available state
private theorem second_values (state : State Nat Bool) : InternedNestedProvenance.Values state secondInputs := by
  intro child member
  have choices : child = .reference (.uninterned 20) ∨ child = .reference (.uninterned 21) := by
    simpa only [secondInputs,lexical,List.map_cons,List.map_nil,input,secondNames,Nat.zero_add,List.mem_cons,List.not_mem_nil,or_false] using member
  rcases choices with rfl | rfl <;> exact InternedNestedProvenance.ordinary_available state _
private theorem first_context : Context reader firstInputs :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic _ (first_values reader),ready.semantic.2⟩
private theorem second_context : Context reader secondInputs :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context reader ready.semantic _ (second_values reader),ready.semantic.2⟩
private theorem source_keeps (expression : Syntax Nat Bool) (inputs : List (Value Nat Bool))
    (before : State Nat Bool) (initial : Ready before) (available : InternedNestedProvenance.Values before inputs)
    (result : Value Nat Bool) (after : State Nat Bool) (actual : build expression inputs before = .done result after) : Keeps before after := by
  have checked := InternedFreshOrdinaryFacts.build_verified expression inputs before initial.semantic.1.normal.facts available
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source expression inputs before initial.semantic available
  · exact InternedFreshOrdinaryCoverage.build_covered expression inputs before initial.semantic.1.normal.facts.coherent.valid initial.covered result after actual
  · simpa only [actual,Outcome.state] using (InternedOpenDepthExecution.build_depth expression inputs before
      (SourceRecursiveIntersectionSemanticHeap.context before initial.semantic inputs available) initial.semantic.2 initial.depth).heap
  · simpa only [actual,Outcome.state] using checked.growth
  · simpa only [actual,Outcome.state] using checked.history
private theorem second_keeps : Keeps reader secondHeap := source_keeps source secondInputs reader ready (second_values reader) secondRaw secondHeap second_done
private theorem stored_available : Available reader storedBody := by
  simpa only [complete_done,Outcome.state] using verified.available storedBody body_available
private theorem second_available : Available secondHeap secondRaw :=
  (InternedFreshOrdinaryFacts.build_verified source secondInputs reader ready.semantic.1.normal.facts (second_values reader)).result secondRaw secondHeap second_done
private theorem first_replacements (state : State Nat Bool) : Replacements state firstMap := by
  intro name result found
  dsimp only [firstMap] at found
  split at found
  · cases found; exact empty_available state
  · split at found
    · cases found; exact InternedNestedProvenance.ordinary_available state _
    · cases found
private theorem second_replacements (state : State Nat Bool) : Replacements state secondMap := by
  intro name result found
  dsimp only [secondMap] at found
  split at found
  · cases found; exact empty_available state
  · split at found
    · cases found; exact InternedNestedProvenance.ordinary_available state _
    · cases found
private theorem execute_keeps (original : Value Nat Bool) (environment : InternedStoredSubstitution.Environment Nat Bool)
    (before : State Nat Bool) (initial : Ready before) (available : Available before original)
    (replacements : Replacements before environment) (result : Value Nat Bool) (after : State Nat Bool)
    (actual : execute original environment before = .done result after) : Keeps before after := by
  obtain ⟨produced,returned,called,kept,_,_⟩ := SourceCurrentStoredReconstruction.execute original environment before initial available replacements
  have same := Outcome.done.inj (called.symm.trans actual)
  cases same.1
  cases same.2
  exact kept
private theorem first_keeps : Keeps secondHeap firstAfter := execute_keeps storedBody firstMap secondHeap second_keeps.ready
  (second_keeps.available storedBody stored_available) (first_replacements secondHeap) firstOutput firstAfter first_execute
private theorem last_keeps : Keeps firstAfter final := execute_keeps secondRaw secondMap firstAfter first_keeps.ready
  (first_keeps.available secondRaw second_available) (second_replacements firstAfter) .empty final second_execute
private theorem whole : Keeps reader final := second_keeps.trans (first_keeps.trans last_keeps)
private theorem first_warm : execute storedBody firstMap final = .done firstOutput final :=
  InternedFreshOrdinaryStoredSubstitution.execute_replay storedBody firstMap secondHeap final firstOutput firstAfter
    second_keeps.ready.semantic.1.normal.facts.coherent.valid first_execute last_keeps.growth
private theorem second_warm : execute secondRaw secondMap final = .done .empty final :=
  InternedFreshOrdinaryStoredSubstitution.execute_replay secondRaw secondMap firstAfter final .empty final
    first_keeps.ready.semantic.1.normal.facts.coherent.valid second_execute (grows_refl _)
private theorem scope : Scope source lexical = [.inl .depth,.inr 0,.inr 1] := by cbv
private theorem aliases : Aliases source lexical firstNames secondNames := by
  intro a ha b hb
  rw [scope] at ha hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> decide
private theorem tests : ∀ label ∈ Scope source lexical,
    Sum.elim id firstNames label = own ↔ Sum.elim id secondNames label = own := by
  intro label member
  rw [scope] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;> decide
private theorem paired : SourceCurrentReaderReplacementSlots.Paired
    (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) firstMap secondMap firstInputs secondInputs := by
  exact .cons (by cbv) (.cons (by cbv) .nil)
private theorem first_filter : run (withoutSelfReference own storedBody) final = (storedBody,final) := by cbv
private theorem second_filter : run (withoutSelfReference own secondRaw) final = (secondRaw,final) := by cbv
private theorem not_empty_fusion : ¬ SourceCurrentBoundedFilteredFusion.Fusion 0 source := by
  intro law
  have compared := law final whole.ready lexical firstNames secondNames own own firstMap secondMap reader reader reader secondHeap
    storedBody secondRaw storedBody secondRaw firstOutput .empty (by cbv) (by cbv)
    first_context second_context aliases tests paired (first_replacements final) (second_replacements final)
    (whole.available storedBody stored_available) ((first_keeps.trans last_keeps).available secondRaw second_available)
    first_done second_done whole.growth (first_keeps.trans last_keeps).growth first_filter second_filter first_warm second_warm
  cbv at compared
private theorem not_tracked_fusion : ¬ SourceCurrentTrackedFilteredFusion.Fusion 0 source := by
  intro law
  exact not_empty_fusion (SourceCurrentTrackedFilteredFusion.to_empty 0 source law)
private theorem body_law : SourceCurrentTrackedFilteredFusion.Fusion 0 body := by
  apply SourceCurrentTrackedFilteredNodeFusion.node
  intro symbol guard children member child included
  have same : EdgeSyntax.mk symbol guard children = .mk 7 false [.var 1,.var 2] := by
    simpa only [body,List.mem_singleton] using member
  cases same
  simp only [List.mem_cons] at included
  rcases included with rfl | rfl | impossible
  · exact SourceCurrentTrackedFilteredFusion.reference _ 1
  · exact SourceCurrentTrackedFilteredFusion.reference _ 2
  · cases impossible

/-- The current all-Context binder law fails even at raw depth zero and a proved strict node body law. -/
theorem counterexample : ∃ expression : Syntax Nat Bool,
    SourceCurrentTrackedFilteredFusion.Fusion 0 expression ∧
    (∀ rank < 0, ∀ term : Syntax Nat Bool, SourceCurrentTrackedFilteredFusion.Fusion rank term) ∧
    ¬ SourceCurrentBoundedFilteredFusion.Fusion 0 (.binder true expression) ∧
    ¬ SourceCurrentTrackedFilteredFusion.Fusion 0 (.binder true expression) :=
  ⟨body,body_law,(by intro rank less; omega),not_empty_fusion,not_tracked_fusion⟩

end MicroCFTA.BinderContractCounterexample

namespace MicroCFTA.BinderContractCounterexample
open InternedBinderProtocol (Reference)
open InternedFreshOrdinaryConstruction (ordinaryLevel)
private def rejected_assignment (name : Reference) : InternedRootProfile.Profile :=
  if name = .uninterned 10 then some []
  else if name = .uninterned 11 then some [.uninterned 30] else some [name]

/-- The preserved artificial cached payload fails the new parametric body/probe contract. -/
theorem parametric_rejected :
    ¬ SourceCurrentStoredMuProfileContract.Correct entry storedBody depth ordinary := by
  intro correct
  have same := correct rejected_assignment (some [])
  have left : SourceCurrentStoredProfileFunction.denote storedBody
      (SourceCurrentStoredMuProfileContract.shadow (.interned entry.identity) (some []) rejected_assignment) = none := by cbv
  have right : SourceCurrentStoredProfileFunction.denote ordinary
      (SourceCurrentStoredMuProfileContract.shadow (.uninterned (ordinaryLevel depth)) (some []) rejected_assignment) = some [] := by cbv
  rw [left,right] at same
  have impossible := same.1.mp rfl
  cases impossible
end MicroCFTA.BinderContractCounterexample

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.BinderContractCounterexample.parametric_rejected
#print MicroCFTA.BinderContractCounterexample.parametric_rejected
#print axioms MicroCFTA.BinderContractCounterexample.parametric_rejected
