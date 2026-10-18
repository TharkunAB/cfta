import MicroCFTA.SourceCurrentCausalFilteredSourceFusion
import MicroCFTA.SourceCurrentStoredReconstruction

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.CausalEmptyKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves encode input)
open InternedBinderProtocol (Reference)
open InternedFreshOrdinaryLiveInputs (input)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentReaderReplacementSlots (Paired)
open SourceCurrentUsedBinderAliasTransport (Aliases Scope)
open SourceEqualityRequiredCache (Ready Keeps)

private def baseSource : Syntax Nat Bool := .node [.mk 0 false [
  .node [.mk 1 false []],.node [.mk 2 false []]]]
private def result (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def baseRun := build baseSource [] empty
private def base := result baseRun
private def before := baseRun.state
private def a := (children base)[0]?.getD .empty
private def b := (children base)[1]?.getD .empty
private def q : Reference := .uninterned 17
private def own : Reference := .uninterned 99
private def expression : Syntax Nat Bool := .node [.mk 9 false [
  .var 0,.binder true (.binder false (.node [.mk 7 false [.var 0,.var 2]]))]]
private def names : Unit → Reference := fun _ => q
private def inputs : List (Sum (Value Nat Bool) Unit) := [.inr ()]
private def rawRun := build expression [.reference q] before
private def raw := result rawRun
private def rawHeap := rawRun.state
private def replacement (value : Value Nat Bool) : Environment Nat Bool :=
  fun name => if name=q then some value else none

private theorem base_done : build baseSource [] empty = .done base before := by cbv
private theorem base_ready : Ready before := SourceEqualityRequiredCache.constructed baseSource base before base_done
private theorem base_available : Available before base :=
  (InternedFreshOrdinaryFacts.build_verified baseSource [] empty InternedNestedFacts.empty_facts
    (by intro value impossible; cases impossible)).result base before base_done
private theorem a_available : Available before a := base_available.children a (by cbv; exact List.mem_cons_self)
private theorem b_available : Available before b :=
  base_available.children b (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)
private theorem q_available : Available before (.reference q) :=
  reference_available before q (InternedFreshProbeKeys.sentinel_references_issued before.nodes 17).2
private theorem raw_context : Context before [.reference q] := by
  refine ⟨SourceRecursiveIntersectionSemanticHeap.context before base_ready.semantic _ ?_,base_ready.semantic.2⟩
  intro value member
  have same : value = .reference q := List.mem_singleton.mp member
  exact same ▸ q_available
private theorem raw_done : build expression [.reference q] before = .done raw rawHeap := by cbv
private theorem raw_effect : Keeps before rawHeap := by
  have checked := InternedFreshOrdinaryFacts.build_verified expression [.reference q] before
    raw_context.base.normal.facts raw_context.base.inputs
  have semantic := SourceRecursiveIntersectionSemanticHeap.source expression [.reference q] before
    base_ready.semantic raw_context.base.inputs
  have covered := InternedFreshOrdinaryCoverage.build_covered expression [.reference q] before
    raw_context.base.normal.facts.coherent.valid base_ready.covered raw rawHeap raw_done
  have depth := (InternedOpenDepthExecution.build_depth expression [.reference q] before raw_context.base
    base_ready.semantic.2 base_ready.depth).heap
  refine ⟨⟨?_,covered,?_⟩,?_,?_⟩
  · simpa only [raw_done,Outcome.state] using semantic
  · simpa only [raw_done,Outcome.state] using depth
  · simpa only [raw_done,Outcome.state] using checked.growth
  · simpa only [raw_done,Outcome.state] using checked.history
private theorem raw_available : Available rawHeap raw :=
  (InternedFreshOrdinaryFacts.build_verified expression [.reference q] before
    raw_context.base.normal.facts raw_context.base.inputs).result raw rawHeap raw_done
private theorem raw_history : History empty rawHeap := by
  obtain ⟨localHistory⟩ := SourceCurrentNativeMuPublication.build_history expression [.reference q] before raw_context
  have initial : History empty before := SourceCurrentNativeMuPublication.closed_history baseSource
  exact .trans initial (by simpa only [raw_done,Outcome.state] using localHistory)
private theorem replacements (state : State Nat Bool) (value : Value Nat Bool) (available : Available state value) :
    Replacements state (replacement value) := by
  intro name output found
  dsimp only [replacement] at found
  split at found
  · cases found; exact available
  · cases found
private theorem aliases : Aliases expression inputs names names := by intro _ _ _ _; rfl
private theorem tests : ∀ label ∈ Scope expression inputs,
    Sum.elim id names label = own ↔ Sum.elim id names label = own := by intro _ _; rfl
private theorem paired (first second : Value Nat Bool)
    (same : (first.referenceOf == .empty) = (second.referenceOf == .empty)) :
    Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty))
      (replacement first) (replacement second)
      (inputs.map (InternedFreshOrdinaryLiveInputs.input names))
      (inputs.map (InternedFreshOrdinaryLiveInputs.input names)) := by
  refine .cons ?_ .nil
  change (((replacement first q).getD (.reference q)).referenceOf == .empty) =
    (((replacement second q).getD (.reference q)).referenceOf == .empty)
  simpa only [replacement,ite_true,Option.getD_some] using same

private theorem compare (first second : Value Nat Bool)
    (firstAvailable : Available rawHeap first) (secondAvailable : Available rawHeap second)
    (same : (first.referenceOf == .empty) = (second.referenceOf == .empty)) :
    ∃ reader left right, Ready reader ∧ History empty reader ∧
      Grows rawHeap reader ∧ Available reader raw ∧
      Replacements reader (replacement first) ∧ Replacements reader (replacement second) ∧
      run (withoutSelfReference own raw) reader = (raw,reader) ∧
      execute raw (replacement first) reader = .done left reader ∧
      execute raw (replacement second) reader = .done right reader ∧
      (left.referenceOf == .empty) = (right.referenceOf == .empty) := by
  obtain ⟨left,middle,firstDone,firstKept,leftAvailable,⟨firstHistory⟩⟩ :=
    SourceCurrentStoredReconstruction.execute raw (replacement first) rawHeap raw_effect.ready raw_available
      (replacements rawHeap first firstAvailable)
  obtain ⟨right,reader,secondDone,secondKept,rightAvailable,⟨secondHistory⟩⟩ :=
    SourceCurrentStoredReconstruction.execute raw (replacement second) middle firstKept.ready
      (firstKept.available raw raw_available)
      (replacements middle second (firstKept.available second secondAvailable))
  have whole := firstKept.trans secondKept
  have history : History empty reader := .trans (.trans raw_history firstHistory) secondHistory
  have firstWarm : execute raw (replacement first) reader = .done left reader :=
    InternedFreshOrdinaryReplay.build_replay (encode (leaves raw) [] raw)
      ((leaves raw).map (InternedStoredSubstitution.input (replacement first))) rawHeap reader left middle
      raw_effect.ready.semantic.1.normal.facts.coherent.valid firstDone secondKept.growth
  have secondWarm : execute raw (replacement second) reader = .done right reader :=
    InternedFreshOrdinaryReplay.build_replay (encode (leaves raw) [] raw)
      ((leaves raw).map (InternedStoredSubstitution.input (replacement second))) middle reader right reader
      firstKept.ready.semantic.1.normal.facts.coherent.valid secondDone (grows_refl _)
  have filtered : run (withoutSelfReference own raw) reader = (raw,reader) := by cbv [raw,result,rawRun,before,baseRun,baseSource,expression,q,own]; rfl
  have context : Context before (inputs.map (InternedFreshOrdinaryLiveInputs.input names)) := raw_context
  have done : build expression (inputs.map (InternedFreshOrdinaryLiveInputs.input names)) before = .done raw rawHeap := raw_done
  have firstReplacements := replacements reader first (whole.available first firstAvailable)
  have secondReplacements := replacements reader second (whole.available second secondAvailable)
  have equal := SourceCurrentCausalFilteredSourceFusion.source expression reader whole.ready history inputs names names own own
    (replacement first) (replacement second) before before rawHeap rawHeap raw raw raw raw left right
    context context aliases tests (paired first second same) firstReplacements secondReplacements
    (whole.available raw raw_available) (whole.available raw raw_available) done done whole.growth whole.growth
    filtered filtered firstWarm secondWarm
  exact ⟨reader,left,right,whole.ready,history,whole.growth,whole.available raw raw_available,
    firstReplacements,secondReplacements,filtered,firstWarm,secondWarm,equal⟩

private def Calls (first second : Value Nat Bool) : Prop :=
  ∃ reader left right, Ready reader ∧ History empty reader ∧
    Grows rawHeap reader ∧ Available reader raw ∧
    Replacements reader (replacement first) ∧ Replacements reader (replacement second) ∧
    run (withoutSelfReference own raw) reader = (raw,reader) ∧
    execute raw (replacement first) reader = .done left reader ∧
    execute raw (replacement second) reader = .done right reader ∧
    (left.referenceOf == .empty) = (right.referenceOf == .empty)

private def Claim : Prop :=
  build baseSource [] empty = .done base before ∧ Ready before ∧
    build expression [.reference q] before = .done raw rawHeap ∧ Ready rawHeap ∧ History empty rawHeap ∧
    Available rawHeap a ∧ Available rawHeap b ∧ a ≠ b ∧
    a.referenceOf ≠ .empty ∧ b.referenceOf ≠ .empty ∧
    raw.depth > 0 ∧ Calls a b ∧ Calls .empty .empty

private theorem checked : Claim := by
  refine ⟨base_done,base_ready,raw_done,raw_effect.ready,raw_history,
    raw_effect.available a a_available,raw_effect.available b b_available,?_,?_,?_,?_,?_,?_⟩
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible
  · cbv
  · exact compare a b (raw_effect.available a a_available) (raw_effect.available b b_available) (by cbv)
  · exact compare .empty .empty (empty_available _) (empty_available _) rfl

/-- Actual nested raw and smart source binders admit distinct nonempty and Empty replacement cases at causal warm readers. -/
theorem witness : Claim := checked

end MicroCFTA.CausalEmptyKernels
