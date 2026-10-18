import MicroCFTA.SourceCurrentCausalUnionPairPreparation
import MicroCFTA.SourceCurrentFilteredUnionFragments
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.PairIntegration
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open InternedEdgeResidency (nodeEdges)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentCausalUnionPairPreparation (Schedule)
open SourceCurrentLiteralRootParts (Row)
open SourceEqualityRequiredCache (Ready Keeps)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private theorem source_effect (term : Syntax Nat Bool) (names : List Reference)
    (before : State Nat Bool) (ready : Ready before)
    (available : InternedNestedProvenance.Values before (names.map Value.reference)) :
    build term (names.map Value.reference) before =
      .done (value (build term (names.map Value.reference) before)) (build term (names.map Value.reference) before).state ∧
      Keeps before (build term (names.map Value.reference) before).state ∧
      Available (build term (names.map Value.reference) before).state (value (build term (names.map Value.reference) before)) := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic _ available
  obtain ⟨result,after,called⟩ := InternedFreshOrdinaryClosedCompletion.literal_complete term names before context ready.semantic.2 ready.covered
  have checked := InternedFreshOrdinaryFacts.build_verified term _ before ready.semantic.1.normal.facts available
  have kept : Keeps before after := by
    refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
    · simpa only [called,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source term _ before ready.semantic available
    · exact InternedFreshOrdinaryCoverage.build_covered term _ before ready.semantic.1.normal.facts.coherent.valid ready.covered result after called
    · simpa only [called,Outcome.state] using (InternedOpenDepthExecution.build_depth term _ before context ready.semantic.2 ready.depth).heap
    · simpa only [called,Outcome.state] using checked.growth
    · simpa only [called,Outcome.state] using checked.history
  rw [called]
  exact ⟨rfl,kept,checked.result result after called⟩


private def baseSource : Syntax Nat Bool := .node [.mk 0 false [
  .binder false (.node [.mk 7 false [.var 0]]),.node [.mk 1 false []],.node [.mk 2 true []]]]
private def baseRun := build baseSource [] empty
private def base := value baseRun
private def before := baseRun.state
private def mu := (children base)[0]?.getD .empty
private def a := (children base)[1]?.getD .empty
private def c := (children base)[2]?.getD .empty
private def row := (nodeEdges c)[0]?.getD (.mk ⟨0,.mk 0 [] false⟩ [])
private def firstOwn : Reference := .depth
private def secondOwn : Reference := .uninterned 1
private def other : Reference := .uninterned 0
private def expressions : List (Syntax Nat Bool) := [.var 0,.var 1]
private def firstNames : List Reference := [firstOwn,other]
private def secondNames : List Reference := [secondOwn,other]
private def firstInputs := firstNames.map Value.reference
private def secondInputs := secondNames.map Value.reference
private def firstRun := build (.union expressions) firstInputs before
private def firstRaw := value firstRun
private def middle := firstRun.state
private def secondRun := build (.union expressions) secondInputs middle
private def secondRaw := value secondRun
private def reader := secondRun.state
private def firstMap : Environment Nat Bool := fun name =>
  if name=firstOwn then some mu else if name=other then some c else none
private def secondMap : Environment Nat Bool := fun name =>
  if name=secondOwn then some a else if name=other then some c else none

private theorem base_done : build baseSource [] empty = .done base before := by cbv
private theorem base_ready : Ready before := SourceEqualityRequiredCache.constructed baseSource base before base_done
private theorem base_available : Available before base :=
  (InternedFreshOrdinaryFacts.build_verified baseSource [] empty InternedNestedFacts.empty_facts
    (by intro supplied impossible; cases impossible)).result base before base_done
private theorem mu_available : Available before mu := base_available.children mu (by cbv; exact List.mem_cons_self)
private theorem a_available : Available before a :=
  base_available.children a (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)
private theorem c_available : Available before c :=
  base_available.children c (by cbv; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
private theorem first_inputs : InternedNestedProvenance.Values before firstInputs := by
  intro supplied present
  have choice : supplied = .reference firstOwn ∨ supplied = .reference other := by
    simpa only [firstInputs,firstNames,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] using present
  rcases choice with rfl | rfl
  · exact InternedNestedProvenance.depth_available before
  · exact InternedNestedProvenance.ordinary_available before 0
private theorem first_effect : build (.union expressions) firstInputs before = .done firstRaw middle ∧
    Keeps before middle ∧ Available middle firstRaw :=
  source_effect (.union expressions) firstNames before base_ready first_inputs
private theorem second_inputs : InternedNestedProvenance.Values middle secondInputs := by
  intro supplied present
  have choice : supplied = .reference secondOwn ∨ supplied = .reference other := by
    simpa only [secondInputs,secondNames,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] using present
  rcases choice with rfl | rfl
  · exact InternedNestedProvenance.ordinary_available middle 1
  · exact InternedNestedProvenance.ordinary_available middle 0
private theorem second_effect : build (.union expressions) secondInputs middle = .done secondRaw reader ∧
    Keeps middle reader ∧ Available reader secondRaw :=
  source_effect (.union expressions) secondNames middle first_effect.2.1.ready second_inputs
private theorem first_context : Context before firstInputs :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context before base_ready.semantic _ first_inputs,base_ready.semantic.2⟩
private theorem second_context : Context middle secondInputs :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context middle first_effect.2.1.ready.semantic _ second_inputs,
    first_effect.2.1.ready.semantic.2⟩
private noncomputable def history : History empty reader := by
  let first := Classical.choice (SourceCurrentNativeMuPublication.build_history (.union expressions) firstInputs before first_context)
  let second := Classical.choice (SourceCurrentNativeMuPublication.build_history (.union expressions) secondInputs middle second_context)
  have one : History before middle := by simpa only [first_effect.1,Outcome.state] using first
  have two : History middle reader := by simpa only [second_effect.1,Outcome.state] using second
  exact .trans (SourceCurrentNativeMuPublication.closed_history baseSource) (.trans one two)
private theorem first_replacements : Replacements reader firstMap := by
  intro name output found
  dsimp only [firstMap] at found
  split at found
  · cases found; exact (first_effect.2.1.trans second_effect.2.1).available mu mu_available
  · split at found
    · cases found; exact (first_effect.2.1.trans second_effect.2.1).available c c_available
    · cases found
private theorem second_replacements : Replacements reader secondMap := by
  intro name output found
  dsimp only [secondMap] at found
  split at found
  · cases found; exact (first_effect.2.1.trans second_effect.2.1).available a a_available
  · split at found
    · cases found; exact (first_effect.2.1.trans second_effect.2.1).available c c_available
    · cases found
private theorem first_filter (heap : State Nat Bool) :
    run (withoutSelfReference firstOwn firstRaw) heap = (.reference other,heap) := by cbv
private theorem second_filter (heap : State Nat Bool) :
    run (withoutSelfReference secondOwn secondRaw) heap = (.reference other,heap) := by cbv
private theorem first_done (heap : State Nat Bool) : execute (.reference other) firstMap heap = .done c heap := by cbv
private theorem second_done (heap : State Nat Bool) : execute (.reference other) secondMap heap = .done c heap := by cbv
private theorem first_many (heap : State Nat Bool) : buildMany expressions firstInputs heap =
    .done [.reference firstOwn,.reference other] heap := by cbv
private theorem second_many (heap : State Nat Bool) : buildMany expressions secondInputs heap =
    .done [.reference secondOwn,.reference other] heap := by cbv
private theorem c_row : Row c row := by cbv; exact Row.node List.mem_cons_self

private theorem selected (heap : State Nat Bool) (ready : Ready heap)
    (own : Reference) (parent : Value Nat Bool) (environment : Environment Nat Bool)
    (filters outputs : List (Value Nat Bool))
    (available : InternedNestedProvenance.Values heap [.reference own,.reference other])
    (made : run (makeUnion [.reference own,.reference other]) heap = (parent,heap))
    (filter : run (withoutSelfReference own parent) heap = (.reference other,heap))
    (replacements : Replacements heap environment)
    (done : execute (.reference other) environment heap = .done c heap)
    (filterCalls : All₂ (fun raw cut => run (withoutSelfReference own raw) heap = (cut,heap))
      [.reference own,.reference other] filters)
    (storedCalls : All₂ (fun cut output => execute cut environment heap = .done output heap) filters outputs)
    (notBare : parent ≠ .reference own) :
    ∃ cut output, filters[1]? = some cut ∧ outputs[1]? = some output ∧ Row output row := by
  have parts := SourceCurrentFilteredUnionFragments.parts heap ready [.reference own,.reference other] filters outputs
    available parent (.reference other) c own environment made filter replacements done filterCalls storedCalls
  obtain ⟨index,raw,cut,output,found,cutFound,outputFound,retained,part⟩ := (parts.2 row).mp c_row
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      cases found
      exact False.elim (retained.elim (fun different => different rfl) notBare)
  | succ index =>
      cases index with
      | zero => exact ⟨cut,output,cutFound,outputFound,part⟩
      | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at found; cases found

private def Claim : Prop :=
  build baseSource [] empty = .done base before ∧
    firstRaw ≠ secondRaw ∧ mu ≠ a ∧ row.entry.key.symbol = 2 ∧ row.entry.key.constraint = true ∧ row.children = [] ∧
    ∃ final, Keeps reader final ∧ Nonempty (History empty final) ∧
      Schedule expressions firstInputs firstOwn firstMap firstRaw (.reference other) c final ∧
      Schedule expressions secondInputs secondOwn secondMap secondRaw (.reference other) c final ∧
      ∃ firstFilters firstOutputs secondFilters secondOutputs,
        All₂ (fun raw cut => run (withoutSelfReference firstOwn raw) final = (cut,final))
          [.reference firstOwn,.reference other] firstFilters ∧
        All₂ (fun cut output => execute cut firstMap final = .done output final) firstFilters firstOutputs ∧
        All₂ (fun raw cut => run (withoutSelfReference secondOwn raw) final = (cut,final))
          [.reference secondOwn,.reference other] secondFilters ∧
        All₂ (fun cut output => execute cut secondMap final = .done output final) secondFilters secondOutputs ∧
        (∃ cut output, firstFilters[1]? = some cut ∧ firstOutputs[1]? = some output ∧ Row output row) ∧
        (∃ cut output, secondFilters[1]? = some cut ∧ secondOutputs[1]? = some output ∧ Row output row)

private theorem checked : Claim := by
  refine ⟨base_done,?_,?_,?_,?_,?_,?_⟩
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible
  · cbv
  · cbv
  · cbv
  · obtain ⟨final,kept,finalHistory,firstSchedule,secondSchedule⟩ := SourceCurrentCausalUnionPairPreparation.prepare
      expressions firstInputs secondInputs before middle middle reader reader first_context second_context
      firstRaw secondRaw first_effect.1 second_effect.1 second_effect.2.1.ready history second_effect.2.1.growth
      (grows_refl _) (second_effect.2.1.available firstRaw first_effect.2.2) second_effect.2.2
      firstOwn secondOwn firstMap secondMap first_replacements second_replacements
      (.reference other) (.reference other) c c (first_filter reader) (second_filter reader) (first_done reader) (second_done reader)
    obtain ⟨firstValues,firstFilters,firstOutputs,firstAvailable,_,_,firstMade,_,firstMany,
      firstFilterCalls,firstStoredCalls,_firstSources,firstParentFilter,firstParentDone⟩ := firstSchedule
    obtain ⟨secondValues,secondFilters,secondOutputs,secondAvailable,_,_,secondMade,_,secondMany,
      secondFilterCalls,secondStoredCalls,_secondSources,secondParentFilter,secondParentDone⟩ := secondSchedule
    have firstValuesEq := (Outcome.done.inj (firstMany.symm.trans (first_many final))).1
    have secondValuesEq := (Outcome.done.inj (secondMany.symm.trans (second_many final))).1
    cases firstValuesEq
    cases secondValuesEq
    have firstSelected := selected final kept.ready firstOwn firstRaw firstMap firstFilters firstOutputs firstAvailable
      firstMade firstParentFilter (fun name output found => kept.available output (first_replacements name output found))
      firstParentDone firstFilterCalls firstStoredCalls (by cbv; intro impossible; cases impossible)
    have secondSelected := selected final kept.ready secondOwn secondRaw secondMap secondFilters secondOutputs secondAvailable
      secondMade secondParentFilter (fun name output found => kept.available output (second_replacements name output found))
      secondParentDone secondFilterCalls secondStoredCalls (by cbv; intro impossible; cases impossible)
    exact ⟨final,kept,finalHistory,firstSchedule,secondSchedule,firstFilters,firstOutputs,secondFilters,secondOutputs,
      firstFilterCalls,firstStoredCalls,secondFilterCalls,secondStoredCalls,firstSelected,secondSelected⟩

/-- Distinct source-built unions retain the same guarded row at original member index one after actual joint preparation. -/
theorem witness : Claim := checked

end MicroCFTA.PairIntegration
