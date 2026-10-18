import MicroCFTA.SourceCurrentFilteredUnionCoverage
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.UnionCoverageKernels
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference)
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentGeneratedUnionPreparation (FilteredCalls)
open SourceCurrentLiteralRootParts (Literal Row)

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


private def source : Syntax Nat Bool := .binder false (.node [.mk 7 false [.var 0]])
private def built := build source [] empty
private def mu := value built
private def before := built.state
private def own : Reference := .depth
private def other : Reference := .uninterned 0
private def expressions : List (Syntax Nat Bool) := [.var 0,.var 1]
private def names : List Reference := [own,other]
private def inputs : List (Value Nat Bool) := names.map Value.reference
private def rawRun := build (.union expressions) inputs before
private def raw := value rawRun
private def reader := rawRun.state
private def raws : List (Value Nat Bool) := [.reference own,.reference other]
private def environment : Environment Nat Bool := fun name =>
  if name = own then some mu else if name = other then some .empty else none
private def used : Value Nat Bool → Prop
  | .mu entry body _ _ => .interned entry.identity ∈ body.free
  | _ => False
private theorem built_done : build source [] empty = .done mu before := by cbv
private theorem before_ready : Ready before := SourceEqualityRequiredCache.constructed source mu before built_done
private theorem mu_available : Available before mu :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro supplied impossible; cases impossible)).result mu before built_done
private theorem names_available : InternedNestedProvenance.Values before inputs := by
  intro supplied member
  have choices : supplied = .reference own ∨ supplied = .reference other := by
    simpa only [inputs,names,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] using member
  rcases choices with rfl | rfl
  · exact InternedNestedProvenance.depth_available before
  · exact InternedNestedProvenance.ordinary_available before 0
private theorem effects : build (.union expressions) inputs before = .done raw reader ∧
    Keeps before reader ∧ Available reader raw := source_effect (.union expressions) names before before_ready names_available
private theorem ready : Ready reader := effects.2.1.ready
private theorem context : Context before inputs :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context before before_ready.semantic inputs names_available,before_ready.semantic.2⟩
private theorem replacements : Replacements reader environment := by
  intro name output found
  dsimp only [environment] at found
  split at found
  · cases found; exact effects.2.1.available mu mu_available
  · split at found
    · cases found; exact empty_available reader
    · cases found
private theorem many_done : buildMany expressions inputs before = .done raws before := by cbv
private theorem parent_filter (heap : State Nat Bool) :
    run (withoutSelfReference own raw) heap = (.reference other,heap) := by cbv
private theorem own_filter (heap : State Nat Bool) :
    run (withoutSelfReference own (.reference own)) heap = (.reference own,heap) := rfl
private theorem own_call (heap : State Nat Bool) : execute (.reference own) environment heap = .done mu heap := by cbv
private theorem other_call (heap : State Nat Bool) : execute (.reference other) environment heap = .done .empty heap := by cbv
private theorem not_retained : ¬ ((.reference own : Value Nat Bool) ≠ .reference own ∨ raw = .reference own) := by
  intro impossible
  rcases impossible with different | same
  · exact different rfl
  · cbv at same
    cases same

private theorem members_warm (heap : State Nat Bool) : ∀ member ∈ raws, ∃ cut output,
    run (withoutSelfReference own member) heap = (cut,heap) ∧ execute cut environment heap = .done output heap := by
  intro member present
  have choices : member = .reference own ∨ member = .reference other := by
    simpa only [raws,List.mem_cons,List.not_mem_nil,or_false] using present
  rcases choices with rfl | rfl
  · exact ⟨.reference own,mu,own_filter heap,own_call heap⟩
  · exact ⟨.reference other,.empty,rfl,other_call heap⟩

private theorem checked :
    build source [] empty = .done mu before ∧ used mu ∧ mu.referenceOf ≠ .empty ∧
    build (.union expressions) inputs before = .done raw reader ∧ Ready reader ∧
    ¬ ((.reference own : Value Nat Bool) ≠ .reference own ∨ raw = .reference own) ∧
    ∃ filters outputs middle filtered filterHeap result final,
      FilteredCalls own environment raws reader filters outputs middle ∧
      run (withoutSelfReference own raw) middle = (filtered,filterHeap) ∧
      execute filtered environment filterHeap = .done result final ∧
      Keeps reader middle ∧ Keeps middle filterHeap ∧ Keeps filterHeap final ∧
      Available final result ∧ InternedNestedProvenance.Values final raws ∧
      run (makeUnion raws) final = (raw,final) ∧
      run (withoutSelfReference own raw) final = (.reference other,final) ∧
      execute (.reference other) environment final = .done .empty final ∧ result = .empty ∧
      run (withoutSelfReference own (.reference own)) final = (.reference own,final) ∧
      execute (.reference own) environment final = .done mu final ∧
      (∀ atom, Literal result atom ↔ ∃ member ∈ raws,
        (member ≠ .reference own ∨ raw = .reference own) ∧ ∃ cut output,
          run (withoutSelfReference own member) final = (cut,final) ∧
          execute cut environment final = .done output final ∧ Literal output atom) ∧
      (∀ row, Row result row ↔ ∃ member ∈ raws,
        (member ≠ .reference own ∨ raw = .reference own) ∧ ∃ cut output,
          run (withoutSelfReference own member) final = (cut,final) ∧
          execute cut environment final = .done output final ∧ Row output row) ∧
      (result.referenceOf = .empty ↔ ∀ member ∈ raws,
        (member ≠ .reference own ∨ raw = .reference own) → ∀ cut output,
          run (withoutSelfReference own member) final = (cut,final) →
          execute cut environment final = .done output final → output.referenceOf = .empty) := by
  refine ⟨built_done,?_,?_,effects.1,ready,not_retained,?_⟩
  · cbv
    exact List.mem_cons_self
  · cbv
    intro impossible
    cases impossible
  · obtain ⟨values,rawHeap,filters,outputs,middle,filtered,filterHeap,result,final,many,rawContext,made,valuesAvailable,
      calls,parentFilter,parentDone,first,second,third,parentAvailable,resultAvailable,membersAvailable,filtersAvailable,outputsAvailable,
      parentWarm,parentStored,filtersWarm,storedWarm,sourceWarm,manyWarm,madeWarm,sources⟩ :=
      SourceCurrentGeneratedUnionPreparation.prepare expressions inputs before reader reader context raw effects.1 ready
        (grows_refl _) effects.2.2 own environment replacements
    obtain ⟨rfl,rfl⟩ := Outcome.done.inj (many.symm.trans many_done)
    have finalReplacements : Replacements final environment := fun name output found =>
      (first.trans (second.trans third)).available output (replacements name output found)
    have covered := SourceCurrentFilteredUnionCoverage.parts final third.ready raws membersAvailable raw filtered result own environment
      madeWarm parentWarm finalReplacements parentStored (members_warm final)
    have empty := SourceCurrentFilteredUnionCoverage.empty_iff final third.ready raws membersAvailable raw filtered result own environment
      madeWarm parentWarm finalReplacements parentStored (members_warm final)
    have filteredSame : filtered = .reference other := congrArg Prod.fst (parentWarm.symm.trans (parent_filter final))
    have resultSame : result = .empty := by
      rw [filteredSame] at parentStored
      exact (Outcome.done.inj (parentStored.symm.trans (other_call final))).1
    exact ⟨filters,outputs,middle,filtered,filterHeap,result,final,calls,parentFilter,parentDone,first,second,third,
      resultAvailable,membersAvailable,madeWarm,parent_filter final,other_call final,resultSame,
      own_filter final,own_call final,covered.1,covered.2,empty⟩

/-- Actual retained-member coverage excludes bare self while its independent reconstruction is a nonempty used Mu. -/
theorem bare_self_exception :
    build source [] empty = .done mu before ∧ used mu ∧ mu.referenceOf ≠ .empty ∧
    build (.union expressions) inputs before = .done raw reader ∧ Ready reader ∧
    ¬ ((.reference own : Value Nat Bool) ≠ .reference own ∨ raw = .reference own) ∧
    ∃ filters outputs middle filtered filterHeap result final,
      FilteredCalls own environment raws reader filters outputs middle ∧
      run (withoutSelfReference own raw) middle = (filtered,filterHeap) ∧
      execute filtered environment filterHeap = .done result final ∧
      Keeps reader middle ∧ Keeps middle filterHeap ∧ Keeps filterHeap final ∧
      Available final result ∧ InternedNestedProvenance.Values final raws ∧
      run (makeUnion raws) final = (raw,final) ∧
      run (withoutSelfReference own raw) final = (.reference other,final) ∧
      execute (.reference other) environment final = .done .empty final ∧ result = .empty ∧
      run (withoutSelfReference own (.reference own)) final = (.reference own,final) ∧
      execute (.reference own) environment final = .done mu final ∧
      (∀ atom, Literal result atom ↔ ∃ member ∈ raws,
        (member ≠ .reference own ∨ raw = .reference own) ∧ ∃ cut output,
          run (withoutSelfReference own member) final = (cut,final) ∧
          execute cut environment final = .done output final ∧ Literal output atom) ∧
      (∀ row, Row result row ↔ ∃ member ∈ raws,
        (member ≠ .reference own ∨ raw = .reference own) ∧ ∃ cut output,
          run (withoutSelfReference own member) final = (cut,final) ∧
          execute cut environment final = .done output final ∧ Row output row) ∧
      (result.referenceOf = .empty ↔ ∀ member ∈ raws,
        (member ≠ .reference own ∨ raw = .reference own) → ∀ cut output,
          run (withoutSelfReference own member) final = (cut,final) →
          execute cut environment final = .done output final → output.referenceOf = .empty) := checked

end MicroCFTA.UnionCoverageKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.UnionCoverageKernels.bare_self_exception
#print MicroCFTA.UnionCoverageKernels.bare_self_exception
#print axioms MicroCFTA.UnionCoverageKernels.bare_self_exception
