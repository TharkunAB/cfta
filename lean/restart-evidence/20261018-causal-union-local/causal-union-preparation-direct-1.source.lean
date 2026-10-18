import MicroCFTA.SourceCurrentGeneratedUnionPreparation

/-!
# Causal histories through actual union preparation

Initial reader facts construct the member and parent schedules. Each
actual filter retains the Mu history. Each actual stored call supplies
its local publication history. Their forward composition gives the final
causal reader without a history from the original source return.
-/
namespace MicroCFTA.SourceCurrentCausalUnionPreparation
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentGeneratedUnionPreparation (FilteredCalls)

private theorem filter_keeps [DecidableEq (EdgeKey Symbol Guard)] (own : Reference)
    (raw : Value Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before raw) : Keeps before (run (withoutSelfReference own raw) before).2 := by
  cases raw with
  | empty | reference | node | mu => exact SourceEqualityRequiredCache.pure_keeps before ready
  | union entry members level free =>
      by_cases chosen : members.any (fun value => value.referenceOf == .ref own) = true
      · simp only [withoutSelfReference,chosen,ite_true]
        exact (SourceEqualityNativeDemandHeapPrimitives.union _ before ready
          (fun value member => available.children value (List.mem_filter.mp member).1)).1
      · simp only [withoutSelfReference,chosen,Bool.false_eq_true,ite_false,run]
        exact SourceEqualityRequiredCache.pure_keeps before ready

private theorem stored_effect [DecidableEq (EdgeKey Symbol Guard)]
    (raw : Value Symbol Guard) (environment : Environment Symbol Guard) (before : State Symbol Guard)
    (ready : Ready before) (available : Available before raw) (replacements : Replacements before environment)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute raw environment before = .done result after) :
    Keeps before after ∧ Nonempty (History before after) := by
  obtain ⟨output,final,called,kept,_,history⟩ :=
    SourceCurrentStoredReconstruction.execute raw environment before ready available replacements
  have same := Outcome.done.inj (called.symm.trans actual)
  cases same.1
  cases same.2
  exact ⟨kept,history⟩

/-- Actual ordered member calls derive retained readiness and their complete publication history. -/
theorem calls_history [DecidableEq (EdgeKey Symbol Guard)]
    (own : Reference) (environment : Environment Symbol Guard)
    {values filters outputs : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (calls : FilteredCalls own environment values before filters outputs after)
    (ready : Ready before) (available : Values before values)
    (replacements : Replacements before environment) :
    Keeps before after ∧ Nonempty (History before after) := by
  induction calls with
  | nil state => exact ⟨SourceEqualityRequiredCache.pure_keeps state ready,⟨.refl state⟩⟩
  | cons raw raws before filtered afterFilter output middle filters outputs after filteredCall storedCall rest ih =>
      have first : Keeps before afterFilter := by
        simpa only [filteredCall] using filter_keeps own raw before ready (available raw List.mem_cons_self)
      have localHistory : History before afterFilter := by
        have history : History before (run (withoutSelfReference own raw) before).2 :=
          .retain before _ (InternedStoredMuOrigins.filter_noNewMu own raw before)
        simpa only [filteredCall] using history
      have filteredAvailable : Available afterFilter filtered :=
        (InternedNestedFacts.filter_verified own raw before ready.semantic.1.normal.facts
          (available raw List.mem_cons_self)).result filtered afterFilter
            (by simp only [work,filteredCall])
      obtain ⟨second,⟨storedHistory⟩⟩ := stored_effect filtered environment afterFilter first.ready filteredAvailable
        (fun name value found => first.available value (replacements name value found)) output middle storedCall
      have whole := first.trans second
      obtain ⟨third,⟨tailHistory⟩⟩ := ih whole.ready
        (fun value member => whole.available value (available value (List.mem_cons_of_mem _ member)))
        (fun name value found => whole.available value (replacements name value found))
      exact ⟨whole.trans third,⟨.trans localHistory (.trans storedHistory tailHistory)⟩⟩

/-- Initial causal reader facts construct full member and parent schedules at a produced causal reader. -/
theorem prepare [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after reader : State Symbol Guard) (context : Context before inputs)
    (raw : Value Symbol Guard)
    (actual : build (.union expressions) inputs before = .done raw after)
    (ready : Ready reader) (history : History empty reader)
    (growth : Grows after reader) (available : Available reader raw)
    (own : Reference) (environment : Environment Symbol Guard) (replacements : Replacements reader environment) :
    ∃ values rawHeap filters outputs middle filtered filterHeap result final,
      buildMany expressions inputs before = .done values rawHeap ∧
      Context rawHeap inputs ∧ run (makeUnion values) rawHeap = (raw,after) ∧
      Values reader values ∧
      FilteredCalls own environment values reader filters outputs middle ∧
      run (withoutSelfReference own raw) middle = (filtered,filterHeap) ∧
      execute filtered environment filterHeap = .done result final ∧
      Keeps reader middle ∧ Keeps middle filterHeap ∧ Keeps filterHeap final ∧
      Available final filtered ∧ Available final result ∧ Values final values ∧
      Values final filters ∧ Values final outputs ∧
      run (withoutSelfReference own raw) final = (filtered,final) ∧
      execute filtered environment final = .done result final ∧
      All₂ (fun raw filtered => run (withoutSelfReference own raw) final = (filtered,final)) values filters ∧
      All₂ (fun filtered output => execute filtered environment final = .done output final) filters outputs ∧
      build (.union expressions) inputs final = .done raw final ∧
      buildMany expressions inputs final = .done values final ∧
      run (makeUnion values) final = (raw,final) ∧
      All₂ (fun expression value => ∃ current returned,
        Context current inputs ∧ build expression inputs current = .done value returned ∧
        Grows returned final ∧ build expression inputs final = .done value final) expressions values ∧
      Nonempty (History reader middle) ∧ Nonempty (History middle filterHeap) ∧
      Nonempty (History filterHeap final) ∧ Nonempty (History empty final) := by
  obtain ⟨values,rawHeap,filters,outputs,middle,filtered,filterHeap,result,final,many,rawContext,made,
    valuesAvailable,calls,parentFilter,parentDone,first,second,third,filteredAvailable,resultAvailable,
    finalValues,finalFilters,finalOutputs,parentWarm,parentStored,filtersWarm,storedWarm,sourceWarm,
    manyWarm,madeWarm,sources⟩ :=
    SourceCurrentGeneratedUnionPreparation.prepare expressions inputs before after reader context raw actual
      ready growth available own environment replacements
  obtain ⟨_,⟨memberHistory⟩⟩ := calls_history own environment calls ready valuesAvailable replacements
  have parentHistory : History middle filterHeap := by
    have localHistory : History middle (run (withoutSelfReference own raw) middle).2 :=
      .retain middle _ (InternedStoredMuOrigins.filter_noNewMu own raw middle)
    simpa only [parentFilter] using localHistory
  have parentAvailable : Available filterHeap filtered :=
    (InternedNestedFacts.filter_verified own raw middle first.ready.semantic.1.normal.facts
      (first.available raw available)).result filtered filterHeap (by simp only [work,parentFilter])
  obtain ⟨_,⟨storedHistory⟩⟩ := stored_effect filtered environment filterHeap second.ready parentAvailable
    (fun name value found => (first.trans second).available value (replacements name value found)) result final parentDone
  have finalHistory : History empty final :=
    .trans history (.trans memberHistory (.trans parentHistory storedHistory))
  exact ⟨values,rawHeap,filters,outputs,middle,filtered,filterHeap,result,final,many,rawContext,made,
    valuesAvailable,calls,parentFilter,parentDone,first,second,third,filteredAvailable,resultAvailable,
    finalValues,finalFilters,finalOutputs,parentWarm,parentStored,filtersWarm,storedWarm,sourceWarm,
    manyWarm,madeWarm,sources,⟨memberHistory⟩,⟨parentHistory⟩,⟨storedHistory⟩,⟨finalHistory⟩⟩

end MicroCFTA.SourceCurrentCausalUnionPreparation
