import MicroCFTA.SourceCurrentGeneratedUnionPreparation

/-!
# Historical source contexts at actual later readers

A completed source call retains its original lexical inputs. Actual Keeps
retains their issued names through the later execution. The resulting reader
context makes each source replay a valid adjacent filter entry. The theorem
does not infer this history from four-table growth alone.
-/
namespace MicroCFTA.SourceCurrentGeneratedHistoricalContext
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceEqualityRequiredCache (Keeps)
open SourceCurrentGeneratedUnionPreparation (FilteredCalls)

/-- A real source return and subsequent Keeps derive the original lexical context and exact replay. -/
theorem replay [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
    (before after reader : State Symbol Guard) (context : Context before inputs)
    (raw : Value Symbol Guard) (actual : build expression inputs before = .done raw after)
    (current : Keeps after reader) :
    Context reader inputs ∧ Keeps before reader ∧
      build expression inputs reader = .done raw reader := by
  have checked := build_verified expression inputs before context.base.normal.facts context.base.inputs
  have growth : Grows before after := by simpa only [actual,Outcome.state] using checked.growth
  have issued : Extends before.nodes.issued after.nodes.issued := by
    simpa only [actual,Outcome.state] using checked.history
  have whole : Keeps before reader :=
    ⟨current.ready,grows_trans growth current.growth,extends_trans issued current.history⟩
  have inputsAvailable : Values reader inputs :=
    fun value member => whole.available value (context.base.inputs value member)
  exact ⟨⟨SourceRecursiveIntersectionSemanticHeap.context reader current.ready.semantic inputs inputsAvailable,
    current.ready.semantic.2⟩,whole,
    InternedFreshOrdinaryReplay.build_replay expression inputs before reader raw after
      context.base.normal.facts.coherent.valid actual current.growth⟩

/-- Actual union preparation supplies one genuine source context for all final adjacent member calls. -/
theorem union_prepare [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after reader : State Symbol Guard) (context : Context before inputs)
    (raw : Value Symbol Guard)
    (actual : build (.union expressions) inputs before = .done raw after)
    (current : Keeps after reader)
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
      Context final inputs ∧ Keeps before final ∧
      run (withoutSelfReference own raw) final = (filtered,final) ∧
      execute filtered environment final = .done result final ∧
      All₂ (fun raw filtered => run (withoutSelfReference own raw) final = (filtered,final)) values filters ∧
      All₂ (fun filtered output => execute filtered environment final = .done output final) filters outputs ∧
      build (.union expressions) inputs final = .done raw final ∧
      buildMany expressions inputs final = .done values final ∧
      run (makeUnion values) final = (raw,final) ∧
      All₂ (fun expression value => build expression inputs final = .done value final) expressions values := by
  have checked := build_verified (.union expressions) inputs before context.base.normal.facts context.base.inputs
  have available : Available reader raw := current.available raw (checked.result raw after actual)
  obtain ⟨values,rawHeap,filters,outputs,middle,filtered,filterHeap,result,final,many,rawContext,made,
    valuesAvailable,calls,parentFilter,parentDone,first,second,third,parentAvailable,resultAvailable,
    finalValues,finalFilters,finalOutputs,parentWarm,parentStored,filtersWarm,storedWarm,
    sourceWarm,manyWarm,madeWarm,sources⟩ :=
    SourceCurrentGeneratedUnionPreparation.prepare expressions inputs before after reader context raw actual
      current.ready current.growth available own environment replacements
  have finalCurrent := current.trans (first.trans (second.trans third))
  obtain ⟨finalContext,whole,_⟩ := replay (.union expressions) inputs before after final context raw actual finalCurrent
  have members : All₂ (fun expression value => build expression inputs final = .done value final) expressions values :=
    All₂.imp (fun _ _ source => by
      obtain ⟨_,_,_,_,_,warm⟩ := source
      exact warm) sources
  exact ⟨values,rawHeap,filters,outputs,middle,filtered,filterHeap,result,final,many,rawContext,made,
    valuesAvailable,calls,parentFilter,parentDone,first,second,third,parentAvailable,resultAvailable,
    finalValues,finalFilters,finalOutputs,finalContext,whole,parentWarm,parentStored,filtersWarm,storedWarm,
    sourceWarm,manyWarm,madeWarm,members⟩

end MicroCFTA.SourceCurrentGeneratedHistoricalContext
