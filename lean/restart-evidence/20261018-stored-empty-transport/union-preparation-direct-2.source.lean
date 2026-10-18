import MicroCFTA.SourceCurrentGeneratedUnionCases
import MicroCFTA.SourceCurrentConstrainedCapSourceHistory
import MicroCFTA.SourceCurrentStoredFilterReconstruction

/-!
# Cold source-union member preparation

Actual union construction retains every original source result at the reader.
Primitive references use the parent free-name support. Nonprimitive records
use the retained cache payload and its complete available contents. Finite
member filters and stored calls execute before their final warm replays.
No lexical availability at the reader or observation law is assumed.
-/
namespace MicroCFTA.SourceCurrentGeneratedUnionPreparation
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceEqualityRequiredCache (Ready Keeps)
open InternedBinderProtocol (Reference)

private theorem retained_available (value parent : Value Symbol Guard) (before reader : State Symbol Guard)
    (ready : Ready reader) (growth : Grows before reader) (old : Available before value)
    (available : Available reader parent) (support : ∀ name ∈ value.free, name ∈ parent.free) :
    Available reader value := by
  cases value with
  | empty => exact empty_available reader
  | reference name =>
      apply reference_available reader name
      intro identity member
      exact available.issued identity (support (.interned identity) member)
  | node entry rows level free =>
      exact ready.semantic.1.normal.facts.cached.nodes entry.key _
        (growth.nodeRecords _ _ (old.resident entry rfl))
  | union entry members level free =>
      exact ready.semantic.1.normal.facts.cached.nodes entry.key _
        (growth.nodeRecords _ _ (old.resident entry rfl))
  | mu entry body depth ordinary =>
      exact ready.semantic.1.normal.facts.cached.nodes entry.key _
        (growth.nodeRecords _ _ (old.resident entry rfl))

private def SourceCall [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
    (reader : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∃ before after, Context before inputs ∧ build expression inputs before = .done value after ∧
    Grows after reader ∧ build expression inputs reader = .done value reader

private theorem source_children [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after reader : State Symbol Guard) (context : Context before inputs)
    (values : List (Value Symbol Guard)) (called : buildMany expressions inputs before = .done values after)
    (growth : Grows after reader) : All₂ (fun expression value => SourceCall expression inputs reader value) expressions values := by
  induction expressions generalizing before values with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at called
      obtain ⟨rfl,rfl⟩ := called
      exact .nil
  | cons expression expressions ih =>
      cases one : build expression inputs before with
      | pending key state => simp only [buildMany,one,Outcome.bind] at called; cases called
      | done value middle =>
          cases tail : buildMany expressions inputs middle with
          | pending key state => simp only [buildMany,one,tail,Outcome.bind] at called; cases called
          | done remaining final =>
              simp only [buildMany,one,tail,Outcome.bind,Outcome.done.injEq] at called
              obtain ⟨rfl,rfl⟩ := called
              have middleContext : Context middle inputs := by simpa only [one,Outcome.state] using context.build expression
              have tailGrowth : Grows middle reader := grows_trans
                (by simpa only [tail,Outcome.state] using
                  (buildMany_verified expressions inputs middle middleContext.base.normal.facts middleContext.base.inputs).growth) growth
              exact .cons ⟨before,middle,context,one,tailGrowth,
                InternedFreshOrdinaryReplay.build_replay expression inputs before reader value middle
                  context.base.normal.facts.coherent.valid one tailGrowth⟩
                (ih middle middleContext remaining tail)

/-- Actual historical union construction recovers all original raw source members at the reader. -/
theorem source_members [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after reader : State Symbol Guard) (context : Context before inputs)
    (raw : Value Symbol Guard)
    (actual : build (.union expressions) inputs before = .done raw after)
    (ready : Ready reader) (growth : Grows after reader) (available : Available reader raw) :
    ∃ values middle,
      buildMany expressions inputs before = .done values middle ∧
      Context middle inputs ∧ run (makeUnion values) middle = (raw,after) ∧
      Grows middle reader ∧ Values reader values ∧
      buildMany expressions inputs reader = .done values reader ∧
      run (makeUnion values) reader = (raw,reader) ∧
      All₂ (fun expression value => ∃ current returned,
        Context current inputs ∧ build expression inputs current = .done value returned ∧
        Grows returned reader ∧ build expression inputs reader = .done value reader) expressions values := by
  cases called : buildMany expressions inputs before with
  | pending key state => simp only [build,called,Outcome.bind] at actual; cases actual
  | done values middle =>
      have made : run (makeUnion values) middle = (raw,after) :=
        Prod.ext (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).1
          (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).2
      have checked := buildMany_verified expressions inputs before context.base.normal.facts context.base.inputs
      have middleContext : Context middle inputs := by simpa only [called,Outcome.state] using context.many expressions
      have valuesAvailable := checked.result values middle called
      have finalGrowth : Grows middle reader := grows_trans
        (by simpa only [made] using (run_correct (makeUnion values) middle middleContext.base.normal.facts.coherent.valid).2) growth
      have recovered : Values reader values := by
        intro value member
        apply retained_available value raw middle reader ready finalGrowth (valuesAvailable value member) available
        intro name named
        have free := InternedNormalizationFree.makeUnion_free values middle middleContext.base.normal.facts.coherent
          middleContext.base.normal.facts.cached middleContext.base.normal.facts.linked middleContext.base.normal.live
          valuesAvailable name
        rw [made] at free
        exact free.mpr ⟨value,member,named⟩
      exact ⟨values,middle,rfl,middleContext,made,finalGrowth,recovered,
        InternedFreshOrdinaryReplay.buildMany_replays expressions inputs before reader values middle
          context.base.normal.facts.coherent.valid called finalGrowth,
        (by simpa only [made] using (InternedConstructorTemplates.replay (makeUnion values) middle reader
          middleContext.base.normal.facts.coherent.valid growth)),
        source_children expressions inputs before middle reader context values called finalGrowth⟩

/-- Each source member performs its root filter and its stored call before the next member starts. -/
inductive FilteredCalls [DecidableEq (EdgeKey Symbol Guard)] (own : Reference)
    (environment : Environment Symbol Guard) :
    List (Value Symbol Guard) → State Symbol Guard → List (Value Symbol Guard) →
      List (Value Symbol Guard) → State Symbol Guard → Prop where
  /-- Empty member lists leave the current state unchanged. -/
  | nil (state) : FilteredCalls own environment [] state [] [] state
  /-- The next member starts after this member's actual stored return. -/
  | cons (raw raws before filtered afterFilter output middle filters outputs after)
      (filteredCall : run (withoutSelfReference own raw) before = (filtered,afterFilter))
      (storedCall : execute filtered environment afterFilter = .done output middle)
      (rest : FilteredCalls own environment raws middle filters outputs after) :
      FilteredCalls own environment (raw::raws) before (filtered::filters) (output::outputs) after

private theorem filter_keeps [DecidableEq (EdgeKey Symbol Guard)] (own : Reference)
    (raw : Value Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before raw) : Keeps before (run (withoutSelfReference own raw) before).2 := by
  cases raw with
  | empty | reference | node | mu => exact SourceEqualityRequiredCache.pure_keeps before ready
  | union entry members level free =>
      by_cases chosen : members.any (fun value => value.referenceOf == .ref own) = true
      · simp only [withoutSelfReference, chosen, ↓reduceIte]
        exact (SourceEqualityNativeDemandHeapPrimitives.union _ before ready
          (fun value member => available.children value (List.mem_filter.mp member).1)).1
      · simp only [withoutSelfReference, chosen, Bool.false_eq_true, ↓reduceIte, run]
        exact SourceEqualityRequiredCache.pure_keeps before ready


private theorem filter_available [DecidableEq (EdgeKey Symbol Guard)]
    (own : Reference) (raw : Value Symbol Guard) (before : State Symbol Guard)
    (ready : Ready before) (available : Available before raw) :
    Available (run (withoutSelfReference own raw) before).2 (run (withoutSelfReference own raw) before).1 := by
  apply (InternedNestedFacts.filter_verified own raw before ready.semantic.1.normal.facts available).result
  rfl

private theorem prepare_members [DecidableEq (EdgeKey Symbol Guard)]
    (own : Reference) (environment : Environment Symbol Guard) (raws : List (Value Symbol Guard))
    (before : State Symbol Guard) (ready : Ready before) (available : Values before raws)
    (replacements : Replacements before environment) :
    ∃ filters outputs after,
      FilteredCalls own environment raws before filters outputs after ∧ Keeps before after ∧
      Values after filters ∧ Values after outputs ∧
      All₂ (fun raw filtered => run (withoutSelfReference own raw) after = (filtered,after)) raws filters ∧
      All₂ (fun filtered output => execute filtered environment after = .done output after) filters outputs := by
  induction raws generalizing before with
  | nil => exact ⟨[],[],before,.nil before,SourceEqualityRequiredCache.pure_keeps before ready,
      by intro value member; cases member,by intro value member; cases member,.nil,.nil⟩
  | cons raw raws ih =>
      let filtered := run (withoutSelfReference own raw) before
      have first : Keeps before filtered.2 := filter_keeps own raw before ready (available raw List.mem_cons_self)
      have filteredAvailable : Available filtered.2 filtered.1 := filter_available own raw before ready (available raw List.mem_cons_self)
      obtain ⟨output,middle,called,second,outputAvailable,_⟩ := SourceCurrentStoredReconstruction.execute filtered.1 environment
        filtered.2 first.ready filteredAvailable
        (fun name value found => first.available value (replacements name value found))
      have prefix := first.trans second
      obtain ⟨filters,outputs,after,calls,third,filtersAvailable,outputsAvailable,filtersWarm,storedWarm⟩ := ih middle prefix.ready
        (fun value member => prefix.available value (available value (List.mem_cons_of_mem _ member)))
        (fun name value found => prefix.available value (replacements name value found))
      have rest := second.trans third
      have headFilter : run (withoutSelfReference own raw) after = (filtered.1,after) :=
        InternedConstructorTemplates.replay (withoutSelfReference own raw) before after ready.semantic.1.normal.facts.coherent.valid
          rest.growth
      have headStored : execute filtered.1 environment after = .done output after :=
        InternedFreshOrdinaryReplay.build_replay (encode (leaves filtered.1) [] filtered.1)
          ((leaves filtered.1).map (input environment)) filtered.2 after output middle
          first.ready.semantic.1.normal.facts.coherent.valid called third.growth
      refine ⟨filtered.1::filters,output::outputs,after,.cons raw raws before filtered.1 filtered.2 output middle filters outputs after
        rfl called calls,prefix.trans third,?_,?_,.cons headFilter filtersWarm,.cons headStored storedWarm⟩
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact rest.available _ filteredAvailable
        · exact filtersAvailable value member
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact third.available _ outputAvailable
        · exact outputsAvailable value member

private theorem filters_replay [DecidableEq (EdgeKey Symbol Guard)]
    (own : Reference) (before after : State Symbol Guard) (valid : Valid before) (growth : Grows before after)
    {raws filters : List (Value Symbol Guard)}
    (calls : All₂ (fun raw filtered => run (withoutSelfReference own raw) before = (filtered,before)) raws filters) :
    All₂ (fun raw filtered => run (withoutSelfReference own raw) after = (filtered,after)) raws filters := by
  induction calls with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (by simpa only [head] using (InternedConstructorTemplates.replay _ before after valid growth)) ih

private theorem stored_replay [DecidableEq (EdgeKey Symbol Guard)]
    (environment : Environment Symbol Guard) (before after : State Symbol Guard) (valid : Valid before) (growth : Grows before after)
    {filters outputs : List (Value Symbol Guard)}
    (calls : All₂ (fun filtered output => execute filtered environment before = .done output before) filters outputs) :
    All₂ (fun filtered output => execute filtered environment after = .done output after) filters outputs := by
  induction calls with
  | nil => exact .nil
  | @cons filtered output filters outputs head tail ih =>
      exact .cons (InternedFreshOrdinaryReplay.build_replay (encode (leaves filtered) [] filtered)
        ((leaves filtered).map (input environment)) before after output before valid head growth) ih

/-- Initial union history constructs cold member filters and stored calls, then every final warm replay. -/
theorem prepare [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before after reader : State Symbol Guard) (context : Context before inputs)
    (raw : Value Symbol Guard)
    (actual : build (.union expressions) inputs before = .done raw after)
    (ready : Ready reader) (growth : Grows after reader) (available : Available reader raw)
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
        Grows returned final ∧ build expression inputs final = .done value final) expressions values := by
  obtain ⟨values,rawHeap,many,rawContext,made,rawGrowth,valuesAvailable,manyWarm,madeWarm,_⟩ :=
    source_members expressions inputs before after reader context raw actual ready growth available
  obtain ⟨filters,outputs,middle,calls,first,filtersAvailable,outputsAvailable,filtersWarm,storedWarm⟩ :=
    prepare_members own environment values reader ready valuesAvailable replacements
  let filtered := run (withoutSelfReference own raw) middle
  have second : Keeps middle filtered.2 := filter_keeps own raw middle first.ready (first.available raw available)
  have filteredAvailable : Available filtered.2 filtered.1 := filter_available own raw middle first.ready (first.available raw available)
  obtain ⟨result,final,called,third,resultAvailable,_⟩ := SourceCurrentStoredReconstruction.execute filtered.1 environment filtered.2
    second.ready filteredAvailable
    (fun name value found => (first.trans second).available value (replacements name value found))
  have rest := second.trans third
  have whole := first.trans rest
  have finalGrowth := grows_trans growth whole.growth
  have rawFinalGrowth := grows_trans rawGrowth whole.growth
  have filtersFinal := filters_replay own middle final first.ready.semantic.1.normal.facts.coherent.valid rest.growth filtersWarm
  have storedFinal := stored_replay environment middle final first.ready.semantic.1.normal.facts.coherent.valid rest.growth storedWarm
  have parentFilter : run (withoutSelfReference own raw) final = (filtered.1,final) :=
    InternedConstructorTemplates.replay (withoutSelfReference own raw) middle final first.ready.semantic.1.normal.facts.coherent.valid third.growth
  have parentStored : execute filtered.1 environment final = .done result final :=
    InternedFreshOrdinaryReplay.build_replay (encode (leaves filtered.1) [] filtered.1)
      ((leaves filtered.1).map (input environment)) filtered.2 final result final
      second.ready.semantic.1.normal.facts.coherent.valid called (grows_refl _)
  refine ⟨values,rawHeap,filters,outputs,middle,filtered.1,filtered.2,result,final,many,rawContext,made,valuesAvailable,
    calls,rfl,called,first,second,third,third.available _ filteredAvailable,resultAvailable,
    (fun value member => whole.available value (valuesAvailable value member)),
    (fun value member => rest.available value (filtersAvailable value member)),
    (fun value member => rest.available value (outputsAvailable value member)),parentFilter,parentStored,filtersFinal,storedFinal,
    InternedFreshOrdinaryReplay.build_replay (.union expressions) inputs before final raw after
      context.base.normal.facts.coherent.valid actual finalGrowth,
    InternedFreshOrdinaryReplay.buildMany_replays expressions inputs before final values rawHeap
      context.base.normal.facts.coherent.valid many rawFinalGrowth,
    ?_,source_children expressions inputs before rawHeap final context values many rawFinalGrowth⟩
  simpa only [made] using (InternedConstructorTemplates.replay (makeUnion values) rawHeap final
    rawContext.base.normal.facts.coherent.valid finalGrowth)

end MicroCFTA.SourceCurrentGeneratedUnionPreparation
