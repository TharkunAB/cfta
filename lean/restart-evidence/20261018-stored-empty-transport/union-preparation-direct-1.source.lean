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
        by simpa only [made] using InternedConstructorTemplates.replay (makeUnion values) middle reader
          middleContext.base.normal.facts.coherent.valid growth,
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

end MicroCFTA.SourceCurrentGeneratedUnionPreparation
