import MicroCFTA.SourceCurrentNativeMuIssuedHistory
import MicroCFTA.SourceCurrentNativeMuGrowthWriters
import MicroCFTA.SourceCurrentGeneratedHistoricalContext

/-!
# Selected writers retain unused issued captures

Actual issued-reference paths recover the selected earlier publication.
The writer-to-reader suffix retains every issued node name. Both original
callback contexts and adjacent source/filter calls then hold at the reader.
The old four-table growth and writer contracts remain unchanged.
-/
namespace MicroCFTA.SourceCurrentNativeMuIssuedWriters
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuIssuedHistory
open SourceCurrentNativeMuGrowthHistory (reserve_growth publication_growth)


private theorem reserve_issued [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    Extends event.cut.nodes.issued event.allocated.nodes.issued := by
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  exact InternedFreshProbeKeys.intern_issued_extends event.cut.nodes event.key cutContext.base.normal.facts.coherent.valid.2

/-- A selected writer retains its exact prefix, callbacks, and later cache growth. -/
def Written [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (key : NodeKey) (value : Value Symbol Guard) : Prop :=
  ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
    key = event.key ∧ value = event.candidate ∧ event.afterBody.nodeRecords event.key = none ∧
    Nonempty (Path before event.before) ∧
    Nonempty (Path event.before event.afterDepth) ∧
    Nonempty (Path event.afterDepth event.cut) ∧
    Nonempty (Path event.allocated event.afterBody) ∧ Grows event.after after ∧ Extends event.after.nodes.issued after.nodes.issued

/-- A preceding actual path preserves the selected publication and its later heap. -/
theorem Written.prepend [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (earlier : Path before middle) (written : Written middle after key value) : Written before after key value := by
  obtain ⟨event, key, value, missing, ⟨first⟩, depth, ordinary, body, growth, issued⟩ := written
  exact ⟨event, key, value, missing, ⟨.trans earlier first⟩, depth, ordinary, body, growth, issued⟩

/-- Later cache growth retains the same writer and every earlier callback heap. -/
theorem Written.later [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : Written before middle key value) (growth : Grows middle after)
    (issued : Extends middle.nodes.issued after.nodes.issued) : Written before after key value := by
  obtain ⟨event, key, value, missing, first, depth, ordinary, body, earlier, earlierIssued⟩ := written
  exact ⟨event, key, value, missing, first, depth, ordinary, body, grows_trans earlier growth, extends_trans earlierIssued issued⟩

/-- The full issued-name receipt retains the earlier selected-writer growth witness. -/
theorem Written.forget [DecidableEq (EdgeKey Symbol Guard)]
    {before after : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : Written before after key value) : SourceCurrentNativeMuGrowthWriters.Written before after key value := by
  obtain ⟨event, key, value, missing, ⟨first⟩, ⟨depth⟩, ⟨ordinary⟩, ⟨body⟩, growth, _⟩ := written
  exact ⟨event,key,value,missing,⟨first.forget⟩,⟨depth.forget⟩,⟨ordinary.forget⟩,⟨body.forget⟩,growth⟩

/-- A final Mu was present initially or has an actual writer whose heap reaches this reader. -/
theorem writers [DecidableEq (EdgeKey Symbol Guard)] {before after : State Symbol Guard}
    (path : Path before after) (key : NodeKey) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      Written before after key (.mu entry body depth ordinary) := by
  induction path with
  | refl => exact Or.inl present
  | retain before after old _growth _issued => exact Or.inl (old key entry body depth ordinary present)
  | trans first next firstIH nextIH =>
      rcases nextIH present with old | written
      · rcases firstIH old with initial | written
        · exact Or.inl initial
        · exact Or.inr (written.later next.growth next.issued)
      · exact Or.inr (written.prepend first)
  | publication event depthPath ordinaryPath bodyPath depthIH ordinaryIH bodyIH =>
      have reserve : Path event.cut event.allocated :=
        .retain event.cut event.allocated (fun _ _ _ _ _ found => found) (reserve_growth event) (reserve_issued event)
      have cutGrowth : Grows event.cut event.after :=
        grows_trans (reserve_growth event) (grows_trans bodyPath.growth (publication_growth event))
      have depthGrowth : Grows event.afterDepth event.after := grows_trans ordinaryPath.growth cutGrowth
      have cutIssued : Extends event.cut.nodes.issued event.after.nodes.issued :=
        extends_trans (reserve_issued event) bodyPath.issued
      have depthIssued : Extends event.afterDepth.nodes.issued event.after.nodes.issued :=
        extends_trans ordinaryPath.issued cutIssued
      have prior (old : event.afterBody.nodeRecords key = some (.mu entry body depth ordinary)) :
          event.before.nodeRecords key = some (.mu entry body depth ordinary) ∨
            Written event.before event.after key (.mu entry body depth ordinary) := by
        rcases bodyIH old with allocated | written
        · rcases ordinaryIH allocated with afterDepth | written
          · rcases depthIH afterDepth with initial | written
            · exact Or.inl initial
            · exact Or.inr (written.later depthGrowth depthIssued)
          · exact Or.inr ((written.prepend depthPath).later cutGrowth cutIssued)
        · exact Or.inr ((written.prepend (.trans (.trans depthPath ordinaryPath) reserve)).later
            (publication_growth event) (extends_refl _))
      rcases record_cases event.afterBody.nodeRecords event.key key event.candidate
        (.mu entry body depth ordinary) present with old | ⟨sameKey, sameValue⟩
      · exact prior old
      · cases firstWrite : event.afterBody.nodeRecords event.key with
        | none => exact Or.inr ⟨event, sameKey, sameValue, firstWrite, ⟨.refl event.before⟩,
            ⟨depthPath⟩, ⟨ordinaryPath⟩, ⟨bodyPath⟩, grows_refl event.after, extends_refl _⟩
        | some previous =>
            apply prior
            change keepFirst event.afterBody.nodeRecords event.key event.candidate key =
              some (.mu entry body depth ordinary) at present
            simpa only [keepFirst, firstWrite] using present

/-- Empty initial caches supply a selected writer and its actual growth to the reader. -/
theorem from_empty [DecidableEq (EdgeKey Symbol Guard)] {after : State Symbol Guard}
    (path : Path empty after) (key : NodeKey) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    Written empty after key (.mu entry body depth ordinary) := by
  rcases writers path key entry body depth ordinary present with impossible | written
  · cases impossible
  · exact written

open InternedNestedConstruction (Outcome work)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceEqualityRequiredCache (Ready Keeps)

private theorem callback_replay [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (own : Reference) (before after reader : State Symbol Guard)
    (context : Context before (.reference own :: environment)) (filtered : Value Symbol Guard)
    (actual : InternedFreshOrdinaryConstruction.callback expression environment own before = .done filtered after)
    (current : Keeps after reader) :
    ∃ raw middle,
      build expression (.reference own :: environment) before = .done raw middle ∧
      run (withoutSelfReference own raw) middle = (filtered,after) ∧
      Context reader (.reference own :: environment) ∧ Keeps middle reader ∧
      Available reader raw ∧
      build expression (.reference own :: environment) reader = .done raw reader ∧
      run (withoutSelfReference own raw) reader = (filtered,reader) := by
  obtain ⟨raw,middle,built,cut⟩ := SourceCurrentNativeMuPublicationCallbacks.callback_raw expression environment own before filtered after actual
  have checked := build_verified expression _ before context.base.normal.facts context.base.inputs
  have returned : Context middle (.reference own :: environment) := by
    simpa only [built,Outcome.state] using context.build expression
  have available := checked.result raw middle built
  have filteredChecked := InternedNestedFacts.filter_verified own raw middle returned.base.normal.facts available
  have filterGrowth : Grows middle after := by
    simpa only [work,cut,Outcome.state] using filteredChecked.growth
  have filterIssued : Extends middle.nodes.issued after.nodes.issued := by
    simpa only [work,cut,Outcome.state] using filteredChecked.history
  have whole : Keeps middle reader :=
    ⟨current.ready,grows_trans filterGrowth current.growth,extends_trans filterIssued current.history⟩
  obtain ⟨readerContext,_,warm⟩ := SourceCurrentGeneratedHistoricalContext.replay expression _ before middle reader
    context raw built whole
  have filterWarm : run (withoutSelfReference own raw) reader = (filtered,reader) := by
    simpa only [cut] using replay (withoutSelfReference own raw) middle reader returned.base.normal.facts.coherent.valid
      (by rw [cut]; exact current.growth)
  exact ⟨raw,middle,built,cut,readerContext,whole,whole.available raw available,warm,filterWarm⟩

/-- The actual selected writer derives both original lexical contexts and adjacent raw/filter calls at a Ready reader. -/
theorem Written.raw_contexts [DecidableEq (EdgeKey Symbol Guard)]
    {before reader : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : Written before reader key value) (ready : Ready reader) :
    ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
      key = event.key ∧ value = event.candidate ∧
      ∃ rawOrdinary ordinaryHeap rawBody bodyHeap,
        build event.expression (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
          event.afterDepth = .done rawOrdinary ordinaryHeap ∧
        run (withoutSelfReference (.uninterned (ordinaryLevel event.depth)) rawOrdinary) ordinaryHeap = (event.ordinary,event.cut) ∧
        build event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated = .done rawBody bodyHeap ∧
        run (withoutSelfReference (.interned event.entry.identity) rawBody) bodyHeap = (event.body,event.afterBody) ∧
        Context reader (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment) ∧
        Context reader (.reference (.interned event.entry.identity) :: event.environment) ∧
        Keeps ordinaryHeap reader ∧ Keeps bodyHeap reader ∧
        Available reader rawOrdinary ∧ Available reader rawBody ∧
        build event.expression (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
          reader = .done rawOrdinary reader ∧
        run (withoutSelfReference (.uninterned (ordinaryLevel event.depth)) rawOrdinary) reader = (event.ordinary,reader) ∧
        build event.expression (.reference (.interned event.entry.identity) :: event.environment)
          reader = .done rawBody reader ∧
        run (withoutSelfReference (.interned event.entry.identity) rawBody) reader = (event.body,reader) := by
  obtain ⟨event,keySame,valueSame,_missing,_prefix,_depth,_ordinary,⟨bodyPath⟩,growth,issued⟩ := written
  have cutGrowth : Grows event.cut reader :=
    grows_trans (reserve_growth event) (grows_trans bodyPath.growth (grows_trans (publication_growth event) growth))
  have cutIssued : Extends event.cut.nodes.issued reader.nodes.issued :=
    extends_trans (reserve_issued event) (extends_trans bodyPath.issued issued)
  have cutCurrent : Keeps event.cut reader := ⟨ready,cutGrowth,cutIssued⟩
  have bodyCurrent : Keeps event.afterBody reader := ⟨ready,grows_trans (publication_growth event) growth,issued⟩
  obtain ⟨ordinaryEntry,cutEntry,bodyEntry⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have ordinaryContext := ordinaryEntry.local (.uninterned (ordinaryLevel event.depth))
    (InternedNestedProvenance.ordinary_available _ _)
  have bodyArgument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutEntry.base.normal.facts.coherent cutEntry.base.normal.facts.cached).2
  have bodyContext := bodyEntry.local (.interned event.entry.identity) bodyArgument
  obtain ⟨rawOrdinary,ordinaryHeap,ordinaryBuild,ordinaryFilter,ordinaryContextReader,ordinaryKept,ordinaryAvailable,ordinaryWarm,ordinaryFilterWarm⟩ :=
    callback_replay event.expression event.environment (.uninterned (ordinaryLevel event.depth)) event.afterDepth event.cut reader
      ordinaryContext event.ordinary event.ordinaryDone cutCurrent
  obtain ⟨rawBody,bodyHeap,bodyBuild,bodyFilter,bodyContextReader,bodyKept,bodyAvailable,bodyWarm,bodyFilterWarm⟩ :=
    callback_replay event.expression event.environment (.interned event.entry.identity) event.allocated event.afterBody reader
      bodyContext event.body event.bodyDone bodyCurrent
  exact ⟨event,keySame,valueSame,rawOrdinary,ordinaryHeap,rawBody,bodyHeap,ordinaryBuild,ordinaryFilter,bodyBuild,bodyFilter,
    ordinaryContextReader,bodyContextReader,ordinaryKept,bodyKept,ordinaryAvailable,bodyAvailable,ordinaryWarm,ordinaryFilterWarm,bodyWarm,bodyFilterWarm⟩

end MicroCFTA.SourceCurrentNativeMuIssuedWriters
