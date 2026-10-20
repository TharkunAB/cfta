import MicroCFTA.SourceCurrentNativeMuPublication

/-!
# Raw calls before actual Mu publication

Each normalized callback retains its actual raw build and filter pair.
Both raw return heaps precede the reserved body's final heap. The source
contexts come from the publication's actual historical context.
-/
namespace MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedNestedFacts InternedNestedProvenance InternedConstructionProvenance
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)

/-- A completed normalized callback exposes its exact earlier build and filter. -/
theorem callback_raw [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (before : State Symbol Guard)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : callback expression environment name before = .done value after) :
    ∃ raw middle, build expression (.reference name :: environment) before = .done raw middle ∧
      run (withoutSelfReference name raw) middle = (value, after) := by
  cases returned : build expression (.reference name :: environment) before with
  | pending key state => simp only [callback, returned, Outcome.bind] at actual; cases actual
  | done raw middle =>
      simp only [callback, returned, Outcome.bind, work, Outcome.done.injEq] at actual
      exact ⟨raw, middle, rfl, Prod.ext actual.1 actual.2⟩

/-- The literal callbacks retain contexts at both probe and reserved body entries. -/
theorem contexts [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    Context event.afterDepth event.environment ∧ Context event.cut event.environment ∧
      Context event.allocated event.environment := by
  have depthContext : Context event.afterDepth event.environment := by
    simpa only [event.depthDone, Outcome.state] using
      event.context.callback event.expression .depth (depth_available event.before)
  have cutContext : Context event.cut event.environment := by
    simpa only [event.ordinaryDone, Outcome.state] using
      depthContext.callback event.expression (.uninterned (ordinaryLevel event.depth))
        (ordinary_available event.afterDepth (ordinaryLevel event.depth))
  exact ⟨depthContext, cutContext, cutContext.reserve event.key⟩

/-- Raw ordinary and reserved calls precede the actual pre-publication body heap. -/
theorem raw_callbacks [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    ∃ rawOrdinary afterRawOrdinary rawBody afterRawBody,
      build event.expression (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
        event.afterDepth = .done rawOrdinary afterRawOrdinary ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel event.depth)) rawOrdinary) afterRawOrdinary =
        (event.ordinary, event.cut) ∧
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done rawBody afterRawBody ∧
      run (withoutSelfReference (.interned event.entry.identity) rawBody) afterRawBody =
        (event.body, event.afterBody) ∧
      Grows afterRawOrdinary event.afterBody ∧ Grows afterRawBody event.afterBody ∧
      Context event.afterDepth event.environment ∧ Context event.allocated event.environment := by
  obtain ⟨depthContext, cutContext, bodyContext⟩ := contexts event
  obtain ⟨rawOrdinary, afterRawOrdinary, ordinaryDone, ordinaryFilter⟩ :=
    callback_raw event.expression event.environment (.uninterned (ordinaryLevel event.depth))
      event.afterDepth event.ordinary event.cut event.ordinaryDone
  have bodyDone : callback event.expression event.environment (.interned event.entry.identity) event.allocated =
      .done event.body event.afterBody := event.bodyDone
  obtain ⟨rawBody, afterRawBody, rawBodyDone, bodyFilter⟩ :=
    callback_raw event.expression event.environment (.interned event.entry.identity)
      event.allocated event.body event.afterBody bodyDone
  have ordinaryInputs := (depthContext.local (.uninterned (ordinaryLevel event.depth))
    (ordinary_available event.afterDepth (ordinaryLevel event.depth))).base
  have rawOrdinaryFacts : Facts afterRawOrdinary := by
    simpa only [ordinaryDone, Outcome.state] using
      (InternedFreshOrdinaryFacts.build_verified event.expression _ event.afterDepth ordinaryInputs.normal.facts ordinaryInputs.inputs).facts
  have ordinaryGrowth : Grows afterRawOrdinary event.cut := by
    simpa only [ordinaryFilter] using
      (run_correct (withoutSelfReference (.uninterned (ordinaryLevel event.depth)) rawOrdinary)
        afterRawOrdinary rawOrdinaryFacts.coherent.valid).2
  have bodyArgument : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have bodyInputs := (bodyContext.local (.interned event.entry.identity) bodyArgument).base
  have rawBodyFacts : Facts afterRawBody := by
    simpa only [rawBodyDone, Outcome.state] using
      (InternedFreshOrdinaryFacts.build_verified event.expression _ event.allocated bodyInputs.normal.facts bodyInputs.inputs).facts
  have bodyGrowth : Grows afterRawBody event.afterBody := by
    simpa only [bodyFilter] using
      (run_correct (withoutSelfReference (.interned event.entry.identity) rawBody)
        afterRawBody rawBodyFacts.coherent.valid).2
  have callbackGrowth : Grows event.allocated event.afterBody := by
    simpa only [bodyDone, Outcome.state] using
      (callback_verified event.expression event.environment (.interned event.entry.identity)
        event.allocated bodyInputs.normal.facts bodyInputs.inputs).growth
  have reservedGrowth : Grows event.cut event.allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  exact ⟨rawOrdinary, afterRawOrdinary, rawBody, afterRawBody, ordinaryDone, ordinaryFilter,
    rawBodyDone, bodyFilter, grows_trans ordinaryGrowth (grows_trans reservedGrowth callbackGrowth),
    bodyGrowth, depthContext, bodyContext⟩

end MicroCFTA.SourceCurrentNativeMuPublicationCallbacks
