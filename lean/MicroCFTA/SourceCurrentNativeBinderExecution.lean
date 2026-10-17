import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks

/-!
# Actual completed binder execution

A completed repaired binder exposes both callbacks and the final request.
Its ordinary callback exposes the raw build before filtering. All contexts,
growth, issued history, and final probe availability follow from execution.
-/
namespace MicroCFTA.SourceCurrentNativeBinderExecution
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work request)
open InternedNestedFacts InternedNestedRequestFacts
open InternedNestedProvenance (Values depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open SourceCurrentConstrainedCapSourceHistory (Context)

/-- A completed binder retains the actual probe schedule and raw ordinary return. -/
theorem decompose [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before : State Symbol Guard)
    (value : Value Symbol Guard) (after : State Symbol Guard) (context : Context before environment)
    (actual : build (.binder smart body) environment before = .done value after) :
    ∃ depth afterDepth ordinary cut rawOrdinary afterRawOrdinary,
      callback body environment .depth before = .done depth afterDepth ∧
      callback body environment (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      request smart depth ordinary (callback body environment) cut = .done value after ∧
      Context afterDepth environment ∧ Context cut environment ∧ Context after environment ∧
      build body (.reference (.uninterned (ordinaryLevel depth)) :: environment) afterDepth =
        .done rawOrdinary afterRawOrdinary ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) rawOrdinary) afterRawOrdinary =
        (ordinary, cut) ∧
      Context afterRawOrdinary (.reference (.uninterned (ordinaryLevel depth)) :: environment) ∧
      Grows afterRawOrdinary after ∧ Extends afterRawOrdinary.nodes.issued after.nodes.issued ∧
      Available after depth ∧ Available after ordinary := by
  have finalContext : Context after environment := by
    simpa only [actual, Outcome.state] using context.build (.binder smart body)
  rw [build] at actual
  change ((callback body environment .depth before).bind fun depth afterDepth =>
    (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary cut =>
      request smart depth ordinary (callback body environment) cut) = .done value after at actual
  cases depthDone : callback body environment .depth before with
  | pending key current => simp only [depthDone, Outcome.bind] at actual; cases actual
  | done depth afterDepth =>
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available before)
      have depthChecked := callback_verified body environment .depth before context.base.normal.facts
        (context.local .depth (depth_available before)).base.inputs
      have depthAvailable := depthChecked.result depth afterDepth depthDone
      simp only [depthDone, Outcome.bind] at actual
      cases ordinaryDone : callback body environment (.uninterned (ordinaryLevel depth)) afterDepth with
      | pending key current => simp only [ordinaryDone] at actual; cases actual
      | done ordinary cut =>
          simp only [ordinaryDone] at actual
          have localContext := depthContext.local (.uninterned (ordinaryLevel depth))
            (ordinary_available afterDepth (ordinaryLevel depth))
          have cutContext : Context cut environment := by
            simpa only [ordinaryDone, Outcome.state] using depthContext.callback body
              (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth (ordinaryLevel depth))
          have ordinaryChecked := callback_verified body environment (.uninterned (ordinaryLevel depth))
            afterDepth depthContext.base.normal.facts localContext.base.inputs
          have ordinaryAvailable := ordinaryChecked.result ordinary cut ordinaryDone
          have depthAtCut : Available cut depth := by
            simpa only [ordinaryDone, Outcome.state] using ordinaryChecked.available depth depthAvailable
          have requestChecked := request_verified smart depth ordinary (callback body environment) cut
            cutContext.base.normal.facts depthAtCut ordinaryAvailable (by
              intro name current growth history facts argument
              apply callback_verified body environment name current facts
              intro chosen member
              rcases List.mem_cons.mp member with rfl | member
              · exact argument
              · exact (cutContext.base.inputs chosen member).grows cut current growth history)
          have requestGrowth : Grows cut after := by
            simpa only [actual, Outcome.state] using requestChecked.growth
          have requestHistory : Extends cut.nodes.issued after.nodes.issued := by
            simpa only [actual, Outcome.state] using requestChecked.history
          obtain ⟨rawOrdinary, afterRawOrdinary, rawDone, rawFilter⟩ :=
            SourceCurrentNativeMuPublicationCallbacks.callback_raw body environment
              (.uninterned (ordinaryLevel depth)) afterDepth ordinary cut ordinaryDone
          have rawContext : Context afterRawOrdinary (.reference (.uninterned (ordinaryLevel depth)) :: environment) := by
            simpa only [rawDone, Outcome.state] using localContext.build body
          have rawChecked := InternedFreshOrdinaryFacts.build_verified body _ afterDepth
            localContext.base.normal.facts localContext.base.inputs
          have rawAvailable := rawChecked.result rawOrdinary afterRawOrdinary rawDone
          have filtered := filter_verified (.uninterned (ordinaryLevel depth)) rawOrdinary afterRawOrdinary
            rawContext.base.normal.facts rawAvailable
          have filterGrowth : Grows afterRawOrdinary cut := by
            simpa only [work, rawFilter, Outcome.state] using filtered.growth
          have filterHistory : Extends afterRawOrdinary.nodes.issued cut.nodes.issued := by
            simpa only [work, rawFilter, Outcome.state] using filtered.history
          exact ⟨depth, afterDepth, ordinary, cut, rawOrdinary, afterRawOrdinary,
            rfl, ordinaryDone, actual, depthContext, cutContext, finalContext, rawDone, rawFilter,
            rawContext, grows_trans filterGrowth requestGrowth, extends_trans filterHistory requestHistory,
            depthAtCut.grows cut after requestGrowth requestHistory,
            ordinaryAvailable.grows cut after requestGrowth requestHistory⟩

end MicroCFTA.SourceCurrentNativeBinderExecution
