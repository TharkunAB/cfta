import MicroCFTA.InternedRecordDepthRoutes
import MicroCFTA.InternedFreshOrdinaryRootEncounter

/-!
# Repaired source construction with captured records returns a complete result

The source depth induction derives the decoded heap even for a pending
outcome. The exact pending encounter then supplies two actual source
routes. Their captured suffixes determine equal ordinary choices, which
contradicts the live ordinary mismatch required by that encounter.
-/
namespace MicroCFTA.InternedRecordDepthCompletion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedFreshOrdinaryActiveOrigins InternedFreshOrdinaryActiveReplay
open InternedFreshOrdinaryActiveSite InternedFreshOrdinarySourceHistory
open InternedFreshOrdinaryLevelReplay (ordinaryNames)
open InternedRecordDepthLevels
open InternedBinderProtocol (Reference NodeKey)

/-- An actual pending site with arbitrary captured records is impossible in a decoded final heap. -/
theorem site_impossible [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) (heap : InternedFreshOrdinaryDepthHeap.Heap final) : False := by
  obtain ⟨earlier, start, previous, finish, descriptors, previousDone, previousContext, suffix, captures, traces,
    oldDepth, afterDepth, oldOrdinary, afterOrdinary, record, oldDepthDone, oldOrdinaryDone, oldRequested, oldStored, oldDifferent,
    index, first, second, level, firstAt, secondAt, bodies, flag, named, unequal, live, present, below, captured⟩ :=
    InternedFreshOrdinaryJointMismatch.Site.mismatch site
  have depthGrowth : Grows site.before site.afterDepth := by
    simpa only [site.depthDone, Outcome.state] using
      (callback_growing site.body site.environment .depth site.before site.context.normal.facts.coherent.valid).2
  have ordinaryGrowth : Grows site.afterDepth final := by
    simpa only [site.ordinaryDone, Outcome.state] using
      (callback_growing site.body site.environment (.uninterned (ordinaryLevel origin.depth)) site.afterDepth
        site.depthContext.normal.facts.coherent.valid).2
  have beforeFinal := grows_trans depthGrowth ordinaryGrowth
  have cutAllocated : Grows origin.cut origin.allocated :=
    ⟨extends_refl _, InternedBinderProtocol.intern_grows _ _, extends_refl _, extends_refl _⟩
  have cutFinal := grows_trans cutAllocated (grows_trans site.initial beforeFinal)
  have earlierHeap : ∀ crossing ∈ earlier, InternedFreshOrdinaryDepthHeap.Heap crossing.before := by
    intro crossing member
    have depthGrowth : Grows crossing.before crossing.afterDepth := by
      simpa only [crossing.depthDone, Outcome.state] using
        (callback_growing crossing.body crossing.environment .depth crossing.before crossing.context.normal.facts.coherent.valid).2
    exact InternedFreshOrdinaryDepthHeap.of_grows _ final
      (grows_trans depthGrowth (grows_trans (traces crossing member).2 cutFinal)) heap
  have currentHeap : ∀ crossing ∈ site.crossings, InternedFreshOrdinaryDepthHeap.Heap crossing.before := by
    intro crossing member
    exact InternedFreshOrdinaryDepthHeap.of_grows _ final
      (grows_trans crossing.facts.2 (grows_trans (site.traces crossing member).2 beforeFinal)) heap
  have projected := InternedRecordDepthRoutes.Path.projected_names site.path earlier
    (.reference .depth :: origin.environment) (.reference (.interned origin.entry.identity) :: origin.environment)
    (by simp only [Origin.localInputs]) descriptors captures
    (project_cons origin.environment origin.environment .depth (.interned origin.entry.identity) rfl rfl)
    earlierHeap currentHeap
  have atIndex := congrArg (fun values => values[index]?) projected
  simp only [List.getElem?_map, firstAt, secondAt, Option.map_some, Option.some.injEq] at atIndex
  have equal : ordinaryLevel first.depth = level := by
    simpa only [InternedFreshOrdinaryProbeChoiceSites.Crossing.name, flag, ↓reduceIte, named, ordinaryNames,
      Reference.uninterned.injEq] using atIndex
  exact unequal equal

/-- Source construction in a complete valid decoded cache cannot stop at an unfinished recursive record. -/
theorem source_not_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) (covered : Covered [] state)
    (key : NodeKey) (final : State Symbol Guard) : build expression environment state ≠ .pending key final := by
  intro pending
  obtain ⟨origin, rooted, ⟨site⟩⟩ := InternedFreshOrdinaryRootEncounter.complete_site expression environment state
    context covered key final pending
  have finalHeap : InternedFreshOrdinaryDepthHeap.Heap final := by
    simpa only [pending, Outcome.state] using (InternedRecordDepthExecution.build_depth expression environment state context heap).heap
  exact site_impossible site finalHeap

/-- Every repaired source construction in a complete valid decoded cache returns a complete value and its actual cache. -/
theorem source_complete [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state environment)
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) (covered : Covered [] state) :
    ∃ value final, build expression environment state = .done value final := by
  cases result : build expression environment state with
  | done value final => exact ⟨value, final, rfl⟩
  | pending key final => exact False.elim (source_not_pending expression environment state context heap covered key final result)

end MicroCFTA.InternedRecordDepthCompletion
