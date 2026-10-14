import MicroCFTA.InternedFreshOrdinaryRouteLevels
import MicroCFTA.InternedFreshOrdinaryRootEncounter

/-!
# Repaired closed source construction returns a complete result

The source depth induction derives the decoded heap even for a pending
outcome. The exact pending encounter then supplies two actual source
routes. Their captured suffixes determine equal ordinary choices, which
contradicts the live ordinary mismatch required by that encounter.
-/
namespace MicroCFTA.InternedFreshOrdinaryClosedCompletion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedFreshOrdinaryActiveOrigins InternedFreshOrdinaryActiveReplay
open InternedFreshOrdinaryActiveSite InternedFreshOrdinarySourceHistory
open InternedFreshOrdinaryLevelReplay
open InternedBinderProtocol (Reference NodeKey)

/-- An actual pending site with literal ancestor captures is impossible in a decoded final heap. -/
theorem site_impossible [DecidableEq (EdgeKey Symbol Guard)] {origin : Origin Symbol Guard key}
    {final : State Symbol Guard} (site : Site origin final) (names : List Reference)
    (inputs : origin.environment = names.map Value.reference) (heap : InternedFreshOrdinaryDepthHeap.Heap final) : False := by
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
  have projected := InternedFreshOrdinaryRouteLevels.Path.projected_names site.path earlier
    (.depth :: names) (.interned origin.entry.identity :: names)
    (by simp only [Origin.localInputs, inputs, List.map_cons]) descriptors
    (by simpa only [inputs, List.map_cons] using captures)
    (by simp only [List.map_cons, ordinaryNames]) earlierHeap currentHeap
  have atIndex := congrArg (fun values => values[index]?) projected
  simp only [List.getElem?_map, firstAt, secondAt, Option.map_some, Option.some.injEq] at atIndex
  have equal : ordinaryLevel first.depth = level := by
    simpa only [InternedFreshOrdinaryProbeChoiceSites.Crossing.name, flag, ↓reduceIte, named, ordinaryNames,
      Reference.uninterned.injEq] using atIndex
  exact unequal equal

/-- Literal source construction in a complete valid decoded cache cannot stop at an unfinished recursive record. -/
theorem literal_not_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) (covered : Covered [] state)
    (key : NodeKey) (final : State Symbol Guard) : build expression (names.map Value.reference) state ≠ .pending key final := by
  intro pending
  obtain ⟨origin, rooted, ⟨site⟩⟩ := InternedFreshOrdinaryRootEncounter.complete_site expression (names.map Value.reference) state
    context covered key final pending
  obtain ⟨crossings, path, histories⟩ := rooted
  have inputs : origin.environment = (crossings.map (fun crossing => crossing.name) ++ names).map Value.reference := by
    simpa only [List.map_append, List.map_map, Function.comp_def] using path.inputs
  have finalHeap : InternedFreshOrdinaryDepthHeap.Heap final := by
    simpa only [pending, Outcome.state] using (InternedFreshOrdinarySourceDepth.build_depth expression names state context heap).heap
  exact site_impossible site _ inputs finalHeap

/-- Every repaired literal-input construction in a complete valid decoded cache returns a complete value and its actual cache. -/
theorem literal_complete [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) (covered : Covered [] state) :
    ∃ value final, build expression (names.map Value.reference) state = .done value final := by
  cases result : build expression (names.map Value.reference) state with
  | done value final => exact ⟨value, final, rfl⟩
  | pending key final => exact False.elim (literal_not_pending expression names state context heap covered key final result)

/-- No repaired source expression built from empty captures and caches stops at an unfinished recursive record. -/
theorem closed_not_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (key : NodeKey) (final : State Symbol Guard) : build expression [] empty ≠ .pending key final :=
  literal_not_pending expression [] empty InternedFreshOrdinaryContext.empty_context
    InternedFreshOrdinaryDepthHeap.empty_heap empty_correct.2 key final

/-- Every repaired closed source expression returns a complete value and its actual final cache. -/
theorem closed_complete [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    ∃ value final, build expression [] empty = .done value final :=
  literal_complete expression [] empty InternedFreshOrdinaryContext.empty_context
    InternedFreshOrdinaryDepthHeap.empty_heap empty_correct.2

end MicroCFTA.InternedFreshOrdinaryClosedCompletion
