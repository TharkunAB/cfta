import MicroCFTA.SourceCurrentRetainedMuDirectedCase

/-!
# Generated membership through actual reader growth

Keeps transports source-generated pairs and their lexical inputs to a
later reader. Historical source and filter receipts remain unchanged.
Their actual warm calls replay at the later reader. This result concerns
membership only. It does not transport observations or prove simulation.
-/
namespace MicroCFTA.SourceCurrentGeneratedGrowth
open InternedConstructorTemplates InternedProbeProvenance
open InternedStoredSubstitution (Environment)
open SourceCurrentRetainedMuDirectedCase (Generated Inputs)
open SourceEqualityRequiredCache (Keeps)

variable [DecidableEq (EdgeKey Symbol Guard)]

mutual
/-- Actual retained cache growth preserves both values of each source-generated pair. -/
theorem generated {before later : State Symbol Guard} {first second : Value Symbol Guard}
    (member : Generated before first second) (kept : Keeps before later) : Generated later first second := by
  cases member with
  | refl value => exact .refl _
  | @filtered Atom expression values firstNames secondNames firstOwn secondOwn firstMap secondMap
      firstBefore secondBefore firstRawHeap secondRawHeap firstFilterHeap secondFilterHeap
      firstRaw secondRaw firstFiltered secondFiltered left right ready firstContext secondContext aliases
      selfTests paired firstReplacements secondReplacements firstAvailable secondAvailable firstBuild secondBuild
      firstFilter secondFilter firstGrowth secondGrowth firstFilteredGrowth secondFilteredGrowth
      firstWarmBuild secondWarmBuild firstWarmFilter secondWarmFilter firstDone secondDone =>
      have valid := ready.semantic.1.normal.facts.coherent.valid
      have firstFilterReplay := replay (withoutSelfReference firstOwn firstRaw) before later valid
        (by simpa only [firstWarmFilter] using kept.growth)
      have secondFilterReplay := replay (withoutSelfReference secondOwn secondRaw) before later valid
        (by simpa only [secondWarmFilter] using kept.growth)
      exact .filtered expression values firstNames secondNames firstOwn secondOwn firstMap secondMap
        firstBefore secondBefore firstRawHeap secondRawHeap firstFilterHeap secondFilterHeap
        firstRaw secondRaw firstFiltered secondFiltered _ _ kept.ready firstContext secondContext aliases
        selfTests (SourceCurrentGeneratedGrowth.inputs paired kept)
        (fun name value found => kept.available value (firstReplacements name value found))
        (fun name value found => kept.available value (secondReplacements name value found))
        (kept.available firstFiltered firstAvailable) (kept.available secondFiltered secondAvailable)
        firstBuild secondBuild firstFilter secondFilter
        (grows_trans firstGrowth kept.growth) (grows_trans secondGrowth kept.growth)
        (grows_trans firstFilteredGrowth kept.growth) (grows_trans secondFilteredGrowth kept.growth)
        (InternedFreshOrdinaryReplay.build_replay expression _ before later firstRaw before valid firstWarmBuild kept.growth)
        (InternedFreshOrdinaryReplay.build_replay expression _ before later secondRaw before valid secondWarmBuild kept.growth)
        (by simpa only [firstWarmFilter] using firstFilterReplay)
        (by simpa only [secondWarmFilter] using secondFilterReplay)
        (InternedFreshOrdinaryStoredSubstitution.execute_replay firstFiltered firstMap before later _ before valid firstDone kept.growth)
        (InternedFreshOrdinaryStoredSubstitution.execute_replay secondFiltered secondMap before later _ before valid secondDone kept.growth)
termination_by structural member

/-- Actual retained cache growth preserves lexical order, fixed bindings, and generated reference pairs. -/
theorem inputs {before later : State Symbol Guard} {first second : Environment Symbol Guard}
    {left right : List (Value Symbol Guard)} (member : Inputs before first second left right)
    (kept : Keeps before later) : Inputs later first second left right := by
  cases member with
  | nil first second => exact .nil first second
  | reference head backward tail =>
      exact .reference (generated head kept) (generated backward kept) (SourceCurrentGeneratedGrowth.inputs tail kept)
  | fixed value agree tail => exact .fixed value agree (SourceCurrentGeneratedGrowth.inputs tail kept)
termination_by structural member
end

end MicroCFTA.SourceCurrentGeneratedGrowth
