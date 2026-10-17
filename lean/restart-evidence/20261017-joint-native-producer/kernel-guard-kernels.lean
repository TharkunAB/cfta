import MicroCFTA.SourceCurrentConstrainedCapKernelGuardHeap
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.InternedFreshOrdinaryCoverage

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.KernelGuardIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open SourceRecursiveIntersectionKernel
local notation "Guards" => SourceCurrentConstrainedCapGuardHeap.Heap
variable {Symbol Guard : Type}

/-- Two actual source constructions supply both operands and the guard heap for every bounded query outcome. -/
theorem constructed_queries [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (first second : Syntax Symbol Guard) :
    ∃ (left right : Value Symbol Guard) (middle after : State Symbol Guard),
      build first [] empty = .done left middle ∧ build second [] middle = .done right after ∧
      Guards annotation after ∧
      ∀ fuel, let machine : Machine Symbol Guard := ⟨after, Cache.emptyState⟩
        let actual := execute emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain left right machine
        Guards annotation actual.state.heap ∧
        Checked machine actual (fun final value => Available final.heap value) := by
  obtain ⟨left, middle, firstDone⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete first
  have firstReady := SourceEqualityRequiredCache.constructed first left middle firstDone
  have firstAvailable := (build_verified first [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result left middle firstDone
  have firstGuards : Guards annotation middle := by
    simpa only [firstDone, Outcome.state] using SourceCurrentConstrainedCapGuardExecution.closed_heap annotation first
  obtain ⟨right, after, secondDone⟩ := InternedRecordDepthCompletion.source_complete second [] middle
    firstReady.semantic.1 firstReady.semantic.2 firstReady.covered
  have secondChecked := build_verified second [] middle firstReady.semantic.1.normal.facts
    (by intro value member; cases member)
  have afterFacts : InternedNestedFacts.Facts after := by simpa only [secondDone, Outcome.state] using secondChecked.facts
  have growth : Grows middle after := by simpa only [secondDone, Outcome.state] using secondChecked.growth
  have history : Cache.Extends middle.nodes.issued after.nodes.issued := by
    simpa only [secondDone, Outcome.state] using secondChecked.history
  have leftAvailable := firstAvailable.grows middle after growth history
  have rightAvailable := secondChecked.result right after secondDone
  have afterSemantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap after := by
    simpa only [secondDone, Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source second [] middle
      firstReady.semantic (by intro value member; cases member)
  have afterGuards : Guards annotation after := by
    simpa only [secondDone, Outcome.state] using
      (SourceCurrentConstrainedCapGuardExecution.build_profile annotation second [] middle
        (SourceCurrentConstrainedCapGuardNative.context middle firstReady.semantic []
          (by intro value member; cases member)) firstGuards).heap
  refine ⟨left, right, middle, after, firstDone, secondDone, afterGuards, ?_⟩
  intro fuel
  dsimp only
  let machine : Machine Symbol Guard := ⟨after, Cache.emptyState⟩
  have valid : SourceRecursiveIntersectionKernel.Valid machine := ⟨afterFacts, Cache.empty_valid⟩
  exact ⟨SourceCurrentConstrainedCapKernelGuardHeap.execute_heap annotation emptyGuard conjoin fuel _ left right machine
      valid (empty_domain machine) leftAvailable rightAvailable afterSemantic afterGuards,
    execute_checked emptyGuard conjoin fuel _ left right machine valid (empty_domain machine) leftAvailable rightAvailable⟩

#print axioms constructed_queries
#check @constructed_queries
end MicroCFTA.KernelGuardIntegration
