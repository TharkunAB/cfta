import MicroCFTA.SourceCurrentConstrainedCapGuardDepth
import MicroCFTA.SourceCurrentConstrainedCapWarmOccurrences

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.GuardDepthKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome request finish)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapGuardDepth

private def ordinaryPlan : Syntax Nat Bool := .node [.mk 0 true [.node [.mk 1 false []]]]
private def winnerPlan : Syntax Nat Bool := .binder false (.union [.var 0, .node [.mk 0 false []]])

private noncomputable def ordinaryObservation : Option Nat :=
  match InternedFreshOrdinaryConstruction.build ordinaryPlan [] empty with
  | .done value _ => profile (fun guard : Bool => guard = true) value
  | .pending .. => none

private theorem ordinary_observed : ordinaryObservation = some 2 := by
  classical
  simp [ordinaryObservation, ordinaryPlan, InternedFreshOrdinaryConstruction.build,
    InternedFreshOrdinaryConstruction.buildEdges, InternedFreshOrdinaryConstruction.buildMany,
    Outcome.bind, InternedNestedConstruction.work, makeNode, makeEdge, canonicalEdges, surviving, run,
    edgeStep, nodeStep, empty, Cache.intern, Cache.reserve, Cache.install, Cache.emptyState, Cache.keepFirst,
    Cache.put, identifyNode, EnumerationBuilderCaches.canonicalIds,
    profile, rows, children, join, raise, guardCost]

/-- An initial ordinary source has exact least depth two despite its allowed outer guard. -/
theorem constructed_least_two :
    ∃ value after, InternedFreshOrdinaryConstruction.build ordinaryPlan [] empty = .done value after ∧
      profile (fun guard : Bool => guard = true) value = some 2 ∧
      Cap (fun guard : Bool => guard = true) 2 value ∧ ¬Cap (fun guard : Bool => guard = true) 1 value := by
  have computed := ordinary_observed
  cases done : InternedFreshOrdinaryConstruction.build ordinaryPlan [] empty with
  | pending key after => simp [ordinaryObservation, done] at computed
  | done value after =>
      change profile (fun guard : Bool => guard = true) value = some 2 at computed
      refine ⟨value, after, rfl, computed, ?_, ?_⟩
      · exact (profile_minimal _ _ _ computed 2).mpr (Nat.le_refl _)
      · intro smaller
        have impossible := (profile_minimal _ _ _ computed 1).mp smaller
        omega

private noncomputable def winnerObservation : Option (Option Nat × Option Nat × Option Nat × Bool × Bool) :=
  match InternedFreshOrdinaryConstruction.build winnerPlan [] empty with
  | .done (.mu _ body depth ordinary) before =>
      match request true depth ordinary (fun _ state => .done .empty state) before with
      | .done result after => some (profile (fun guard : Bool => guard = true) body,
          profile (fun guard : Bool => guard = true) depth,
          profile (fun guard : Bool => guard = true) ordinary,
          InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary, result == body && decide (after = before))
      | .pending .. => none
  | _ => none

end MicroCFTA.GuardDepthKernels
