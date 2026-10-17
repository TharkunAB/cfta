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

private def ordinaryValue : Value Nat Bool :=
  .node {identity := 1, key := .node [1]}
    [.mk {identity := 1, key := ⟨0, [.node 0], true⟩}
      [.node {identity := 0, key := .node [0]}
        [.mk {identity := 0, key := ⟨1, [], false⟩} []] 0 []]] 0 []

private def badValue : Value Nat Bool :=
  .node {identity := 0, key := .node [0]} [.mk {identity := 0, key := ⟨0, [], false⟩} []] 0 []

private def winnerValue : Value Nat Bool :=
  .mu {identity := 3, key := .mu ⟨.node 0, .node 0⟩} badValue badValue badValue

set_option cbv.maxSteps 100000000 in
private theorem ordinary_computed :
    (match InternedFreshOrdinaryConstruction.build ordinaryPlan [] empty with
     | .done value _ => value | .pending .. => .empty) = ordinaryValue := by cbv

set_option cbv.maxSteps 100000000 in
private theorem winner_computed :
    (match InternedFreshOrdinaryConstruction.build winnerPlan [] empty with
     | .done value _ => value | .pending .. => .empty) = winnerValue := by cbv

/-- Initial construction has exact least depth two despite its allowed outer guard. -/
theorem constructed_least_two :
    ∃ after, InternedFreshOrdinaryConstruction.build ordinaryPlan [] empty = .done ordinaryValue after ∧
      profile (fun guard : Bool => guard = true) ordinaryValue = some 2 ∧
      Cap (fun guard : Bool => guard = true) 2 ordinaryValue ∧ ¬Cap (fun guard : Bool => guard = true) 1 ordinaryValue := by
  obtain ⟨value, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete ordinaryPlan
  have same : value = ordinaryValue := by simpa only [done] using ordinary_computed
  subst value
  have computed : profile (fun guard : Bool => guard = true) ordinaryValue = some 2 := by
    classical
    simp [ordinaryValue, profile, rows, SourceCurrentConstrainedCapGuardDepth.children, join, raise, guardCost]
  refine ⟨after, done, computed, (profile_minimal _ _ _ computed 2).mpr (Nat.le_refl _), ?_⟩
  intro smaller
  have impossible := (profile_minimal _ _ _ computed 1).mp smaller
  omega

/-- A real earlier raw Mu has nonhereditary finite probes and an exact-state smart warm return. -/
theorem constructed_positive_probe_warm :
    ∃ before, InternedFreshOrdinaryConstruction.build winnerPlan [] empty = .done winnerValue before ∧
      request true badValue badValue (fun _ state => .done .empty state) before = .done badValue before ∧
      InternedFreshOrdinaryDepthHeap.usesLocal badValue badValue = false ∧
      profile (fun guard : Bool => guard = true) badValue = some 1 ∧
      Cap (fun guard : Bool => guard = true) 1 badValue ∧ ¬SourceEqualityAnnotationLanguage.Annotated (fun guard : Bool => guard = true) badValue ∧
      profile (fun guard : Bool => guard = true) winnerValue = none := by
  obtain ⟨value, before, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete winnerPlan
  have same : value = winnerValue := by simpa only [done] using winner_computed
  subst value
  have physical := InternedFreshOrdinaryFacts.closed_verified winnerPlan
  have available := physical.result winnerValue before done
  have facts : Facts before := by simpa only [done, Outcome.state] using physical.facts
  have present : before.nodeRecords (muKey badValue badValue) = some winnerValue :=
    available.resident _ rfl
  obtain ⟨entry, installed, _⟩ := facts.coherent.nodes _ _ present
  have warm : request true badValue badValue (fun _ state => .done .empty state) before = .done badValue before := by
    simp only [InternedNestedConstruction.request, installed, present]
    rfl
  have computed : profile (fun guard : Bool => guard = true) badValue = some 1 := by
    classical
    simp [badValue, profile, rows, SourceCurrentConstrainedCapGuardDepth.children, join, raise, guardCost]
  refine ⟨before, done, warm, ?_, computed, (profile_minimal _ _ _ computed 1).mpr (Nat.le_refl _), ?_, ?_⟩
  · decide
  · intro annotated
    have zero := (profile_zero_iff _ _).mpr annotated
    rw [computed] at zero
    cases zero
  · simp only [winnerValue, profile, computed, Nat.one_ne_zero, Option.some.injEq, ite_false]

#print axioms constructed_least_two
#check @constructed_least_two
#print axioms constructed_positive_probe_warm
#check @constructed_positive_probe_warm
end MicroCFTA.GuardDepthKernels
