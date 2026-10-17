import MicroCFTA.SourceCurrentOpenObservations
import MicroCFTA.SourceEqualityRequiredCache

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.OpenObservationKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedBinderProtocol (Reference NodeKey)
open InternedFreshOrdinaryConstruction (build)
open SourceCurrentOpenObservations
open MergedFreshOrdinaryGraph

private def source : Syntax Nat Bool :=
  .binder false (.union [.node [.mk 0 true []], .node [.mk 1 false [.var 0]]])
private def positive (value : Value Nat Bool) : Bool :=
  (InternedEdgeResidency.nodeEdges value).any (fun row => row.entry.key.symbol == 0 && row.entry.key.constraint)
private def observation : Option (Bool × Bool) :=
  match build source [] empty with
  | .done value before => match value with
    | .mu _ _ depth ordinary =>
      match InternedFreshOrdinaryStoredSubstitution.unfold value before with
      | .done result _ => some (InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary, positive result)
      | .pending .. => none
    | _ => none
  | .pending .. => none
set_option cbv.maxSteps 100000000 in
private theorem observed : observation = some (true, true) := by cbv

/-- An actual productive raw Mu builds from empty tables and constructs its own positive-row unfolding observations. -/
theorem initial_productive_mu :
    ∃ entry body depth ordinary before result after,
      build source [] empty = .done (.mu entry body depth ordinary) before ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
      InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) before = .done result after ∧
      positive result = true ∧
      ∀ count, Same count before [.mu entry body depth ordinary] [result] := by
  have computed := observed
  cases actual : build source [] empty with
  | pending key before => simp [observation, actual] at computed
  | done value before =>
    cases value with
    | empty | reference | node | union => simp [observation, actual] at computed
    | mu entry body depth ordinary =>
      have ready := SourceEqualityRequiredCache.constructed source _ before actual
      have physical := InternedFreshOrdinaryFacts.closed_verified source
      have available := physical.result _ before actual
      obtain ⟨result, after, completed, _, _, _, _, _, related⟩ :=
        unfold_complete before entry body depth ordinary ready.semantic ready.covered available
      simp only [observation, actual, completed, Option.some.injEq, Prod.mk.injEq] at computed
      exact ⟨entry, body, depth, ordinary, before, result, after, rfl,
        computed.1, completed, computed.2, related⟩

private theorem no_empty_seed (view : State Nat Bool) (target : Value Nat Bool)
    (actual : Productivity.Reachable (MergedFreshOrdinaryGraph.successors view) [] target) : False := by
  induction actual with
  | seed impossible => cases impossible
  | step _ _ ih => exact ih

/-- A bare Depth reference and Empty have equal row origins but distinct open observations in every view. -/
theorem bare_reference_is_observable (view : State Nat Bool) :
    (∀ row, Origin view [.reference .depth] row ↔ Origin view [.empty] row) ∧
      ¬ Same 0 view [.reference .depth] [.empty] := by
  constructor
  · intro row
    apply iff_of_false
    · intro origin
      have impossible := MergedFreshOrdinaryExposureCoverage.origin_terminal view (.reference .depth) rfl row origin
      cases impossible
    · exact origin_empty view row
  · intro related
    have present : ReferenceOrigin view [.reference .depth] .depth := .seed List.mem_cons_self
    have emptyReference := (related .depth).mp present
    have expanded := (reference_expand view .empty (fun _ impossible => by cases impossible) .depth).mp emptyReference
    exact no_empty_seed view (.reference .depth) expanded

end MicroCFTA.OpenObservationKernels

set_option linter.all true
set_option pp.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.OpenObservationKernels.initial_productive_mu
#print axioms MicroCFTA.OpenObservationKernels.initial_productive_mu
#check @MicroCFTA.OpenObservationKernels.bare_reference_is_observable
#print axioms MicroCFTA.OpenObservationKernels.bare_reference_is_observable
