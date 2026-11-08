import MicroCFTA.SourceSynthesisGuardRegions
import MicroCFTA.SourceEqualityConstraintRegions

/-!
# Inherited regions at actual application and filter rows

The source guard constructs its own normalized physical payload. Actual
inherited combination preserves its Type fields. Descent to each program
child leaves only the annotation field. Row equations establish the roles.
-/
namespace MicroCFTA.SourceSynthesisInheritedRegions
open EqualityNormalize SourceEqualityConstraintRegions SourceSynthesisGuardRegions
open SourceSynthesisGeneralizeSyntax (Guard eqGuard)
open SourceSynthesisFirstOrderConstruction (Expression application ofType)
open SourceEqualityDescend (WellFormed descend)

private theorem eqGuard_cached (classes : Constraints) :
    SourceEqualityGuardReadback.Cached (eqGuard classes).equalities := by
  rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
  exact SourceEqualityGuardReadback.normalize_cached classes

private theorem own_regions (region : Path → Prop) (guard : Guard)
    (stored : SourceEqualityGuardReadback.Cached guard.equalities)
    (endpoints : ∀ path ∈ members ((SourceCompactGuards.sourceEqualities guard).getD []), region path) :
    ∃ own, SourceEqualityPhysicalPayload.own guard = .ok own ∧ WellFormed own ∧ Within region own := by
  have cached := SourceEqualityGuardReadback.source_cached guard stored
  obtain ⟨own, built, wellFormed, _meaning⟩ := SourceEqualityInheritedPayload.read_complete
    (Symbol := Unit) (SourceCompactGuards.sourceEqualities guard) cached
  refine ⟨own, built, wellFormed, ?_⟩
  apply read_preserves region (SourceCompactGuards.sourceEqualities guard) cached ?_ own built
  intro classes same path member
  apply endpoints path
  simpa only [same, Option.getD] using member

/-- Actual application combination derives the annotation regions of both program children. -/
theorem application_inherited (types function argument : Expression)
    (symbol : String) (guard : Guard) (children : List Expression)
    (actual : application types function argument = .node [.mk symbol guard children])
    (inherited : SourceEqualityPrecheck.Constraint) (inheritedWithin : Within applicationRegion inherited) :
    ∃ own combined,
      SourceEqualityPhysicalPayload.own guard = .ok own ∧ WellFormed own ∧ Within applicationRegion own ∧
      SourceEqualityInheritedPayload.combine inherited own = .ok combined ∧
      WellFormed combined ∧ Within applicationRegion combined ∧
      Within annotationRegion (descend combined 2) ∧ Within annotationRegion (descend combined 3) := by
  have stored : SourceEqualityGuardReadback.Cached guard.equalities := by
    cases actual
    exact eqGuard_cached [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]]
  have endpoints := (application_guard_endpoints types function argument symbol guard children actual).2
  obtain ⟨own, built, ownWellFormed, ownWithin⟩ := own_regions applicationRegion guard stored endpoints
  obtain ⟨combined, combinedDone, wellFormed, within, descended⟩ :=
    combine_descend_preserves applicationRegion application_rightClosed inherited own inheritedWithin ownWithin
  refine ⟨own, combined, built, ownWellFormed, ownWithin, combinedDone, wellFormed, within, ?_, ?_⟩
  · simpa only [application_descend_function] using descended 2
  · simpa only [application_descend_argument] using descended 3

/-- Actual filter combination derives the candidate program's annotation region. -/
theorem filter_inherited (candidates goal : Expression)
    (symbol : String) (guard : Guard) (children : List Expression)
    (actual : ofType candidates goal = .node [.mk symbol guard children])
    (inherited : SourceEqualityPrecheck.Constraint) (inheritedWithin : Within filterRegion inherited) :
    ∃ own combined,
      SourceEqualityPhysicalPayload.own guard = .ok own ∧ WellFormed own ∧ Within filterRegion own ∧
      SourceEqualityInheritedPayload.combine inherited own = .ok combined ∧
      WellFormed combined ∧ Within filterRegion combined ∧
      Within annotationRegion (descend combined 1) := by
  have stored : SourceEqualityGuardReadback.Cached guard.equalities := by
    cases actual
    exact eqGuard_cached [[[0], [1, 0]]]
  have endpoints := (filter_guard_endpoints candidates goal symbol guard children actual).2
  obtain ⟨own, built, ownWellFormed, ownWithin⟩ := own_regions filterRegion guard stored endpoints
  obtain ⟨combined, combinedDone, wellFormed, within, descended⟩ :=
    combine_descend_preserves filterRegion filter_rightClosed inherited own inheritedWithin ownWithin
  refine ⟨own, combined, built, ownWellFormed, ownWithin, combinedDone, wellFormed, within, ?_⟩
  simpa only [filter_descend_program] using descended 1

end MicroCFTA.SourceSynthesisInheritedRegions
