import MicroCFTA.SourceSynthesisOriginalCallerInitialization
import MicroCFTA.SourceCurrentAllocatedTupleConjunctionWorkerActual

/-!
# Tuple calls from original signed source requests

An accepted source request constructs its own build and initial caller.
That caller derives its actual tuple call, reads and stable completion.
No initial caller invariant, completed body or fuel supplier is an input.
This result does not switch the selected driver or establish native demand.
-/
namespace MicroCFTA.SourceSynthesisOriginalTupleCall
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceEqualityConstraintOrigins (guards)
open SourceCurrentAllocatedPartialInitialization (caller inventory globals)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Call" => SourceCurrentConjunctionDemandWorklistExecution.Call
local notation "CallReads" => SourceCurrentConjunctionDemandWorklistMemos.CallReads
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Original source success derives a complete conservative tuple call and its exact returned caller. -/
theorem request (lib : Library) (query : Query) (signed : Int) (width budget : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    match firstOrderRaw lib query signed with
    | .error _ => True
    | .ok expression =>
        ∃ fields cache value heap,
          ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
          ∃ answer after saved final p h,
          SourceEqualityOriginalAllocationPreparation.Receipt (guards (ordinarySymbols expression))
            Cache.emptyState fields cache ∧
          Context formulas solver (inventory (ordinarySymbols expression) value heap built)
            (caller width cache heap) globals ∧
          SourceSynthesisProgramBuildRolesGeneric.ProgramValue SourceSynthesisLabelProgramBuildRoles.literal value ∧
          ∃ actual : Call budget (caller width cache heap).fourth value
              (physical (caller width cache heap).checked) answer after saved,
            CallReads actual globals final ∧
            (∀ P H, p ≤ P → h ≤ H →
              SourceCurrentAllocatedTupleConjunctionWorker.call P H budget value (caller width cache heap).checked
                (caller width cache heap).fourth =
                .done answer (advancePhysical (caller width cache heap).checked after) saved) ∧
            Post formulas solver (inventory (ordinarySymbols expression) value heap built) (caller width cache heap)
              (SourceCurrentAllocatedPartialState.advance (caller width cache heap)
                (advancePhysical (caller width cache heap).checked after) saved (caller width cache heap).merge) final ∧
            SourceCurrentEmptinessMemo.AnswerSound formulas solver value answer ∧ Available after.heap value ∧
            Extends globals.unfolding final.unfolding ∧ final.query = globals.query := by
  cases returned : firstOrderRaw lib query signed with
  | error => trivial
  | ok expression =>
      obtain ⟨fields, cache, value, heap, built, prepared, initial, _facts, available,
          roles, _growth, _issued, _inherited⟩ :=
        SourceSynthesisOriginalCallerInitialization.accepted lib query signed expression returned width
          Cache.emptyState Cache.empty_valid formulas solver
      obtain ⟨answer, after, saved, final, actual, reads, post⟩ :=
        SourceCurrentAllocatedTupleConjunctionCaller.finite formulas solver budget initial available
      obtain ⟨p, h, stable⟩ := SourceCurrentConjunctionDemandWorklistExecution.call_complete actual
      exact ⟨fields, cache, value, heap, built, answer, after, saved, final, p, h,
        prepared, initial, roles, actual, reads,
        (fun P H enoughP enoughH => SourceCurrentAllocatedTupleConjunctionWorker.call_lift
          (stable P H enoughP enoughH)), post⟩

end MicroCFTA.SourceSynthesisOriginalTupleCall
