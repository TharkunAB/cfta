import MicroCFTA.SourceSynthesisOriginalGuardsCached
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.SourceCurrentAllocatedPartialInitialization

/-!
# Initial callers from original signed source requests

Source success derives its actual Label build and normalized guards.
The serial allocator supplies the history used by caller initialization.
No completed build, loaded-field predicate or final caller is an input.
Source errors remain explicit. Native cache initialization is separate.
-/
namespace MicroCFTA.SourceSynthesisOriginalCallerInitialization
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceEqualityConstraintOrigins (guards)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Accepted source construction derives preparation, build, roles and the full initial Context. -/
theorem accepted (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : firstOrderRaw lib query signed = .ok expression)
    (width : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt (guards (ordinarySymbols expression)) initial fields cache ∧
      Context formulas solver (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) value heap built)
        (SourceCurrentAllocatedPartialInitialization.caller width cache heap) SourceCurrentAllocatedPartialInitialization.globals ∧
      Facts heap ∧ Available heap value ∧
      SourceSynthesisProgramBuildRolesGeneric.ProgramValue SourceSynthesisLabelProgramBuildRoles.literal value ∧
      Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued ∧
      ∃ identity, SourceCurrentAllocatedPartialInitialization.emptyValue cache = .live identity [] ∧
        SourceEqualityConstraintAllocation.Ready (SourceCurrentAllocatedPartialInitialization.caller width cache heap).checked.operations.constraints
          (.live identity []) ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  obtain ⟨fields, cache, prepared⟩ := SourceEqualityOriginalAllocationPreparation.prepare_complete
    (guards (ordinarySymbols expression)) initial valid
    (SourceSynthesisOriginalGuardsCached.firstOrderRaw_guards_cached lib query signed expression returned)
  obtain ⟨value, heap, observed, facts, available, roles, growth, issued⟩ :=
    SourceSynthesisLabelProgramBuildRoles.firstOrderRaw_build_roles lib query signed expression returned
  have built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap :=
    Eq.mp (by congr <;> exact Subsingleton.elim _ _) observed
  have initialized := SourceCurrentAllocatedPartialInitialization.constructed width prepared.history valid (ordinarySymbols expression)
    (fun _ member => member) value heap built formulas solver
  obtain ⟨identity, emptySame, emptyReady, _available, closed, original⟩ := initialized.2
  exact ⟨fields, cache, value, heap, built, prepared, initialized.1, facts, available,
    roles, growth, issued, identity, emptySame, emptyReady, closed, original⟩

/-- An original signed request retains source errors and constructs its own cold caller on success. -/
theorem request (lib : Library) (query : Query) (signed : Int) (width : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    match firstOrderRaw lib query signed with
    | .error _ => True
    | .ok expression =>
        ∃ fields cache value heap,
          ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
          SourceEqualityOriginalAllocationPreparation.Receipt (guards (ordinarySymbols expression))
            Cache.emptyState fields cache ∧
          Context formulas solver (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) value heap built)
            (SourceCurrentAllocatedPartialInitialization.caller width cache heap) SourceCurrentAllocatedPartialInitialization.globals ∧
          Facts heap ∧ Available heap value ∧
          SourceSynthesisProgramBuildRolesGeneric.ProgramValue SourceSynthesisLabelProgramBuildRoles.literal value ∧
          Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued ∧
          ∃ identity, SourceCurrentAllocatedPartialInitialization.emptyValue cache = .live identity [] ∧
            SourceEqualityConstraintAllocation.Ready (SourceCurrentAllocatedPartialInitialization.caller width cache heap).checked.operations.constraints
              (.live identity []) ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  cases returned : firstOrderRaw lib query signed with
  | error => trivial
  | ok expression => exact accepted lib query signed expression returned width Cache.emptyState Cache.empty_valid formulas solver

end MicroCFTA.SourceSynthesisOriginalCallerInitialization
