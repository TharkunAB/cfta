import MicroCFTA.SourceCurrentConstrainedCapEditSupport
import MicroCFTA.SourceCurrentConstrainedCapMaskCharacterization
import MicroCFTA.SourceCurrentClassFoldDomains

/-!
# Original masks through successive class forests

Ordered all-path relations retain each later class mask at the actual tail
return. Closed available captured values supply every signed path domain.
Final literal empty propagation retains the same relation and forest arity.
These are local composition laws. They do not assert class completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapForestSupport
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityProjectionGraph (select select_member)
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceCurrentConstrainedCapPaths (Supported ForestSupported)
open SourceCurrentConstrainedCapRequiredSupport (Preserves forest_supported)
variable {Symbol Guard : Type}

/-- Two ordered actual-return relations retain every original signed position. -/
theorem trans {valid : Guard → Prop} {values middle results : List (Value Symbol Guard)}
    (first : All₂ (Preserves valid) values middle) (last : All₂ (Preserves valid) middle results) :
    All₂ (Preserves valid) values results := by
  induction first generalizing results with
  | nil => cases last; exact .nil
  | cons first rest ih =>
      cases last with
      | cons second tail => exact .cons (SourceCurrentConstrainedCapEditSupport.preserves_trans first second) (ih tail)

/-- A later record uses its original masks at the actual earlier tail return. -/
theorem record_masks {valid : Guard → Prop} {values results : List (Value Symbol Guard)}
    (related : All₂ (Preserves valid) values results) (record : SourceEqualityClassOrder.Record)
    (supported : ∀ path ∈ record.paths, ForestSupported valid (path.map Int.ofNat) values) :
    ∀ path ∈ record.paths, ForestSupported valid (path.map Int.ofNat) results :=
  fun path member => forest_supported valid related _ (supported path member)

/-- Each literal other-path operand uses a mask from the same captured record. -/
theorem operand_masks {valid : Guard → Prop} (record : SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard))
    (supported : ∀ path ∈ record.paths, ForestSupported valid (path.map Int.ofNat) values)
    (path : EqualityNormalize.Path) :
    ∀ operand ∈ SourceEqualityClassTarget.operandPaths record.paths path, ForestSupported valid operand values := by
  intro operand member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact supported original (List.mem_filter.mp present).1

section Closed
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Closed available captured values supply every signed selected path domain. -/
theorem closed_domains (values : List (Value Symbol Guard)) (heap : State Symbol Guard)
    (ready : SourceEqualityRequiredSemanticCache.SemanticReady heap) (available : Values heap values) (closed : ClosedValues values)
    (path : List Int) : ForestClosed path values := by
  cases path with
  | nil => exact closed
  | cons index path =>
      intro value selected
      have member := select_member selected
      exact SourceCurrentRequiredEndpoints.closed_path path value heap ready (available value member) (closed value member)

end Closed

/-- Actual physical edit transport retains captured whole-value closedness. -/
theorem closed_transport {values results : List (Value Symbol Guard)}
    (related : All₂ SourceCurrentEditDomains.Transport values results) (closed : ClosedValues values) :
    ClosedValues results :=
  SourceCurrentEditDomains.transport_forest related [] closed

/-- Final source empty propagation retains every original supported path in order. -/
theorem propagate (valid : Guard → Prop) (values : List (Value Symbol Guard)) :
    All₂ (Preserves valid) values (EqualityLeafProjectionRuntimeEmpty.propagate values) := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · rename_i condition
    clear condition
    unfold EqualityLeafProjectionRuntimeEmpty.erase
    induction values with
    | nil => exact .nil
    | cons value values ih =>
        exact .cons (SourceCurrentConstrainedCapEditSupport.preserves_of_annotated valid value .empty .empty) ih
  · exact SourceCurrentConstrainedCapEditSupport.forest_refl valid values

end MicroCFTA.SourceCurrentConstrainedCapForestSupport
