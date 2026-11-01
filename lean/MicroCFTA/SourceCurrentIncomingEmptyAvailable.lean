import MicroCFTA.SourceCurrentIncomingReadFrame

/-! The empty replacement has no residency requirement. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentIncomingEmptyAvailable
open InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

variable {width : Nat}

/-- The literal empty replacement is available in the reached heap. -/
theorem empty_available (caller : SourceCurrentAllocatedPartialState.State width) :
    Available caller.checked.native.machine.heap (.empty : Value Symbol Constraint) := by
  constructor
  · simp [InternedFreshProbeKeys.Resident, InternedRecordCoherence.entryOf]
  · simp [InternedFreshProbeKeys.IssuedReferences, Value.free]
  · intro child member
    simp [children] at member

end MicroCFTA.SourceCurrentIncomingEmptyAvailable
