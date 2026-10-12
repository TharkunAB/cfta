import MicroCFTA.InternedNestedProvenance
import MicroCFTA.InternedUnionRetention

/-!
# Nested open reconstruction through the source constructor executor

The outer binder retains an inner binder. The inner body has the outer
reference, a recursive constructor, and one external free reference.
Reapplying the scoped body with the complete outer record exercises the
same constructor operations used during source substitution.
-/
namespace MicroCFTA.InternedGateReconstructionExamples
open InternedConstructorTemplates InternedNestedConstruction
open InternedNestedFacts InternedNestedProvenance

/-- Inner scope contains its own reference, the outer reference, and reference 999. -/
def innerBody : Syntax Nat Unit := .union [.var 1, .node [.mk 0 () [.var 0]], .var 2]

/-- The body constructs a binder that depends on its enclosing binder. -/
def outerBody : Syntax Nat Unit := .binder true innerBody

/-- The original source constructor call has one external open reference. -/
def original : Outcome Nat Unit (Value Nat Unit) :=
  build (.binder true outerBody) [.reference (.uninterned 999)] empty

/-- Reapply the outer body to its full recursive record. -/
def firstUnfold : Outcome Nat Unit (Value Nat Unit) :=
  original.bind fun outer state => build outerBody [outer, .reference (.uninterned 999)] state

/-- Reapply the inner body while retaining the original outer record. -/
def secondUnfold : Outcome Nat Unit (Value Nat Unit) :=
  original.bind fun outer state =>
    (build outerBody [outer, .reference (.uninterned 999)] state).bind fun inner later =>
      build innerBody [inner, outer, .reference (.uninterned 999)] later

/-- Observe the head rank separately from cached maximum binder depth. -/
def ranks : Outcome Nat Unit (Value Nat Unit) → Option (Nat × Nat)
  | .done value _ => some (InternedGateRank.headRank value, value.depth)
  | .pending _ _ => none

/-- Source cached depth increases during the first reconstruction while
consecutive root binders decrease. Cached maximum depth is not the gate rank. -/
theorem rank_trace : ranks original = some (2, 2) ∧
    ranks firstUnfold = some (1, 3) ∧ ranks secondUnfold = some (0, 3) := by
  cbv

/-- The original execution derives every record invariant from empty caches. -/
theorem original_verified : Verified empty original InternedProbeProvenance.Available := by
  apply build_verified _ _ empty empty_facts
  intro value member
  have same : value = .reference (.uninterned 999) := by simpa using member
  subst value
  exact ordinary_available empty 999

/-- Its completed record therefore has actual coherent metadata and resident
edge payloads, rather than a separately postulated representation premise. -/
theorem original_fields : Facts original.state := original_verified.facts

end MicroCFTA.InternedGateReconstructionExamples
