import MicroCFTA.InternedStoredSubstitution

/-!
# Actual nested source unfolding can increase the head rank

A raw nested binder retains an unused wrapper around the outer reference.
Stored substitution uses smart binders and removes that wrapper. Two
previously distinct union members then become the same canonical record.
Singleton normalization exposes its leading binders. This rules out the
unrestricted leading-binder count as a strict unfolding measure.
The enclosing callback violates the documented substitution-parametricity
precondition because substitution removes its raw unused wrapper. This is
not a counterexample for callbacks that satisfy that precondition.
-/
namespace MicroCFTA.InternedGateHeadGrowth
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedStoredSubstitution InternedGateReconstructionExamples

/-- Both inner binders use their references below an ordinary source constructor. -/
def direct : Syntax Nat Unit :=
  .binder true (.binder true (.node [.mk 0 () [.var 1, .var 0, .var 2, .var 3]]))

/-- The raw wrapper distinguishes the second union member before substitution. -/
def wrapped : Syntax Nat Unit :=
  .binder true (.binder true (.node [.mk 0 () [.var 1, .var 0, .binder false (.var 3), .var 3]]))

/-- The outer binder is open because both branches retain an external free reference. -/
def program : Syntax Nat Unit := .binder true (.union [direct, wrapped])

def environment : List (Value Nat Unit) := [.reference (.uninterned 999)]
def original : Outcome Nat Unit (Value Nat Unit) := build program environment empty

def firstUnfold : Outcome Nat Unit (Value Nat Unit) := original.bind unfold

/-- Each step executes actual stored-body preparation and both source binder probes.
The first unfolding increases head rank from one to two. -/
theorem rank_trace : ranks original = some (1, 4) ∧
    ranks firstUnfold = some (2, 6) := by
  set_option cbv.maxSteps 1000000 in cbv

/-- Each queried record retains an unresolved free reference. -/
def openResult : Outcome Nat Unit (Value Nat Unit) → Bool
  | .done value _ => !value.free.isEmpty
  | .pending .. => false

theorem open_trace : openResult original = true ∧ openResult firstUnfold = true := by
  set_option cbv.maxSteps 1000000 in cbv

/-- The counterexample starts with complete source reference provenance. -/
theorem inputs_available : Values (empty (Symbol := Nat) (Guard := Unit)) environment := by
  intro value member
  have same : value = .reference (.uninterned 999) := by simpa [environment] using member
  subst value
  exact ordinary_available empty 999

/-- Every original cache field and returned record comes from the actual source constructor. -/
theorem checked : Verified empty original Available :=
  build_verified program environment empty empty_facts inputs_available

end MicroCFTA.InternedGateHeadGrowth
