import MicroCFTA.SourceEqualityProjectionAPI
import MicroCFTA.SourceClosedSelfHeadRepair

/-!
# Kernel checks for general source projection

The retained raw self binder distinguishes root identity, head normalization,
closed forest union, and the two exhausted proof bounds.
-/
namespace MicroCFTA.SourceEqualityProjectionExamples
open InternedConstructorTemplates InternedNestedConstruction SourceEqualityProjectionWorker

/-- Bare references keep source root priority and report unresolved proper paths. -/
theorem reference_priority (state : State Nat Unit) :
    project 1 0 [] (.reference .depth) state = .done (.reference .depth) state ∧
    project 1 0 [0] (.reference .depth) state = .unresolved .depth state := ⟨rfl, rfl⟩

/-- Missing signed forest positions do not inspect the payload or use a worker bound. -/
theorem missing_positions (state : State Nat Unit) :
    forest 0 0 [-1] [.reference .depth] state = .done .empty state ∧
    forest 0 0 [9] [.reference .depth] state = .done .empty state := ⟨rfl, rfl⟩

/-- Observe the actual constructed closed self binder and exact returned caches. -/
def SelfResults : Outcome Nat Unit (Value Nat Unit) → Prop
  | .pending _ _ => False
  | .done value state =>
      project 1 0 [] value state = .done value state ∧
      project 2 2 [0] value state = .done .empty state ∧
      project 1 2 [0] value state = .exhausted .worker state ∧
      project 2 1 [0] value state = .exhausted .head state ∧
      forest 0 2 [] [value] state = .done .empty state ∧
      forest 0 1 [] [value] state = .exhausted .head state

/-- Closed forest union reads recursive rows even for a singleton operand. -/
theorem raw_self : SelfResults
    (InternedFreshOrdinaryConstruction.build SourceClosedSelfRequireBoundary.expression [] empty) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in
    cbv

end MicroCFTA.SourceEqualityProjectionExamples
