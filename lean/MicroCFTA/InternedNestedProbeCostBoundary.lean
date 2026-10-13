import MicroCFTA.InternedNestedConstructionExamples
import MicroCFTA.InternedFreeOccurrenceRank

/-!
# Exact probe-cost membership does not extend to every nested callback

The callback captures the two source sentinels. A discarded edge first
constructs an unused smart Mu. The live branch then constructs a used
inner Mu. Canonical probe hits remove that inner wrapper in both probes,
while the fresh body retains it. This is a boundary for an auxiliary cost
lemma. It is not a gate-termination counterexample.
-/
namespace MicroCFTA.InternedNestedProbeCostBoundary
open InternedConstructorTemplates InternedNestedConstruction InternedFreeOccurrenceRank
open InternedBinderProtocol (Reference)

/-- Both captured inputs are present before the live branch constructs its inner local binder. -/
def body : Syntax Nat Unit := .union [
  .node [.mk 2 () [.binder true (.node [.mk 0 () [.var 2], .mk 0 () [.var 3]]), .empty]],
  .node [.mk 1 () [.binder true (.node [.mk 0 () [.var 0], .mk 0 () [.var 1], .mk 0 () [.var 2], .mk 0 () [.var 3]])]]]

/-- The supplied capture records are available source sentinels. -/
def result : Outcome Nat Unit (Value Nat Unit) :=
  build (.binder false body) [.reference .depth, .reference (.uninterned 0)] empty

/-- Inspect only a completed actual raw Mu and its complete stored body and probes. -/
def observations : Outcome Symbol Guard (Value Symbol Guard) →
    Option (Nat × List (Reference × Nat) × List (Reference × Nat) × List (Reference × Nat))
  | .done (.mu entry actual depth ordinary) _ => some (entry.identity, costs actual, costs depth, costs ordinary)
  | _ => none

/-- Kernel evaluation exhibits the extra actual-body binder cost on both fixed captures. -/
theorem actual_costs : observations result =
    some (3, [(.depth, 1), (.uninterned 0, 1), (.interned 3, 1)],
      [(.depth, 0), (.uninterned 0, 0)], [(.depth, 0), (.uninterned 0, 0)]) := by
  set_option cbv.maxSteps 5000000 in cbv

/-- This proposed generalization requires every external body cost in at least one probe. -/
def ExactProbeCoverage (outcome : Outcome Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ identity actual depth ordinary, observations outcome = some (identity, actual, depth, ordinary) →
    ∀ name count, name ≠ .interned identity → (name, count) ∈ actual →
      (name, count) ∈ depth ∨ (name, count) ∈ ordinary

/-- Actual nested smart cleanup refutes the unrestricted exact-cost predecessor claim. -/
theorem not_exact_probe_coverage : ¬ ExactProbeCoverage result := by
  intro covered
  have impossible := covered 3 _ _ _ actual_costs .depth 1 (by simp) (by simp)
  simp at impossible

/-- The source expression uses only its supplied local and two fixed captures. -/
theorem expression_scoped : Scoped 2 (.binder false body) := by
  simp [body, Scoped, ManyScoped, EdgesScoped]

end MicroCFTA.InternedNestedProbeCostBoundary
