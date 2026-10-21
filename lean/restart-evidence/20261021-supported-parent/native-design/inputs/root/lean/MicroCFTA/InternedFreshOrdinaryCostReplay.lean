import MicroCFTA.InternedNestedProbeCostBoundary
import MicroCFTA.InternedFreshOrdinaryConstruction

/-!
# The repaired replay of the retained probe-cost boundary

The source expression and captured sentinels are unchanged. The repaired
ordinary name avoids the earlier masked alias. Both probes now retain the
external body occurrence costs. This finite replay does not establish the
cost relation for arbitrary nested repaired callbacks.
-/
namespace MicroCFTA.InternedFreshOrdinaryCostReplay
open InternedConstructorTemplates InternedNestedConstruction InternedFreeOccurrenceRank
open InternedNestedProbeCostBoundary (body observations ExactProbeCoverage)
open InternedBinderProtocol (Reference)

/-- Replay the exact original nested source expression with repaired ordinary probes. -/
def result : Outcome Nat Unit (Value Nat Unit) :=
  InternedFreshOrdinaryConstruction.build (.binder false body)
    [.reference .depth, .reference (.uninterned 0)] empty

/-- Kernel evaluation confirms the external body costs in both actual repaired probes. -/
theorem actual_costs : observations result =
    some (10, [(.depth, 1), (.uninterned 0, 1), (.interned 10, 1)],
      [(.depth, 1), (.uninterned 0, 1)],
      [(.depth, 1), (.uninterned 0, 1), (.uninterned 1, 1)]) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in cbv

/-- The earlier exact-cost counterexample does not refute coverage for this repaired replay. -/
theorem exact_probe_coverage : ExactProbeCoverage result := by
  intro identity actual depth ordinary completed name count different member
  have fields := completed.symm.trans actual_costs
  simp only [Option.some.injEq, Prod.mk.injEq] at fields
  rcases fields with ⟨rfl, rfl, rfl, rfl⟩
  simp_all [List.mem_cons, Prod.mk.injEq]

end MicroCFTA.InternedFreshOrdinaryCostReplay
