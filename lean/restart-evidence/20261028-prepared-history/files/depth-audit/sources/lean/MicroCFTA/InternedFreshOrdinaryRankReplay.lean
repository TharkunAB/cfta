import MicroCFTA.InternedSourceRankStutter
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution

/-!
# The repaired executor avoids the retained rank stutter

The source expressions, captures, and allocation order are the same as in
`InternedSourceRankStutter`. Every constructor and stored unfolding uses the
repaired ordinary probe policy. The first unfolding decreases both candidate
ranks and does not hit the later representative. This finite example does
not establish a rank for arbitrary repaired execution.
-/
namespace MicroCFTA.InternedFreshOrdinaryRankReplay
open InternedConstructorTemplates InternedNestedConstruction
open InternedSourceRankStutter (original preloadFirst preloadSecond representative observed traceRanks)
open InternedGateRank InternedFreeOccurrenceRank

/-- Replay the original source schedule with the repaired constructors and stored executor. -/
def staged : Outcome Nat Unit (Value Nat Unit × Value Nat Unit × Value Nat Unit) :=
  (InternedFreshOrdinaryConstruction.build original [.reference .depth, .reference (.uninterned 2)] empty).bind fun node afterNode =>
  let environment := [node, .reference .depth, .reference (.uninterned 2)]
  (InternedFreshOrdinaryConstruction.build preloadFirst environment afterNode).bind fun _ afterFirst =>
  (InternedFreshOrdinaryConstruction.build preloadSecond environment afterFirst).bind fun _ afterSecond =>
  (InternedFreshOrdinaryConstruction.build representative environment afterSecond).bind fun later afterLater =>
  (InternedFreshOrdinaryStoredSubstitution.unfold node afterLater).bind fun unfolded after =>
    .done (node, later, unfolded) after

/-- Kernel evaluation confirms strict progress and the absence of the old representative hit. -/
theorem actual_progress : observed staged = some ((2, 2, 1), (2, 2, 1), false, true) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in cbv

/-- Both candidate ranks strictly decrease for this actual repaired first unfolding. -/
theorem strictly_decreasing (node later unfolded : Value Nat Unit) (state : State Nat Unit)
    (completed : staged = .done (node, later, unfolded) state) :
    headRank unfolded < headRank node ∧ rank unfolded < rank node := by
  have actual := actual_progress
  simp only [completed, observed, Option.some.injEq, Prod.mk.injEq] at actual
  rw [actual.1.1, actual.1.2.2, actual.2.1.1, actual.2.1.2.2]
  decide

/-- Continue the same repaired stored executor twice more in its actual returned cache. -/
def continued := staged.bind fun (node, _, value) state =>
  (InternedFreshOrdinaryStoredSubstitution.unfold value state).bind fun next afterNext =>
  (InternedFreshOrdinaryStoredSubstitution.unfold next afterNext).bind fun last final =>
    .done [node, value, next, last] final

/-- The repaired trace reaches head rank zero after two unfolds. Cached depth can still increase. -/
theorem finite_continuation : traceRanks continued = some ([2, 1, 0, 0], [2, 1, 0, 0], [2, 3, 3, 3]) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in cbv

end MicroCFTA.InternedFreshOrdinaryRankReplay
