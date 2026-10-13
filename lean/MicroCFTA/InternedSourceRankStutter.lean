import MicroCFTA.InternedStoredSubstitution
import MicroCFTA.InternedFreeOccurrenceRank

/-!
# Actual canonical readback can leave both candidate unfolding ranks unchanged

The source first constructs an open raw Mu. Two unused smart binders then
populate probe records for another raw Mu. The actual stored-body unfolding
hits that later canonical representative. Both its head rank and its
minimum free-reference cost equal those of the original Mu.

The callback captures the depth sentinel and ordinary sentinel at level
two. All constructors use scoped source syntax. The finite continuation
reaches an ordinary node. This is a counterexample to the strict candidate
ranks, not a source divergence witness.
-/
namespace MicroCFTA.InternedSourceRankStutter
open InternedConstructorTemplates InternedNestedConstruction InternedFreeOccurrenceRank
open InternedBinderProtocol (Reference)
open InternedGateRank

/-- The original raw body has one inner raw binder and two fixed sentinel captures. -/
def original : Syntax Nat Unit := .binder false (.binder false (.node [
  .mk 0 () [.var 2], .mk 0 () [.var 3], .mk 1 () [.var 0], .mk 2 () [.var 1]]))

/-- The first unused binder returns the complete node for the depth-side canonical probe. -/
def preloadFirst : Syntax Nat Unit := .binder true (.node [
  .mk 0 () [.var 2], .mk 0 () [.var 3], .mk 1 () [.var 2], .mk 2 () [.var 1]])

/-- The second unused binder returns the corresponding ordinary-side canonical probe. -/
def preloadSecond : Syntax Nat Unit := .binder true (.node [
  .mk 0 () [.var 2], .mk 0 () [.var 3], .mk 1 () [.var 3], .mk 2 () [.var 1]])

/-- This later representative retains a used inner binder in its actual fresh body. -/
def representative : Syntax Nat Unit := .binder false (.binder true (.node [
  .mk 0 () [.var 0], .mk 0 () [.var 3], .mk 0 () [.var 4], .mk 1 () [.var 1], .mk 2 () [.var 2]]))

/-- Execute the actual source allocations before unfolding the original stored record. -/
def staged : Outcome Nat Unit (Value Nat Unit × Value Nat Unit × Value Nat Unit) :=
  (build original [.reference .depth, .reference (.uninterned 2)] empty).bind fun node afterNode =>
  let environment := [node, .reference .depth, .reference (.uninterned 2)]
  (build preloadFirst environment afterNode).bind fun _ afterFirst =>
  (build preloadSecond environment afterFirst).bind fun _ afterSecond =>
  (build representative environment afterSecond).bind fun later afterLater =>
  (InternedStoredSubstitution.unfold node afterLater).bind fun unfolded after =>
    .done (node, later, unfolded) after

/-- Inspect both actual rank functions, canonical identity equality, and openness. -/
def observed : Outcome Nat Unit (Value Nat Unit × Value Nat Unit × Value Nat Unit) →
    Option ((Nat × Nat × Nat) × (Nat × Nat × Nat) × Bool × Bool)
  | .pending .. => none
  | .done (node, later, unfolded) _ => some ((headRank node, headRank later, headRank unfolded),
      (rank node, rank later, rank unfolded), unfolded.referenceOf == later.referenceOf,
      !node.free.isEmpty && !unfolded.free.isEmpty)

/-- Kernel evaluation confirms the actual cache hit and equal ranks on two open records. -/
theorem actual_stutter : observed staged = some ((2, 2, 2), (2, 2, 2), true, true) := by
  set_option maxRecDepth 10000 in
  set_option cbv.maxSteps 10000000 in cbv

/-- Neither candidate is a strict rank for this actual completed source unfolding. -/
theorem not_strictly_decreasing (node later unfolded : Value Nat Unit) (state : State Nat Unit)
    (completed : staged = .done (node, later, unfolded) state) :
    ¬ headRank unfolded < headRank node ∧ ¬ rank unfolded < rank node := by
  have actual := actual_stutter
  simp only [completed, observed, Option.some.injEq, Prod.mk.injEq] at actual
  rw [actual.1.1, actual.1.2.2, actual.2.1.1, actual.2.1.2.2]
  simp

/-- Continue the same exact stored-body executor twice more. -/
def continued := staged.bind fun (node, _, value) state =>
  (InternedStoredSubstitution.unfold value state).bind fun next afterNext =>
  (InternedStoredSubstitution.unfold next afterNext).bind fun last final =>
    .done [node, value, next, last] final

/-- Read all three numeric observations from the completed source trace. -/
def traceRanks : Outcome Nat Unit (List (Value Nat Unit)) → Option (List Nat × List Nat × List Nat)
  | .pending .. => none
  | .done values _ => some (values.map headRank, values.map rank, values.map Value.depth)

/-- The checked continuation reaches head rank zero after the first stuttering step. -/
theorem finite_continuation : traceRanks continued = some ([2, 2, 1, 0], [2, 2, 1, 0], [2, 4, 5, 5]) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in cbv

/-- Every original source variable lies within its actual local and captured scope. -/
theorem source_scoped : Scoped 2 original ∧ Scoped 3 preloadFirst ∧ Scoped 3 preloadSecond ∧ Scoped 3 representative := by
  simp [original, preloadFirst, preloadSecond, representative, Scoped, EdgesScoped, ManyScoped]

end MicroCFTA.InternedSourceRankStutter
