import MicroCFTA.SymbolicSignedPaths

/-!
# Canonical operand order for memoized intersections

The source swaps an intersection pair when the right identity is smaller.
After that swap the worker enters the ordinary branch. Canonical ordering
gives identical keys and results in both call directions. Commutativity of
the branch body is not assumed.
-/
namespace MicroCFTA.SymbolicCanonicalOrder

/-- The source numeric identity order, independent of the intersection body. -/
def orderedPair (left right : Nat) : Nat × Nat :=
  if right < left then (right, left) else (left, right)

/-- The stored pair is the minimum and maximum of the two identities. -/
theorem orderedPair_minmax (left right : Nat) : orderedPair left right = (min left right, max left right) := by
  by_cases reverse : right < left
  · simp [orderedPair, reverse, Nat.min_eq_right (by omega : right ≤ left), Nat.max_eq_left (by omega : right ≤ left)]
  · simp [orderedPair, reverse, Nat.min_eq_left (by omega : left ≤ right), Nat.max_eq_right (by omega : left ≤ right)]

/-- Reversing operands retains the same complete canonical key. -/
theorem orderedPair_symmetric (left right : Nat) : orderedPair left right = orderedPair right left := by
  simp [orderedPair_minmax, Nat.min_comm, Nat.max_comm]

/-- The bounded operational port makes the same recursive swap as the source. -/
def orderWorker (body : Nat → Nat → Value) : Nat → Nat → Nat → Option Value
  | 0, _, _ => none
  | fuel + 1, left, right =>
      if right < left then orderWorker body fuel right left else some (body left right)

/-- At most one swap is needed before the source reaches the ordinary body. -/
theorem orderWorker_exact (body : Nat → Nat → Value) (fuel left right : Nat) :
    orderWorker body (fuel + 2) left right = some (body (orderedPair left right).1 (orderedPair left right).2) := by
  by_cases reverse : right < left
  · simp [orderWorker, orderedPair, reverse, show ¬left < right by omega]
  · simp [orderWorker, orderedPair, reverse]

/-- The actual swap worker has equal results in both directions without a symmetric-body premise. -/
theorem orderWorker_symmetric (body : Nat → Nat → Value) (fuel left right : Nat) :
    orderWorker body (fuel + 2) left right = orderWorker body (fuel + 2) right left := by
  rw [orderWorker_exact, orderWorker_exact, orderedPair_symmetric]

/-- First-writer memo readback preserves the canonical pair's deterministic result. -/
theorem memo_canonical (body : Nat × Nat → Value) (table : Cache.Table (Nat × Nat) Value)
    (valid : Cache.MemoValid body table) (left right : Nat) :
    (Cache.keepFirst table (orderedPair left right) (body (orderedPair left right)) (orderedPair left right)).getD
        (body (orderedPair left right)) =
      (Cache.keepFirst table (orderedPair right left) (body (orderedPair right left)) (orderedPair right left)).getD
        (body (orderedPair right left)) := by
  rw [Cache.memo_correct body valid, Cache.memo_correct body valid, orderedPair_symmetric]

/-- Canonical identity equality in a valid intern table also identifies the exact payload key. -/
theorem stored_payload_same (state : Cache.State Key) (valid : Cache.Valid state)
    (leftKey rightKey : Key) (left right : Cache.Interned Key)
    (leftStored : state.table leftKey = some left) (rightStored : state.table rightKey = some right)
    (identity : left.identity = right.identity) : left = right := by
  have same := (Cache.identity_eq_iff_key_eq state valid leftStored rightStored).mp identity
  subst rightKey
  exact Option.some.inj (leftStored.symm.trans rightStored)

/-- Swapping compiled guard conjunction operands retains their exact numeric interpretation. -/
theorem conjoin_score_symmetric (test : Atom → Bool) (left right : ConstraintIndicators.Series Atom) :
    ConstraintIndicators.score test (ConstraintIndicators.conjoin left right) =
      ConstraintIndicators.score test (ConstraintIndicators.conjoin right left) := by
  rw [ConstraintIndicators.score_conjoin, ConstraintIndicators.score_conjoin, Int.mul_comm]

end MicroCFTA.SymbolicCanonicalOrder
