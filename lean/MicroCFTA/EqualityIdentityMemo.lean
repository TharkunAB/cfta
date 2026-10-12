import MicroCFTA.Cache
import MicroCFTA.EqualityNormalize

/-!
# Interned equality constraint keys

The new source cache interns the ordered list of equality classes. The
identity supplies equality and memo keys. Ordering still compares the class
lists. This adapter uses the existing cache invariant and normalization
semantics. Trie/list coherence, machine identity bounds, and source cache
storage remain separate representation obligations.
-/
namespace MicroCFTA.EqualityIdentityMemo
open Language EqualityNormalize

/-- The noncontradictory source constructor stores its identity and class list. -/
abbrev Entry := Cache.Interned Constraints

/-- The value was read from the current shared constraint cache. -/
def Stored (state : Cache.State Constraints) (entry : Entry) : Prop :=
  state.table entry.key = some entry

/-- Source equality compares identities without traversing classes. -/
def equal (left right : Entry) : Bool := left.identity == right.identity

/-- Identity equality is exactly equality of ordered class keys in a valid cache. -/
theorem equal_exact (state : Cache.State Constraints) (valid : Cache.Valid state)
    (left right : Entry) (leftStored : Stored state left) (rightStored : Stored state right) :
    equal left right = true ↔ left.key = right.key := by
  simp only [equal, beq_iff_eq]
  exact Cache.identity_eq_iff_key_eq state valid leftStored rightStored

/-- The source comparator has an identity fast path and a structural fallback. -/
def compareWith (compareClasses : Constraints → Constraints → Ordering) (left right : Entry) : Ordering :=
  if equal left right then .eq else compareClasses left.key right.key

/-- Allocation order cannot change structural class ordering. No canonical
class-list premise is required: the key is the ordered list itself. -/
theorem compare_exact (compareClasses : Constraints → Constraints → Ordering)
    (reflexive : ∀ classes, compareClasses classes classes = .eq)
    (state : Cache.State Constraints) (valid : Cache.Valid state) (left right : Entry)
    (leftStored : Stored state left) (rightStored : Stored state right) :
    compareWith compareClasses left right = compareClasses left.key right.key := by
  unfold compareWith
  split
  · next same => rw [(equal_exact state valid left right leftStored rightStored).mp same, reflexive]
  · rfl

/-- Decode an allocated identity through the existing reservation registry. -/
def classesAt (state : Cache.State Constraints) (identity : Nat) : Constraints :=
  (state.issued identity).getD []

/-- Every stored identity decodes to the exact key that the source interned. -/
theorem classesAt_exact (state : Cache.State Constraints) (valid : Cache.Valid state)
    (entry : Entry) (stored : Stored state entry) : classesAt state entry.identity = entry.key := by
  simp [classesAt, (valid.2 entry.key entry stored).2]

/-- The descent memo key is the constraint identity and selected child index. -/
def descendCompute (state : Cache.State Constraints) (key : Nat × Nat) : Constraints :=
  eqConstraintsDescend key.2 (classesAt state key.1)

/-- Read the first completed result, or store the pure descent on a miss. -/
def descend (state : Cache.State Constraints) (table : Cache.Table (Nat × Nat) Constraints)
    (entry : Entry) (index : Nat) : Constraints :=
  let key := (entry.identity, index)
  (Cache.keepFirst table key (descendCompute state key) key).getD (descendCompute state key)

/-- Memoization on identities computes the same descendant constraints. -/
theorem descend_exact (state : Cache.State Constraints) (valid : Cache.Valid state)
    (table : Cache.Table (Nat × Nat) Constraints) (memo : Cache.MemoValid (descendCompute state) table)
    (entry : Entry) (stored : Stored state entry) (index : Nat) :
    descend state table entry index = eqConstraintsDescend index entry.key := by
  rw [descend, Cache.memo_correct _ memo]
  simp [descendCompute, classesAt_exact state valid entry stored]

/-- The identity-keyed memo retains all and only the surviving same-child
equality pairs. Singleton classes still impose no existence requirement. -/
theorem descend_semantics (state : Cache.State Constraints) (valid : Cache.Valid state)
    (table : Cache.Table (Nat × Nat) Constraints) (memo : Cache.MemoValid (descendCompute state) table)
    (entry : Entry) (stored : Stored state entry) (index : Nat) (term : Term Symbol) :
    Satisfies term (descend state table entry index) ↔
      ∀ paths ∈ entry.key, ∀ left, index :: left ∈ paths →
        ∀ right, index :: right ∈ paths → left ≠ right → PathsEqual term left right := by
  rw [descend_exact state valid table memo entry stored index]
  exact eqConstraintsDescend_exact term index entry.key

/-- The binary combination memo uses both identities in argument order. -/
def combineCompute (state : Cache.State Constraints) (fuel : Nat) (key : Nat × Nat) : RunResult :=
  mkEqConstraints fuel (classesAt state key.1 ++ classesAt state key.2)

/-- Read or store one completed pure combination worker result. -/
def combine (state : Cache.State Constraints) (fuel : Nat)
    (table : Cache.Table (Nat × Nat) RunResult) (left right : Entry) : RunResult :=
  let key := (left.identity, right.identity)
  (Cache.keepFirst table key (combineCompute state fuel key) key).getD (combineCompute state fuel key)

/-- Identity-based combination equals normalization of both structural inputs. -/
theorem combine_exact (state : Cache.State Constraints) (valid : Cache.Valid state)
    (fuel : Nat) (table : Cache.Table (Nat × Nat) RunResult)
    (memo : Cache.MemoValid (combineCompute state fuel) table) (left right : Entry)
    (leftStored : Stored state left) (rightStored : Stored state right) :
    combine state fuel table left right = mkEqConstraints fuel (left.key ++ right.key) := by
  rw [combine, Cache.memo_correct _ memo]
  simp [combineCompute, classesAt_exact state valid left leftStored,
    classesAt_exact state valid right rightStored]

/-- Every completed memoized combination is exactly logical conjunction.
The fuel premise concerns normalization, not identity equality. -/
theorem combine_semantics (state : Cache.State Constraints) (valid : Cache.Valid state)
    (fuel : Nat) (table : Cache.Table (Nat × Nat) RunResult)
    (memo : Cache.MemoValid (combineCompute state fuel) table) (left right : Entry)
    (leftStored : Stored state left) (rightStored : Stored state right) (term : Term Symbol)
    (finished : combine state fuel table left right ≠ .timeout) :
    RunSat term (combine state fuel table left right) ↔
      Satisfies term left.key ∧ Satisfies term right.key := by
  rw [combine_exact state valid fuel table memo left right leftStored rightStored] at finished ⊢
  rw [mkEqConstraints_correct term fuel _ finished]
  simp [Satisfies, or_imp, forall_and]

end MicroCFTA.EqualityIdentityMemo
