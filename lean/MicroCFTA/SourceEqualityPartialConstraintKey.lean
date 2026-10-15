import MicroCFTA.SourceEqualityPrecheck
import MicroCFTA.Cache

/-!
# Physical equality-constraint identities for partial-reduction requests

The interner compares the ordered list of class tries. It does not read the
class path-set field. Trie child lists represent IntMap ascending entries.
The source representation boundary requires ascending valid tries.
-/
namespace MicroCFTA.SourceEqualityPartialConstraintKey
open EqualityTrie

mutual
  /-- Decide equality of complete physical trie representations. -/
  def trieDecEq : (left right : Trie) → Decidable (left = right)
    | .empty, .empty => isTrue rfl
    | .terminal, .terminal => isTrue rfl
    | .branch left, .branch right =>
        match childrenDecEq left right with
        | isTrue same => isTrue (congrArg Trie.branch same)
        | isFalse different => isFalse (fun same => different (Trie.branch.inj same))
    | .empty, .terminal | .empty, .branch _ | .terminal, .empty | .terminal, .branch _ | .branch _, .empty | .branch _, .terminal => isFalse (by intro same; cases same)
  /-- Decide equality of ascending physical child-map entries. -/
  def childrenDecEq : (left right : List (Nat × Trie)) → Decidable (left = right)
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse (by intro same; cases same)
    | (i, a) :: as, (j, b) :: bs =>
        if indices : i = j then
          match trieDecEq a b with
          | isFalse different => isFalse (fun same => different (congrArg Prod.snd (List.cons.inj same).1))
          | isTrue nodes =>
              match childrenDecEq as bs with
              | isTrue rest => isTrue (by cases indices; cases nodes; cases rest; rfl)
              | isFalse different => isFalse (fun same => different (List.cons.inj same).2)
        else isFalse (fun same => indices (congrArg Prod.fst (List.cons.inj same).1))
end

instance : DecidableEq Trie := trieDecEq

/-- A live constraint key retains class order and each physical trie. -/
abbrev Key := List Trie

/-- Read the fields used by the source PathEClass equality instance. -/
def key (records : List SourceEqualityClassOrder.Record) : Key := records.map (·.trie)

/-- Source IntMap representations use valid tries with ascending child entries. -/
def Represented (records : List SourceEqualityClassOrder.Record) : Prop :=
  ∀ record ∈ records, Valid record.trie ∧ Ascending record.trie

/-- Contradiction has its own tag. Each live payload receives an interned identity. -/
def identify (payload : SourceEqualityPrecheck.Constraint) (before : Cache.State Key) : Option Nat × Cache.State Key :=
  match payload with
  | none => (none, before)
  | some records =>
      let built := Cache.intern before (key records)
      (some built.1.identity, built.2)

/-- Physical interning preserves the cache invariant and stores the actual trie key. -/
theorem identify_live (records : List SourceEqualityClassOrder.Record) (before : Cache.State Key)
    (valid : Cache.Valid before) :
    Cache.Valid (identify (some records) before).2 ∧
      ∃ entry, (identify (some records) before).1 = some entry.identity ∧
        (identify (some records) before).2.table (key records) = some entry ∧ entry.key = key records := by
  have checked := Cache.intern_correct before (key records) valid
  exact ⟨checked.1, (Cache.intern before (key records)).1, rfl, checked.2⟩

/-- Equal stored identities mean equal ordered trie keys, in both directions. -/
theorem identity_iff (state : Cache.State Key) (valid : Cache.Valid state)
    (left : state.table (key first) = some firstEntry) (right : state.table (key second) = some secondEntry) :
    firstEntry.identity = secondEntry.identity ↔ key first = key second :=
  Cache.identity_eq_iff_key_eq state valid left right

/-- Contradiction does not allocate a live equality-constraint identity. -/
theorem contradiction (before : Cache.State Key) : identify none before = (none, before) := rfl

/-- An interned live empty payload cannot be the contradiction tag. -/
theorem empty_not_contradiction (before : Cache.State Key) : (identify (some []) before).1 ≠ none := by
  simp [identify]

/-- Path-set metadata cannot distinguish equal physical trie keys. -/
theorem identify_same (before : Cache.State Key) (first second : List SourceEqualityClassOrder.Record)
    (same : key first = key second) : identify (some first) before = identify (some second) before := by
  simp only [identify, same]

/-- A repeated physical payload retains its original identity and allocation state. -/
theorem identify_idempotent (before : Cache.State Key) (valid : Cache.Valid before)
    (records : List SourceEqualityClassOrder.Record) :
    identify (some records) (identify (some records) before).2 = identify (some records) before := by
  have repeated := Cache.intern_idempotent before (key records) valid
  simpa only [identify] using congrArg (fun result : Cache.Interned Key × Cache.State Key =>
    (some result.1.identity, result.2)) repeated

end MicroCFTA.SourceEqualityPartialConstraintKey
