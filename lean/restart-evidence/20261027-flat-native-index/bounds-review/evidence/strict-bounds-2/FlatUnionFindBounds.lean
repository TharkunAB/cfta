import MicroCFTA.FlatUnionFindUnion

/-!
# Allocation bounds for direct-parent forests

The bound limits explicit map keys. Validity then limits parent targets and
stored members too. Semantic correspondence alone does not give this bound.
-/

namespace MicroCFTA.FlatUnionFind

/-- Every explicit map key is below the supplied allocation limit. -/
def StoredBelow (forest : Forest) (bound : Nat) : Prop :=
  ∀ uv entry, forest uv = some entry → uv < bound

/-- A larger allocation limit retains every explicit-key bound. -/
theorem StoredBelow.mono (bounded : StoredBelow forest bound) (larger : bound ≤ next) :
    StoredBelow forest next :=
  fun uv entry stored => Nat.lt_of_lt_of_le (bounded uv entry stored) larger

/-- The next unallocated variable has no explicit map entry. -/
theorem StoredBelow.fresh (bounded : StoredBelow forest bound) : forest bound = none := by
  cases stored : forest bound with
  | none => rfl
  | some entry => exact False.elim (Nat.lt_irrefl bound (bounded bound entry stored))

/-- Bounded initial variables establish the explicit-key bound. -/
theorem initial_storedBelow (variables : List Nat) (bound : Nat)
    (inside : ∀ uv ∈ variables, uv < bound) : StoredBelow (withInitialValues variables) bound := by
  intro uv entry stored
  by_cases member : uv ∈ variables
  · exact inside uv member
  · simp [withInitialValues, member] at stored

/-- The representative of an allocated variable remains allocated. -/
theorem root_lt (valid : Valid forest) (bounded : StoredBelow forest bound)
    (inside : uv < bound) : root forest uv < bound := by
  cases stored : forest uv with
  | none => simpa [root, stored] using inside
  | some entry =>
      cases entry with
      | root size members => simpa [root, stored] using inside
      | parent parent =>
          obtain ⟨size, members, target⟩ := valid.parents uv parent stored
          simpa [root, stored] using bounded parent (.root size members) target

/-- Every member of an allocated root class remains allocated. -/
theorem member_lt (valid : Valid forest) (bounded : StoredBelow forest bound)
    (fixed : root forest representative = representative) (inside : representative < bound)
    (member : uv ∈ (entryOf forest representative).2) : uv < bound := by
  have same := ((entryOf_spec valid fixed).2.2 uv).mp member
  cases stored : forest uv with
  | none =>
      have equal : uv = representative := by simpa [root, stored] using same
      simpa only [equal] using inside
  | some entry => exact bounded uv entry stored

/-- A merge writes only the bounded winner and the supplied bounded members. -/
theorem merge_storedBelow (bounded : StoredBelow forest bound)
    (winnerInside : winner < bound) (membersInside : ∀ uv ∈ loserMembers, uv < bound)
    (winnerSize loserSize : Nat) (winnerMembers : List Nat) :
    StoredBelow (merge forest winner winnerSize loserSize loserMembers winnerMembers) bound := by
  intro uv entry stored
  by_cases atWinner : uv = winner
  · simpa only [atWinner] using winnerInside
  · by_cases inMembers : uv ∈ loserMembers
    · exact membersInside uv inMembers
    · apply bounded uv entry
      simpa only [merge_lookup, atWinner, inMembers, ↓reduceIte] using stored

/-- Linking bounded root classes retains the explicit-key bound. -/
theorem link_storedBelow (valid : Valid forest) (bounded : StoredBelow forest bound)
    (loserRoot : root forest loser = loser) (loserInside : loser < bound)
    (winnerInside : winner < bound) : StoredBelow (link forest loser winner) bound := by
  exact merge_storedBelow bounded winnerInside
    (fun uv member => member_lt valid bounded loserRoot loserInside member) _ _ _

/-- Union of allocated variables preserves the explicit-key bound. -/
theorem union_storedBelow (valid : Valid forest) (bounded : StoredBelow forest bound)
    (leftInside : left < bound) (rightInside : right < bound) :
    StoredBelow (union forest left right) bound := by
  have leftRoot := root_lt valid bounded leftInside
  have rightRoot := root_lt valid bounded rightInside
  dsimp only [union]
  by_cases same : root forest left = root forest right
  · simpa only [same, ↓reduceIte] using bounded
  · simp only [same, ↓reduceIte, unionRoots]
    split
    · exact link_storedBelow valid bounded (root_root valid left) leftRoot rightRoot
    · exact link_storedBelow valid bounded (root_root valid right) rightRoot leftRoot

end MicroCFTA.FlatUnionFind
