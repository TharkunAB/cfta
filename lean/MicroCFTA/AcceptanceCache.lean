import MicroCFTA.AcceptanceReference

/-!
# Memoized acceptance cache

The cache key is the numbered subtree position and the automaton state.
Each cached Boolean agrees with direct acceptance of the registered subtree.
Numbering establishes the registry used by this invariant.
-/

namespace MicroCFTA.AcceptanceCache
open Language NumberedTerms AcceptanceReference

/-- Read the unique cache position of a numbered node. -/
def position : Positioned Symbol → Nat
  | .node index _ _ => index

mutual
/-- Store every numbered subtree in preorder. -/
def nodeEntries : Positioned Symbol → List (Nat × Term Symbol)
  | .node index term children => (index, term) :: childEntries children

/-- Concatenate each child's numbered subtree entries. -/
def childEntries : List (Positioned Symbol) → List (Nat × Term Symbol)
  | [] => []
  | first :: rest => nodeEntries first ++ childEntries rest
end

mutual
/-- Registry keys equal the previously verified preorder positions. -/
theorem nodeEntries_positions (node : Positioned Symbol) : (nodeEntries node).map Prod.fst = positions node := by
  cases node with
  | node index term children => simp [nodeEntries, positions, childEntries_positions]

/-- Child registry keys equal their forest positions. -/
theorem childEntries_positions (nodes : List (Positioned Symbol)) :
    (childEntries nodes).map Prod.fst = forestPositions nodes := by
  cases nodes with
  | nil => rfl
  | cons first rest => simp [childEntries, forestPositions, nodeEntries_positions, childEntries_positions]
end

/-- Unique registry keys retrieve the exact stored subtree of every entry. -/
theorem lookup_unique (entries : List (Nat × α)) (unique : (entries.map Prod.fst).Nodup)
    (entry : Nat × α) (present : entry ∈ entries) : entries.lookup entry.1 = some entry.2 := by
  induction entries with
  | nil => simp at present
  | cons first rest ih =>
      rcases first with ⟨firstKey, firstValue⟩
      rcases entry with ⟨entryKey, entryValue⟩
      have separated := List.nodup_cons.mp unique
      rcases List.mem_cons.mp present with same | later
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        simp
      · have distinct : entryKey ≠ firstKey := by
          intro same
          apply separated.1
          exact same ▸ List.mem_map.mpr ⟨(entryKey, entryValue), later, rfl⟩
        have different : (entryKey == firstKey) = false := by simp [distinct]
        simpa [List.lookup_cons, different] using ih separated.2 later

/-- A registry assigns the correct complete subtree to every position used below this node. -/
def Registered (registry : Nat → Option (Term Symbol)) (node : Positioned Symbol) : Prop :=
  ∀ entry ∈ nodeEntries node, registry entry.1 = some entry.2

/-- The source's complete numbering provides a valid immutable subtree registry. -/
theorem number_registered (term : Term Symbol) (next : Nat) :
    Registered (fun index => (nodeEntries (number term next).2).lookup index) (number term next).2 := by
  intro entry present
  apply lookup_unique _ _ entry present
  rw [nodeEntries_positions]
  exact numbered_positions_unique term next

/-- Every child entry is present in the enclosing forest registry. -/
theorem childEntries_member (children : List (Positioned Symbol)) (child : Positioned Symbol)
    (present : child ∈ children) (entry : Nat × Term Symbol) (member : entry ∈ nodeEntries child) :
    entry ∈ childEntries children := by
  induction children with
  | nil => simp at present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact List.mem_append_left _ member
      · exact List.mem_append_right _ (ih later)

/-- Registered subtrees retain the same registry during recursive calls. -/
theorem registered_child (registry : Nat → Option (Term Symbol)) (index : Nat) (term : Term Symbol)
    (children : List (Positioned Symbol)) (registered : Registered registry (.node index term children))
    (child : Positioned Symbol) (present : child ∈ children) : Registered registry child := by
  intro entry member
  exact registered entry (List.mem_cons_of_mem _ (childEntries_member children child present entry member))

/-- The root entry itself is always registered. -/
theorem registered_root (registry : Nat → Option (Term Symbol)) (node : Positioned Symbol)
    (registered : Registered registry node) : registry (position node) = some (original node) := by
  cases node with
  | node index term children => exact registered (index, term) (by simp [nodeEntries])

/-- Every child inherits the stored-subtree representation invariant. -/
theorem valid_child (children : List (Positioned Symbol)) (valid : AllValid children)
    (child : Positioned Symbol) (present : child ∈ children) : Valid child := by
  induction children with
  | nil => simp at present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact valid.1
      · exact ih valid.2 later

/-- Cache truth uses sufficient structural fuel and therefore equals finite-run acceptance. -/
def truth [DecidableEq Symbol] (automaton : Automaton State Symbol) (key : State) (term : Term Symbol) : Bool :=
  accept automaton term.height key term

/-- Additional sufficient fuel does not change a subtree's acceptance. -/
theorem accept_truth [DecidableEq Symbol] (automaton : Automaton State Symbol) (fuel : Nat)
    (key : State) (term : Term Symbol) (enough : term.height ≤ fuel) :
    accept automaton fuel key term = truth automaton key term := by
  apply Bool.eq_iff_iff.mpr
  exact (accept_complete automaton fuel key term enough).trans
    (accept_complete automaton term.height key term (Nat.le_refl _)).symm

/-- This functional finite-map interface records exactly the source lookup and insertion behavior. -/
abbrev Cache (State : Type) := Nat × State → Option Bool

/-- Every cached answer refers to the same registered subtree and its exact acceptance truth. -/
def Sound [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (registry : Nat → Option (Term Symbol)) (cache : Cache State) : Prop :=
  ∀ index key answer, cache (index, key) = some answer →
    ∃ term, registry index = some term ∧ answer = truth automaton key term

/-- An empty cache satisfies the invariant without checking any alternative. -/
theorem empty_sound [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (registry : Nat → Option (Term Symbol)) : Sound automaton registry (fun _ => none) := by
  intro index key answer found
  cases found

/-- Store one result after its complete shared subtree search returns. -/
def insert [DecidableEq State] (cache : Cache State) (index : Nat) (key : State) (answer : Bool) : Cache State :=
  fun query => if query = (index, key) then some answer else cache query

/-- Inserting a computed answer preserves every cache invariant. -/
theorem insert_sound [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (registry : Nat → Option (Term Symbol)) (cache : Cache State) (sound : Sound automaton registry cache)
    (index : Nat) (key : State) (term : Term Symbol) (registered : registry index = some term) :
    Sound automaton registry (insert cache index key (truth automaton key term)) := by
  intro other otherKey answer found
  by_cases same : (other, otherKey) = (index, key)
  · cases same
    have equal : truth automaton key term = answer := by simpa [insert] using found
    exact ⟨term, registered, equal.symm⟩
  · exact sound other otherKey answer (by simpa [insert, same] using found)

/-- A child visit reads its cache entry before evaluating and storing a new answer. -/
def visit [DecidableEq State] (compute : State → Positioned Symbol → Cache State → Bool × Cache State)
    (key : State) (node : Positioned Symbol) (cache : Cache State) : Bool × Cache State :=
  match cache (position node, key) with
  | some answer => (answer, cache)
  | none =>
      let result := compute key node cache
      (result.1, insert result.2 (position node) key result.1)

/-- Both cache hits and newly computed visits return the exact subtree truth and preserve the cache. -/
theorem visit_correct [DecidableEq Symbol] [DecidableEq State] (automaton : Automaton State Symbol)
    (registry : Nat → Option (Term Symbol)) (compute : State → Positioned Symbol → Cache State → Bool × Cache State)
    (key : State) (node : Positioned Symbol) (cache : Cache State) (registered : Registered registry node)
    (sound : Sound automaton registry cache)
    (correct : (compute key node cache).1 = truth automaton key (original node) ∧
      Sound automaton registry (compute key node cache).2) :
    (visit compute key node cache).1 = truth automaton key (original node) ∧
      Sound automaton registry (visit compute key node cache).2 := by
  cases found : cache (position node, key) with
  | some answer =>
      obtain ⟨term, stored, accepted⟩ := sound (position node) key answer found
      have same : term = original node := Option.some.inj (stored.symm.trans (registered_root registry node registered))
      simpa [visit, found, same] using And.intro accepted sound
  | none =>
      simp only [visit, found]
      refine ⟨correct.1, ?_⟩
      rw [correct.1]
      exact insert_sound automaton registry _ correct.2 _ key _ (registered_root registry node registered)

/-- Cache extension retains every previously stored answer. -/
def Extends (before after : Cache State) : Prop :=
  ∀ query answer, before query = some answer → after query = some answer

/-- Cache retention composes across consecutive child and alternative actions. -/
theorem extends_trans (first middle last : Cache State) (left : Extends first middle) (right : Extends middle last) :
    Extends first last := fun query answer found => right query answer (left query answer found)

/-- A visit preserves all old entries and inserts the newly requested result on a miss. -/
theorem visit_extends [DecidableEq State]
    (compute : State → Positioned Symbol → Cache State → Bool × Cache State)
    (key : State) (node : Positioned Symbol) (cache : Cache State)
    (preserved : Extends cache (compute key node cache).2) :
    Extends cache (visit compute key node cache).2 := by
  intro query answer found
  cases cached : cache (position node, key) with
  | some stored => simpa [visit, cached] using found
  | none =>
      have different : query ≠ (position node, key) := by intro same; subst query; rw [cached] at found; contradiction
      simpa [visit, cached, insert, different] using preserved query answer found

/-- A cache hit returns immediately and runs no subtree computation. -/
theorem visit_hit [DecidableEq State]
    (compute : State → Positioned Symbol → Cache State → Bool × Cache State)
    (key : State) (node : Positioned Symbol) (cache : Cache State) (answer : Bool)
    (found : cache (position node, key) = some answer) : visit compute key node cache = (answer, cache) := by
  simp [visit, found]

/-- Every child visit leaves its answer stored for all later visits to the same position and state. -/
theorem visit_stored [DecidableEq State]
    (compute : State → Positioned Symbol → Cache State → Bool × Cache State)
    (key : State) (node : Positioned Symbol) (cache : Cache State) :
    (visit compute key node cache).2 (position node, key) = some (visit compute key node cache).1 := by
  cases found : cache (position node, key) <;> simp [visit, found, insert]

end MicroCFTA.AcceptanceCache
