import MicroCFTA.TermRepresentation

/-!
# Indexed child construction

`Term.fromAssocs` requires each index from zero to arity minus one exactly
once. Missing source slots are bottom. This model represents an unwritten
slot by `none` and proves that valid inputs fill every slot in index order.
-/

namespace MicroCFTA.ChildBuilder
open TermRepresentation

/-- The source sequence update loop, with explicit unwritten slots. -/
def writeAll (slots : List (Option α)) : List (Nat × α) → List (Option α)
  | [] => slots
  | (index, value) :: rest => writeAll (slots.set index (some value)) rest

/-- Sequence updates cannot change the declared arity. -/
theorem writeAll_length (slots : List (Option α)) (entries : List (Nat × α)) :
    (writeAll slots entries).length = slots.length := by
  induction entries generalizing slots with
  | nil => rfl
  | cons entry rest ih => simpa [writeAll] using ih (slots.set entry.1 (some entry.2))

/-- A position absent from the association list retains its previous contents. -/
theorem unwritten (slots : List (Option α)) (entries : List (Nat × α)) (query : Nat)
    (absent : ∀ entry ∈ entries, entry.1 ≠ query) :
    (writeAll slots entries)[query]? = slots[query]? := by
  induction entries generalizing slots with
  | nil => rfl
  | cons entry rest ih =>
      simp only [writeAll]
      rw [ih _ (fun item member => absent item (by simp [member]))]
      exact List.getElem?_set_ne (absent entry (by simp))

/-- A written position contains its designated value when repeated writes agree. -/
theorem written (slots : List (Option α)) (entries : List (Nat × α)) (query : Nat) (value : α)
    (bound : query < slots.length) (present : (query, value) ∈ entries)
    (consistent : ∀ entry ∈ entries, entry.1 = query → entry.2 = value) :
    (writeAll slots entries)[query]? = some (some value) := by
  induction entries generalizing slots with
  | nil => simp at present
  | cons entry rest ih =>
      by_cases later : (query, value) ∈ rest
      · exact ih (slots.set entry.1 (some entry.2)) (by simpa using bound) later
          (fun item member => consistent item (by simp [member]))
      · have same : (query, value) = entry := (List.mem_cons.mp present).resolve_right later
        subst entry
        simp only [writeAll]
        rw [unwritten]
        · exact List.getElem?_set_self bound
        · intro item member equal
          have sameValue := consistent item (by simp [member]) equal
          have sameEntry : item = (query, value) := Prod.ext equal sameValue
          exact later (by simpa [sameEntry] using member)

/-- Exact declared index/value correspondence for an association list. -/
def Describes (values : List α) (entries : List (Nat × α)) : Prop :=
  ∀ index value, (index, value) ∈ entries ↔ values[index]? = some value

/-- Every correctly described association list fills the complete sequence. -/
theorem writeAll_exact (values : List α) (entries : List (Nat × α))
    (describes : Describes values entries) :
    writeAll (List.replicate values.length none) entries = values.map some := by
  apply List.ext_getElem?
  intro query
  by_cases bound : query < values.length
  · have present : (query, values[query]) ∈ entries :=
      (describes query values[query]).mpr (List.getElem?_eq_getElem bound)
    rw [written _ entries query values[query] (by simpa using bound) present]
    · simp [List.getElem?_eq_getElem bound]
    · intro entry member same
      have value := (describes entry.1 entry.2).mp member
      rw [same, List.getElem?_eq_getElem bound] at value
      exact Option.some.inj value.symm
  · have outside : values.length ≤ query := by omega
    rw [List.getElem?_eq_none (by simpa [writeAll_length] using outside)]
    simp [List.getElem?_eq_none outside]

/-- Turn a fully initialized sequence into a child list. -/
def finish : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some value :: rest => (finish rest).map (value :: ·)

/-- A completely filled sequence has exactly its original child list. -/
theorem finish_map (values : List α) : finish (values.map some) = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [finish, ih]

/-- The generic many-child builder cannot leave a hole under its input contract. -/
theorem complete_builder (values : List α) (entries : List (Nat × α))
    (describes : Describes values entries) :
    finish (writeAll (List.replicate values.length none) entries) = some values := by
  rw [writeAll_exact values entries describes, finish_map]

/-- Source fast paths for zero through three children, then indexed sequence writes. -/
def fromAssocs (symbol : Symbol) (size : Nat) :
    List (Nat × Packed Symbol) → Option (Packed Symbol)
  | [] => some (.leaf symbol)
  | [(_, first)] => some (.one symbol first)
  | [(0, first), (_, second)] => some (.two symbol first second)
  | [(_, second), (_, first)] => some (.two symbol first second)
  | [(0, first), (1, second), (_, third)] => some (.three symbol first second third)
  | [(0, first), (_, third), (_, second)] => some (.three symbol first second third)
  | [(1, second), (0, first), (_, third)] => some (.three symbol first second third)
  | [(1, second), (_, third), (_, first)] => some (.three symbol first second third)
  | [(_, third), (0, first), (_, second)] => some (.three symbol first second third)
  | [(_, third), (_, second), (_, first)] => some (.three symbol first second third)
  | entries => (finish (writeAll (List.replicate size none) entries)).map (.many symbol)

/-- Canonical ordered index/value associations. -/
def indexed (values : List α) : List (Nat × α) := (values.zipIdx).map Prod.swap

/-- Indexed associations describe the child lookup independently of their order. -/
theorem indexed_describes (values : List α) : Describes values (indexed values) := by
  intro index value
  simp only [indexed, List.mem_map]
  constructor
  · rintro ⟨entry, member, same⟩
    have pair : entry = (value, index) := by
      have swapped := congrArg Prod.swap same
      simpa using swapped
    subst entry
    simpa using (List.mem_zipIdx_iff_getElem?.mp member)
  · intro found
    exact ⟨(value, index), List.mem_zipIdx_iff_getElem?.mpr found, rfl⟩

/-- Reordering valid input associations changes no indexed value. -/
theorem permutation_describes (values : List α) (entries : List (Nat × α))
    (order : entries.Perm (indexed values)) : Describes values entries := by
  intro index value
  exact (order.mem_iff).trans (indexed_describes values index value)

/-- The two-element permutations retain both entries exactly once. -/
private theorem perm_pair (entries : List α) (a b : α)
    (order : entries.Perm [a, b]) : entries = [a, b] ∨ entries = [b, a] := by
  cases entries with
  | nil => have := order.length_eq; simp at this
  | cons first rest =>
    have member := order.mem_iff.mp List.mem_cons_self
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inl (congrArg (first :: ·) (List.Perm.eq_singleton order.cons_inv))
    · have remaining : rest.Perm [a] := (order.trans (List.Perm.swap _ _ [])).cons_inv
      exact Or.inr (congrArg (first :: ·) remaining.eq_singleton)

/-- The three-element permutations retain all entries exactly once. -/
private theorem perm_triple (entries : List α) (a b c : α)
    (order : entries.Perm [a, b, c]) :
    entries = [a,b,c] ∨ entries = [a,c,b] ∨ entries = [b,a,c] ∨
      entries = [b,c,a] ∨ entries = [c,a,b] ∨ entries = [c,b,a] := by
  cases entries with
  | nil => have := order.length_eq; simp at this
  | cons first rest =>
    have member := order.mem_iff.mp List.mem_cons_self
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rcases perm_pair rest b c order.cons_inv with rfl | rfl <;> simp
    · have remaining : rest.Perm [a,c] := (order.trans (List.Perm.swap _ _ [c])).cons_inv
      rcases perm_pair rest a c remaining with rfl | rfl <;> simp
    · have moved : [a,b,first].Perm [first,a,b] := by
        exact (List.Perm.cons a (List.Perm.swap first b [])).trans (List.Perm.swap first a [b])
      have remaining : rest.Perm [a,b] := (order.trans moved).cons_inv
      rcases perm_pair rest a b remaining with rfl | rfl <;> simp

/-- Every source fast path agrees with the indexed builder on valid input. -/
theorem fromAssocs_correct (symbol : Symbol) (values : List (Packed Symbol))
    (entries : List (Nat × Packed Symbol)) (order : entries.Perm (indexed values)) :
    fromAssocs symbol values.length entries = some (node symbol values) := by
  have length : entries.length = values.length := by simpa [indexed] using order.length_eq
  have complete := complete_builder values entries (permutation_describes values entries order)
  cases values with
  | nil =>
      have empty : entries = [] := List.eq_nil_of_length_eq_zero length
      subst entries
      rfl
  | cons a rest => cases rest with
    | nil =>
      have shape : entries = [(0,a)] := order.eq_singleton
      subst entries
      rfl
    | cons b rest => cases rest with
      | nil =>
        have shape : entries.Perm [(0,a),(1,b)] := order
        rcases perm_pair entries (0,a) (1,b) shape with rfl | rfl <;> rfl
      | cons c rest => cases rest with
        | nil =>
          have shape : entries.Perm [(0,a),(1,b),(2,c)] := order
          rcases perm_triple entries (0,a) (1,b) (2,c) shape with
            rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
        | cons d rest =>
          cases entries with
          | nil => simp at length
          | cons e entries => cases entries with
            | nil => simp at length
            | cons f entries => cases entries with
              | nil => simp at length
              | cons g entries => cases entries with
                | nil => simp at length
                | cons h entries => simpa [fromAssocs, node] using congrArg (Option.map (Packed.many symbol)) complete

/-- Indexed construction preserves canonical storage and every valid child. -/
theorem fromAssocs_valid (symbol : Symbol) (values : List (Packed Symbol))
    (entries : List (Nat × Packed Symbol)) (order : entries.Perm (indexed values))
    (valid : ∀ child ∈ values, Valid child) :
    ∃ result, fromAssocs symbol values.length entries = some result ∧
      Valid result ∧ children result = values :=
  ⟨node symbol values, fromAssocs_correct symbol values entries order,
    node_valid symbol values valid, (node_views symbol values).2⟩

end MicroCFTA.ChildBuilder
