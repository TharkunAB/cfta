import MicroCFTA.IntersectionEmptyDomain
import MicroCFTA.SourcePreparedSharedRows

/-!
# Actual recursive intersection bindings and domain keys

Source Mu branches bind each complete Mu at its own identity. Canonical
domain keys retain those identities. Physical record readback then returns
the exact original binder, including after later constructor effects.
-/
namespace MicroCFTA.SourceRecursiveIntersectionDomain
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedBinderProtocol
open IntersectionFlatMemoKeyDomain CanonicalClasses
open Std
attribute [local instance] lexOrd

/-- The source domain's free-map keys are its enclosing Mu identities. -/
def names (domain : DomainKey) : List Nat := domain.free.map Prod.fst

/-- Source binder entries retain the original Mu under that same identity. -/
def Typed (domain : DomainKey) : Prop := ∀ binding ∈ domain.free, binding.2 = NodeRef.mu binding.1

/-- Every source free binding has its actual complete physical Mu payload. -/
def AvailableBindings (state : State Symbol Guard) (domain : DomainKey) : Prop :=
  ∀ name ∈ names domain, ∃ entry body depth ordinary,
    entry.identity = name ∧ Available state (.mu entry body depth ordinary)

/-- Extend the source map and recursive-pair set, then read both in canonical key order. -/
def extend (domain : DomainKey) (bound : List Nat) (pair : Nat × Nat) : DomainKey :=
  ⟨(sortedSet (bound ++ names domain)).map (fun name => (name, NodeRef.mu name)), sortedSet (pair :: domain.seen)⟩

/-- Ascending distinct natural keys are strictly ordered. -/
theorem nat_ordered (values : List Nat) : (sortedSet values).Pairwise (fun left right => left < right) := by
  have ordered := sortedSet_ordered values
  have distinct : (sortedSet values).Pairwise (fun left right => left ≠ right) := sortedSet_nodup values
  apply (ordered.and distinct).imp
  intro left right both
  have bounded : left ≤ right := Nat.isLE_compare.mp both.1
  omega

/-- Ascending distinct pair keys use exactly the source IntersectId order. -/
theorem pairs_ordered (values : List (Nat × Nat)) : (sortedSet values).Pairwise pairLess := by
  have ordered := sortedSet_ordered values
  have distinct : (sortedSet values).Pairwise (fun left right => left ≠ right) := sortedSet_nodup values
  apply (ordered.and distinct).imp
  intro left right both
  have comparison := both.1
  have different := both.2
  change ((compare left.1 right.1).then (compare left.2 right.2)).isLE = true at comparison
  rcases Nat.lt_trichotomy left.1 right.1 with smaller | equal | larger
  · exact Or.inl smaller
  · have first : compare left.1 right.1 = .eq := Nat.compare_eq_eq.mpr equal
    simp only [first] at comparison
    have bounded : left.2 ≤ right.2 := Nat.isLE_compare.mp comparison
    have apart : left.2 ≠ right.2 := fun same => different (Prod.ext equal same)
    exact Or.inr ⟨equal, by omega⟩
  · have first : compare left.1 right.1 = .gt := Nat.compare_eq_gt.mpr larger
    simp [first] at comparison

/-- Domain readback has the same strictly ascending map and set order as the source. -/
theorem extend_canonical (domain : DomainKey) (bound : List Nat) (pair : Nat × Nat) : Canonical (extend domain bound pair) := by
  constructor
  · exact (List.pairwise_map.mpr (nat_ordered (bound ++ names domain)))
  · exact pairs_ordered (pair :: domain.seen)

/-- Read the structural node reference of one source free-map entry. -/
def keyLookup (domain : DomainKey) (name : Nat) : Option NodeRef :=
  (domain.free.find? (fun binding => binding.1 == name)).map Prod.snd

/-- Every typed source lookup has its own Mu identity, independently of duplicate entries. -/
theorem keyLookup_typed (domain : DomainKey) (typed : Typed domain) (name : Nat) :
    keyLookup domain name = if name ∈ names domain then some (.mu name) else none := by
  cases domain with
  | mk free seen =>
      induction free with
      | nil => rfl
      | cons binding rest ih =>
          have first := typed binding List.mem_cons_self
          have tail : Typed ⟨rest, seen⟩ := fun other member => typed other (List.mem_cons_of_mem _ member)
          by_cases same : binding.1 = name
          · simp [keyLookup, names, same, first]
          · simp only [keyLookup, List.find?_cons, beq_eq_false_iff_ne.mpr same]
            have equation := ih tail
            simp only [keyLookup] at equation
            rw [equation]
            simp only [names, List.map_cons, List.mem_cons, Ne.symm same, false_or]
            rfl

/-- The exact source free-map domain after extension. -/
theorem extend_names (domain : DomainKey) (bound : List Nat) (pair : Nat × Nat) (name : Nat) :
    name ∈ names (extend domain bound pair) ↔ name ∈ bound ∨ name ∈ names domain := by
  simp [names, extend, List.map_map, Function.comp_def, mem_sortedSet]

/-- The exact source recursive-pair set after insertion. -/
theorem extend_seen (domain : DomainKey) (bound : List Nat) (pair next : Nat × Nat) :
    next ∈ (extend domain bound pair).seen ↔ next = pair ∨ next ∈ domain.seen := by
  simp [extend, mem_sortedSet]

/-- Every extended binding still names its own original Mu. -/
theorem extend_typed (domain : DomainKey) (bound : List Nat) (pair : Nat × Nat) : Typed (extend domain bound pair) := by
  intro binding member
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- Canonical extension has the exact source last-new-binding overwrite and old-map fallback. -/
theorem extend_lookup_source (domain : DomainKey) (typed : Typed domain) (bound : List Nat) (pair : Nat × Nat) (name : Nat) :
    keyLookup (extend domain bound pair) name =
      keyLookup ⟨(bound.map (fun key => (key, NodeRef.mu key))).reverse ++ domain.free, pair :: domain.seen⟩ name := by
  let source : DomainKey := ⟨(bound.map (fun key => (key, NodeRef.mu key))).reverse ++ domain.free, pair :: domain.seen⟩
  have sourceTyped : Typed source := by
    intro binding member
    rcases List.mem_append.mp member with new | old
    · obtain ⟨key, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp new)
      rfl
    · exact typed binding old
  rw [keyLookup_typed _ (extend_typed domain bound pair), keyLookup_typed source sourceTyped]
  have same : name ∈ names (extend domain bound pair) ↔ name ∈ names source := by
    rw [extend_names]
    simp [names, source, List.map_map, Function.comp_def]
  simp only [same]

/-- Earlier and newly encountered Mu payloads supply every actual extended binding. -/
theorem extend_available (state : State Symbol Guard) (domain : DomainKey) (bound : List Nat) (pair : Nat × Nat)
    (old : AvailableBindings state domain)
    (new : ∀ name ∈ bound, ∃ entry body depth ordinary, entry.identity = name ∧ Available state (.mu entry body depth ordinary)) :
    AvailableBindings state (extend domain bound pair) := by
  intro name member
  rcases (extend_names domain bound pair name).mp member with first | earlier
  · exact new name first
  · exact old name earlier

/-- Later constructor effects retain the exact original physical bindings. -/
theorem AvailableBindings.grows (before after : State Symbol Guard) (domain : DomainKey)
    (available : AvailableBindings before domain) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) : AvailableBindings after domain := by
  intro name member
  obtain ⟨entry, body, depth, ordinary, same, stored⟩ := available name member
  exact ⟨entry, body, depth, ordinary, same, stored.grows before after growth history⟩

/-- Resolve only an actual bound RecInt identity through the canonical physical payload maps. -/
def lookup (state : State Symbol Guard) (domain : DomainKey) (name : Nat) : Option (Value Symbol Guard) :=
  if name ∈ names domain then SourcePreparedSharedRows.read state name else none

/-- Source lookup returns the exact original available Mu, with all stored probes and body. -/
theorem lookup_mu (state : State Symbol Guard) (facts : Facts state) (domain : DomainKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (available : Available state (.mu entry body depth ordinary)) (member : entry.identity ∈ names domain) :
    lookup state domain entry.identity = some (.mu entry body depth ordinary) := by
  rw [lookup, ite_eq_left member]
  exact SourcePreparedSharedRows.read_identity state facts _ available entry.identity rfl

/-- Available source bindings exclude missing lookup results. -/
theorem lookup_complete (state : State Symbol Guard) (facts : Facts state) (domain : DomainKey)
    (available : AvailableBindings state domain) (name : Nat) (member : name ∈ names domain) :
    ∃ entry body depth ordinary, entry.identity = name ∧ Available state (.mu entry body depth ordinary) ∧
      lookup state domain name = some (.mu entry body depth ordinary) := by
  obtain ⟨entry, body, depth, ordinary, rfl, stored⟩ := available name member
  exact ⟨entry, body, depth, ordinary, rfl, stored, lookup_mu state facts domain entry body depth ordinary stored member⟩

/-- Canonical domain allocation retains the exact extended structural key. -/
theorem intern_extended (state : Cache.State DomainKey) (valid : Cache.Valid state)
    (domain : DomainKey) (bound : List Nat) (pair : Nat × Nat) :
    Cache.Valid (IntersectionEmptyDomain.make state (extend domain bound pair)).2 ∧
      IntersectionEmptyDomain.Represents (IntersectionEmptyDomain.make state (extend domain bound pair)).2
        (extend domain bound pair) (IntersectionEmptyDomain.make state (extend domain bound pair)).1 :=
  IntersectionEmptyDomain.make_correct state valid (extend domain bound pair)

end MicroCFTA.SourceRecursiveIntersectionDomain
