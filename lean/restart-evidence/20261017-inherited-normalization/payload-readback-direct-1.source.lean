import MicroCFTA.SourceEqualityInheritedPayload

/-!
# Exact readback of well-formed inherited payloads

Valid ascending tries have one physical representation for each path set.
Reading the stored paths therefore retains every record and its list position.
This result does not require normalization of the complete class list.
-/
namespace MicroCFTA.SourceCurrentEqualityPayloadReadback
open EqualityTrie EqualityNormalize SourceEqualityClassOrder

private theorem key_member (children : List (Nat × Trie))
    (valid : ∀ index child, (index, child) ∈ children → child ≠ .empty ∧ Valid child)
    (index : Nat) :
    index ∈ children.map Prod.fst ↔ ∃ suffix, index :: suffix ∈ fromChildren children := by
  constructor
  · intro member
    obtain ⟨⟨key, child⟩, present, same⟩ := List.mem_map.mp member
    subst key
    obtain ⟨suffix, found⟩ := valid_has_path child (valid index child present).2
      (valid index child present).1
    exact ⟨suffix, (mem_fromChildren children _).mpr ⟨index, child, suffix, present, found, rfl⟩⟩
  · rintro ⟨suffix, found⟩
    obtain ⟨key, child, tail, present, _, same⟩ := (mem_fromChildren children _).mp found
    cases same
    exact List.mem_map.mpr ⟨(key, child), present, rfl⟩

private theorem children_eq (first second : List (Nat × Trie))
    (keys : first.map Prod.fst = second.map Prod.fst)
    (same : ∀ index child, (index, child) ∈ first →
      ∀ other, (index, other) ∈ second → child = other) : first = second := by
  induction first generalizing second with
  | nil => cases second <;> simp_all
  | cons entry rest ih =>
      obtain ⟨index, child⟩ := entry
      cases second with
      | nil => simp at keys
      | cons entry remaining =>
          obtain ⟨key, other⟩ := entry
          change index :: rest.map Prod.fst = key :: remaining.map Prod.fst at keys
          have equal := List.cons.inj keys
          have indexEqual := equal.1
          subst key
          have heads := same index child List.mem_cons_self other List.mem_cons_self
          have tails := ih remaining (List.cons.inj keys).2
            (fun i value member next present => same i value (List.mem_cons_of_mem _ member)
              next (List.mem_cons_of_mem _ present))
          rw [heads, tails]

private theorem trie_eq (first second : Trie) (firstValid : Valid first)
    (secondValid : Valid second) (firstAscending : Ascending first)
    (secondAscending : Ascending second)
    (same : ∀ path, path ∈ fromPathTrie first ↔ path ∈ fromPathTrie second) : first = second := by
  cases first with
  | empty =>
      cases second with
      | empty => rfl
      | terminal => have found := (same []).mpr (by simp [fromPathTrie]); simp [fromPathTrie] at found
      | branch children =>
          obtain ⟨path, found⟩ := valid_has_path (.branch children) secondValid (by intro impossible; cases impossible)
          have found := (same path).mpr found
          simp [fromPathTrie] at found
  | terminal =>
      have terminal := (nil_mem second).mp ((same []).mp (by simp [fromPathTrie]))
      exact terminal.symm
  | branch first =>
      cases second with
      | empty =>
          obtain ⟨path, found⟩ := valid_has_path (.branch first) firstValid (by intro impossible; cases impossible)
          have found := (same path).mp found
          simp [fromPathTrie] at found
      | terminal =>
          have impossible := (nil_mem (.branch first)).mp ((same []).mpr (by simp [fromPathTrie]))
          cases impossible
      | branch second =>
          have members : ∀ index, index ∈ first.map Prod.fst ↔ index ∈ second.map Prod.fst := by
            intro index
            rw [key_member first firstValid.2.2, key_member second secondValid.2.2]
            exact exists_congr (fun suffix => same (index :: suffix))
          have perm := (List.perm_ext_iff_of_nodup firstValid.2.1 secondValid.2.1).mpr members
          have keys := perm.eq_of_pairwise
            (fun _ _ _ _ before after => Nat.le_antisymm before after)
            (firstAscending.1.imp Nat.le_of_lt) (secondAscending.1.imp Nat.le_of_lt)
          apply congrArg Trie.branch
          apply children_eq first second keys
          intro index child member other present
          apply trie_eq child other (firstValid.2.2 index child member).2
            (secondValid.2.2 index other present).2 (firstAscending.2 index child member)
            (secondAscending.2 index other present)
          intro suffix
          have firstLookup := lookup_of_mem index first child firstValid.2.1 member
          have secondLookup := lookup_of_mem index second other secondValid.2.1 present
          have firstRead := descend_exact (.branch first) firstValid index suffix
          have secondRead := descend_exact (.branch second) secondValid index suffix
          simpa only [pathTrieDescend, firstLookup, secondLookup, Option.getD_some] using
            firstRead.trans ((same (index :: suffix)).trans secondRead.symm)
termination_by sizeOf first
decreasing_by
  have smaller := List.sizeOf_lt_of_mem member
  simp_all only [Prod.mk.sizeOf_spec, Trie.branch.sizeOf_spec]
  omega

/-- Reading one coherent ascending record retains both physical fields. -/
theorem record (original : Record) (coherent : Coherent original)
    (ascending : Ascending original.trie) : recordOf original.paths = some original := by
  have enumerated := canonicalClass_ext original.paths (fromPathTrie original.trie)
    (fun path => (coherent.2.2 path).symm)
  rw [coherent.2.1, SourceEqualityDescend.canonical_fromTrie original.trie coherent.1 ascending] at enumerated
  have supported : Supported original.paths := by
    rw [enumerated]
    exact fromPathTrie_supported original.trie coherent.1
  have supportedErase : Supported original.paths.eraseDups := by
    simpa only [List.eraseDups_eq_self.mpr (supported_nodup _ supported)] using supported
  obtain ⟨actual, built, valid, _, paths⟩ := toPathTrie_correct original.paths.eraseDups supportedErase
  simp only [List.mem_eraseDups] at paths
  have equal := trie_eq actual original.trie valid coherent.1 (build_ascending _ _ _ built) ascending
    (fun path => (paths path).trans (coherent.2.2 path).symm)
  simp only [recordOf, built, Option.map_some, equal, coherent.2.1]

/-- Reading a coherent ascending record list retains its order and repeats. -/
theorem records (originals : List Record)
    (coherent : ∀ original ∈ originals, Coherent original)
    (ascending : ∀ original ∈ originals, Ascending original.trie) :
    recordsOf (originals.map Record.paths) = some originals := by
  induction originals with
  | nil => rfl
  | cons first rest ih =>
      have head := record first (coherent first List.mem_cons_self) (ascending first List.mem_cons_self)
      have tail := ih (fun original member => coherent original (List.mem_cons_of_mem _ member))
        (fun original member => ascending original (List.mem_cons_of_mem _ member))
      simp only [List.map_cons, recordsOf, head, tail, Option.bind_some]
      rfl

/-- A well-formed inherited payload has exact physical readback without class normalization. -/
theorem read (payload : SourceEqualityPrecheck.Constraint) (wellFormed : SourceEqualityDescend.WellFormed payload) :
    SourceEqualityPhysicalPayload.read (SourceEqualityInheritedPayload.classes payload) = .ok payload := by
  cases payload with
  | none => rfl
  | some originals =>
      have exact := records originals (fun original member => (wellFormed originals rfl original member).1)
        (fun original member => (wellFormed originals rfl original member).2.1)
      simp only [SourceEqualityInheritedPayload.classes, Option.map_some, SourceEqualityPhysicalPayload.read, exact]

end MicroCFTA.SourceCurrentEqualityPayloadReadback
