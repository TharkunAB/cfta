import Std

/-!
# Equality path tries

This module models `Equality.Constraint.PathTrie`. A terminal has no children.
Construction groups nonempty paths by their first index. Invalid input returns
`none` instead of the Haskell exception. Natural indices describe the supported
nonnegative path domain. Finite child lists represent the `IntMap` entries.
-/

namespace MicroCFTA.EqualityTrie

abbrev Path := List Nat

/-- A terminal-or-branch trie for equality paths. -/
inductive Trie where
  | empty
  | terminal
  | branch (children : List (Nat × Trie))
  deriving Repr

mutual
  /-- Enumerate every represented path. -/
  def fromPathTrie : Trie → List Path
    | .empty => []
    | .terminal => [[]]
    | .branch children => fromChildren children
  /-- Prefix each child path by its child index. -/
  def fromChildren : List (Nat × Trie) → List Path
    | [] => []
    | (index, child) :: rest => (fromPathTrie child).map (index :: ·) ++ fromChildren rest
end

/-- Read a finite child map. -/
def lookup (index : Nat) : List (Nat × Trie) → Option Trie
  | [] => none
  | (key, child) :: rest => if index = key then some child else lookup index rest

/-- Descend one index. Missing children and terminals have no suffix paths. -/
def pathTrieDescend : Trie → Nat → Trie
  | .empty, _ => .empty
  | .terminal, _ => .empty
  | .branch children, index => (lookup index children).getD .empty

/-- The structural empty test used to discard suspended constraints. -/
def isEmpty : Trie → Bool
  | .empty => true
  | _ => false

/-- The structural terminal test used to discharge suspended constraints. -/
def isTerminal : Trie → Bool
  | .terminal => true
  | _ => false

/-- Child maps have distinct indices, no empty values, and valid descendants. -/
def Valid : Trie → Prop
  | .empty => True
  | .terminal => True
  | .branch children => children ≠ [] ∧ (children.map Prod.fst).Nodup ∧
      ∀ index child, (index, child) ∈ children → child ≠ .empty ∧ Valid child
termination_by trie => sizeOf trie
decreasing_by
  rename_i member
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec] at smaller
  simp only [Trie.branch.sizeOf_spec]
  omega

/-- Two listed paths cannot be equal or extend each other. -/
def Supported (paths : List Path) : Prop :=
  paths.Pairwise (fun left right => ¬ left.IsPrefix right ∧ ¬ right.IsPrefix left)

/-- Membership in a branch is exactly membership in one prefixed child. -/
theorem mem_fromChildren (children : List (Nat × Trie)) (path : Path) :
    path ∈ fromChildren children ↔
      ∃ index child suffix, (index, child) ∈ children ∧ suffix ∈ fromPathTrie child ∧ path = index :: suffix := by
  induction children with
  | nil => simp [fromChildren]
  | cons pair rest ih =>
      obtain ⟨index, child⟩ := pair
      simp only [fromChildren, List.mem_append, List.mem_map, ih, List.mem_cons]
      constructor
      · rintro (⟨suffix, member, rfl⟩ | ⟨key, node, suffix, member, present, rfl⟩)
        · exact ⟨index, child, suffix, Or.inl rfl, member, rfl⟩
        · exact ⟨key, node, suffix, Or.inr member, present, rfl⟩
      · rintro ⟨key, node, suffix, (same | member), present, rfl⟩
        · cases same
          exact Or.inl ⟨suffix, present, rfl⟩
        · exact Or.inr ⟨key, node, suffix, member, present, rfl⟩

/-- Empty paths occur only at a terminal. -/
theorem nil_mem (trie : Trie) : [] ∈ fromPathTrie trie ↔ trie = .terminal := by
  cases trie with
  | empty => simp [fromPathTrie]
  | terminal => simp [fromPathTrie]
  | branch children => simp [fromPathTrie, mem_fromChildren]

/-- Successful map lookup finds an actual child entry. -/
theorem lookup_mem (index : Nat) (children : List (Nat × Trie)) (child : Trie)
    (found : lookup index children = some child) : (index, child) ∈ children := by
  induction children with
  | nil => simp [lookup] at found
  | cons pair rest ih =>
      obtain ⟨key, node⟩ := pair
      by_cases same : index = key
      · simp [lookup, same] at found
        subst key
        subst node
        simp
      · simp [lookup, same] at found
        exact List.mem_cons_of_mem _ (ih found)

/-- Distinct child keys make lookup complete. -/
theorem lookup_of_mem (index : Nat) (children : List (Nat × Trie)) (child : Trie)
    (unique : (children.map Prod.fst).Nodup) (member : (index, child) ∈ children) :
    lookup index children = some child := by
  induction children with
  | nil => simp at member
  | cons pair rest ih =>
      obtain ⟨key, node⟩ := pair
      have unique' := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | member
      · cases same
        simp [lookup]
      · have different : index ≠ key := by
          intro same
          subst index
          exact unique'.1 (List.mem_map.mpr ⟨(key, child), member, rfl⟩)
        simpa [lookup, different] using ih unique'.2 member

/-- Descent preserves exactly the paths that start with the selected child. -/
theorem descend_exact (trie : Trie) (valid : Valid trie) (index : Nat) (suffix : Path) :
    suffix ∈ fromPathTrie (pathTrieDescend trie index) ↔ index :: suffix ∈ fromPathTrie trie := by
  cases trie with
  | empty => simp [pathTrieDescend, fromPathTrie]
  | terminal => simp [pathTrieDescend, fromPathTrie]
  | branch children =>
      rw [Valid] at valid
      rcases valid with ⟨_, unique, _⟩
      constructor
      · intro member
        cases found : lookup index children with
        | none => simp [pathTrieDescend, found, fromPathTrie] at member
        | some child =>
            have present : suffix ∈ fromPathTrie child := by simpa [pathTrieDescend, found] using member
            exact (mem_fromChildren children _).mpr ⟨index, child, suffix, lookup_mem _ _ _ found, present, rfl⟩
      · intro member
        obtain ⟨key, child, rest, entry, present, same⟩ := (mem_fromChildren children _).mp member
        cases same
        simp [pathTrieDescend, lookup_of_mem _ _ _ unique entry, present]


/-- Remove one selected first index and omit every other path. -/
def suffixOf (index : Nat) : Path → Option Path
  | [] => none
  | key :: suffix => if key = index then some suffix else none

/-- One constructor group, in the original path order. -/
def tailsAt (index : Nat) (paths : List Path) : List Path := paths.filterMap (suffixOf index)

/-- Distinct child indices present in the input. -/
def childKeys (paths : List Path) : List Nat :=
  (paths.filterMap List.head?).eraseDups.mergeSort (fun left right => left ≤ right)

/-- A group contains exactly the suffixes selected by its first index. -/
theorem mem_tailsAt (index : Nat) (paths : List Path) (suffix : Path) :
    suffix ∈ tailsAt index paths ↔ index :: suffix ∈ paths := by
  simp only [tailsAt, List.mem_filterMap]
  constructor
  · rintro ⟨path, member, selected⟩
    cases path with
    | nil => simp [suffixOf] at selected
    | cons key rest =>
        by_cases same : key = index
        · simp [suffixOf, same] at selected
          subst key
          subst rest
          exact member
        · simp [suffixOf, same] at selected
  · intro member
    exact ⟨index :: suffix, member, by simp [suffixOf]⟩

/-- The constructor creates exactly the requested first indices. -/
theorem mem_childKeys (index : Nat) (paths : List Path) :
    index ∈ childKeys paths ↔ ∃ suffix, index :: suffix ∈ paths := by
  simp only [childKeys, List.mem_mergeSort, List.mem_eraseDups, List.mem_filterMap]
  constructor
  · rintro ⟨path, member, selected⟩
    cases path with
    | nil => simp at selected
    | cons key rest => simp at selected; subst key; exact ⟨rest, member⟩
  · rintro ⟨suffix, member⟩
    exact ⟨index :: suffix, member, rfl⟩

/-- Removing a common first index preserves the supported-input condition. -/
theorem tailsAt_supported (index : Nat) (paths : List Path) (supported : Supported paths) :
    Supported (tailsAt index paths) := by
  apply supported.filterMap (suffixOf index)
  intro left right separate suffix selected rest chosen
  cases left with
  | nil => simp [suffixOf] at selected
  | cons key tail =>
      by_cases same : key = index
      · simp [suffixOf, same] at selected
        subst key
        subst tail
        cases right with
        | nil => simp [suffixOf] at chosen
        | cons key tail =>
            by_cases same : key = index
            · simp [suffixOf, same] at chosen
              subst key
              subst tail
              simpa using separate
            · simp [suffixOf, same] at chosen
      · simp [suffixOf, same] at selected

/-- A supported list containing the empty path contains only that path. -/
theorem supported_nil (paths : List Path) (supported : Supported paths) (member : [] ∈ paths) :
    paths = [[]] := by
  induction paths with
  | nil => simp at member
  | cons path rest ih =>
      obtain ⟨separate, recursive⟩ := List.pairwise_cons.mp supported
      rcases List.mem_cons.mp member with same | member
      · subst path
        cases rest with
        | nil => rfl
        | cons first tail => exact False.elim ((separate first (by simp)).1 (by simp))
      · exact False.elim ((separate [] member).2 (by simp))

/-- Build one finite child map after recursive construction of its groups. -/
def makeChildren (recur : List Path → Option Trie) (paths : List Path) : List Nat → Option (List (Nat × Trie))
  | [] => some []
  | index :: rest => do
      let child ← recur (tailsAt index paths)
      let children ← makeChildren recur paths rest
      pure ((index, child) :: children)

/-- Successful recursive groups give a successful child map with exactly those keys. -/
theorem makeChildren_spec (recur : List Path → Option Trie) (paths : List Path) (keys : List Nat)
    (property : Nat → Trie → Prop)
    (recursive : ∀ index ∈ keys, ∃ child, recur (tailsAt index paths) = some child ∧ property index child) :
    ∃ children, makeChildren recur paths keys = some children ∧ children.map Prod.fst = keys ∧
      ∀ index child, (index, child) ∈ children → property index child := by
  induction keys with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons index rest ih =>
      obtain ⟨child, built, correct⟩ := recursive index (by simp)
      obtain ⟨children, tailBuilt, keys, each⟩ := ih (fun i hi => recursive i (by simp [hi]))
      refine ⟨(index, child) :: children, by simp [makeChildren, built, tailBuilt], by simp [keys], ?_⟩
      intro i node member
      rcases List.mem_cons.mp member with same | member
      · cases same; exact correct
      · exact each i node member

/-- Group paths recursively. The budget bounds path depth, not the graph. -/
def build : Nat → List Path → Option Trie
  | 0, [] => some .empty
  | 0, _ :: _ => none
  | _ + 1, [] => some .empty
  | _ + 1, [[]] => some .terminal
  | fuel + 1, paths =>
      if [] ∈ paths then none
      else (makeChildren (build fuel) paths (childKeys paths)).map Trie.branch

/-- Duplicate elimination produces distinct finite map keys. -/
theorem eraseDups_nodup (keys : List Nat) : keys.eraseDups.Nodup := by
  cases keys with
  | nil => simp
  | cons key rest =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, eraseDups_nodup (rest.filter (fun index => !index == key))⟩
      simp [List.mem_eraseDups]
termination_by keys.length
decreasing_by
  have smaller := List.length_filter_le (fun index => !index == key) rest
  simp only [List.length_cons]
  omega

/-- Every supported finite path list has an exact valid trie when the budget is adequate. -/
theorem build_supported (fuel : Nat) (paths : List Path) (supported : Supported paths)
    (budget : ∀ path ∈ paths, path.length < fuel) :
    ∃ trie, build fuel paths = some trie ∧ Valid trie ∧
      (∀ path, path ∈ fromPathTrie trie ↔ path ∈ paths) ∧ (trie = .empty ↔ paths = []) := by
  induction fuel generalizing paths with
  | zero =>
      have empty : paths = [] := by
        cases paths with
        | nil => rfl
        | cons path rest => have := budget path (by simp); omega
      subst paths
      exact ⟨.empty, rfl, by simp [Valid], by simp [fromPathTrie], by simp⟩
  | succ fuel ih =>
      by_cases empty : paths = []
      · subst paths
        exact ⟨.empty, rfl, by simp [Valid], by simp [fromPathTrie], by simp⟩
      by_cases terminal : paths = [[]]
      · subst paths
        exact ⟨.terminal, rfl, by simp [Valid], by simp [fromPathTrie], by simp⟩
      have absent : [] ∉ paths := fun member => terminal (supported_nil paths supported member)
      have recursive : ∀ index ∈ childKeys paths, ∃ child,
          build fuel (tailsAt index paths) = some child ∧
          (Valid child ∧ child ≠ .empty ∧ ∀ suffix, suffix ∈ fromPathTrie child ↔ index :: suffix ∈ paths) := by
        intro index member
        have shorter : ∀ suffix ∈ tailsAt index paths, suffix.length < fuel := by
          intro suffix present
          have := budget (index :: suffix) ((mem_tailsAt _ _ _).mp present)
          simp only [List.length_cons] at this
          omega
        obtain ⟨child, built, valid, exactPaths, emptyIff⟩ := ih (tailsAt index paths)
          (tailsAt_supported _ _ supported) shorter
        obtain ⟨suffix, present⟩ := (mem_childKeys _ _).mp member
        have childNonempty : child ≠ .empty := by
          intro equal
          have noPaths := emptyIff.mp equal
          have := (mem_tailsAt index paths suffix).mpr present
          simp [noPaths] at this
        exact ⟨child, built, valid, childNonempty, fun suffix => (exactPaths suffix).trans (mem_tailsAt _ _ _)⟩
      obtain ⟨children, built, keys, each⟩ := makeChildren_spec (build fuel) paths (childKeys paths) _ recursive
      have hasKey : childKeys paths ≠ [] := by
        cases paths with
        | nil => contradiction
        | cons path rest =>
            cases path with
            | nil => simp at absent
            | cons index suffix =>
                intro noKeys
                have present := (mem_childKeys index ((index :: suffix) :: rest)).mpr ⟨suffix, by simp⟩
                simp [noKeys] at present
      have childrenNonempty : children ≠ [] := by intro noChildren; simp [noChildren] at keys; exact hasKey keys
      refine ⟨.branch children, ?_, ?_, ?_, by simp [empty]⟩
      · cases paths with
        | nil => contradiction
        | cons path rest =>
            cases path with
            | nil => simp at absent
            | cons index suffix => simpa [build, absent] using congrArg (Option.map Trie.branch) built
      · rw [Valid]
        refine ⟨childrenNonempty, ?_, fun index child member => ⟨(each index child member).2.1, (each index child member).1⟩⟩
        rw [keys]
        exact (List.mergeSort_perm _ _).symm.nodup (eraseDups_nodup _)
      · intro path
        constructor
        · intro member
          obtain ⟨index, child, suffix, entry, present, rfl⟩ := (mem_fromChildren children path).mp member
          exact ((each index child entry).2.2 suffix).mp present
        · intro member
          cases path with
          | nil => exact False.elim (absent member)
          | cons index suffix =>
              have keyMember : index ∈ children.map Prod.fst := by
                rw [keys]
                exact (mem_childKeys _ _).mpr ⟨suffix, member⟩
              obtain ⟨⟨key, child⟩, entry, same⟩ := List.mem_map.mp keyMember
              change key = index at same
              subst key
              exact (mem_fromChildren children _).mpr ⟨index, child, suffix, entry,
                ((each index child entry).2.2 suffix).mpr member, rfl⟩


/-- Distinct child keys preserve distinct, prefix-free path lists. -/
theorem fromChildren_supported (children : List (Nat × Trie))
    (unique : (children.map Prod.fst).Nodup)
    (each : ∀ index child, (index, child) ∈ children → Supported (fromPathTrie child)) :
    Supported (fromChildren children) := by
  induction children with
  | nil => simp [fromChildren, Supported]
  | cons entry rest ih =>
      obtain ⟨index, child⟩ := entry
      obtain ⟨absent, uniqueRest⟩ := List.nodup_cons.mp unique
      rw [fromChildren, Supported, List.pairwise_append]
      refine ⟨?_, ih uniqueRest (fun i node member => each i node (by simp [member])), ?_⟩
      · simpa [List.pairwise_map, Supported] using each index child (by simp)
      · intro left leftMember right rightMember
        obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp leftMember
        obtain ⟨key, node, tail, member, _, rfl⟩ := (mem_fromChildren rest right).mp rightMember
        have different : key ≠ index := by
          intro same
          subst key
          exact absent (List.mem_map.mpr ⟨(index, node), member, rfl⟩)
        simp [different, Ne.symm different]

/-- Valid terminal-or-branch tries represent prefix-free distinct paths. -/
theorem fromPathTrie_supported (trie : Trie) (valid : Valid trie) : Supported (fromPathTrie trie) := by
  cases trie with
  | empty => simp [fromPathTrie, Supported]
  | terminal => simp [fromPathTrie, Supported]
  | branch children =>
      rw [Valid] at valid
      apply fromChildren_supported children valid.2.1
      intro index child member
      exact fromPathTrie_supported child (valid.2.2 index child member).2
termination_by sizeOf trie
decreasing_by
  have smaller := List.sizeOf_lt_of_mem member
  simp_all only [Prod.mk.sizeOf_spec, Trie.branch.sizeOf_spec]
  omega

/-- Every nonempty valid trie contains an actual represented path. -/
theorem valid_has_path (trie : Trie) (valid : Valid trie) (nonempty : trie ≠ .empty) :
    ∃ path, path ∈ fromPathTrie trie := by
  cases trie with
  | empty => contradiction
  | terminal => exact ⟨[], by simp [fromPathTrie]⟩
  | branch children =>
      rw [Valid] at valid
      obtain ⟨entry, member⟩ := List.exists_mem_of_ne_nil children valid.1
      obtain ⟨index, child⟩ := entry
      have childValid := valid.2.2 index child member
      obtain ⟨suffix, present⟩ := valid_has_path child childValid.2 childValid.1
      exact ⟨index :: suffix, (mem_fromChildren children _).mpr ⟨index, child, suffix, member, present, rfl⟩⟩
termination_by sizeOf trie
decreasing_by
  have smaller := List.sizeOf_lt_of_mem member
  simp_all only [Prod.mk.sizeOf_spec, Trie.branch.sizeOf_spec]
  omega

/-- The structural empty test is exact on constructor-valid tries. -/
theorem empty_exact (trie : Trie) (valid : Valid trie) :
    isEmpty trie = true ↔ fromPathTrie trie = [] := by
  cases trie with
  | empty => simp [isEmpty, fromPathTrie]
  | terminal => simp [isEmpty, fromPathTrie]
  | branch children =>
      obtain ⟨path, present⟩ := valid_has_path (.branch children) valid (by intro impossible; cases impossible)
      have nonempty : fromPathTrie (.branch children) ≠ [] := by intro same; simp [same] at present
      simp [isEmpty, nonempty]

/-- Descent also preserves the finite-map representation invariant. -/
theorem descend_valid (trie : Trie) (valid : Valid trie) (index : Nat) :
    Valid (pathTrieDescend trie index) := by
  cases trie with
  | empty => simp [pathTrieDescend, Valid]
  | terminal => simp [pathTrieDescend, Valid]
  | branch children =>
      cases found : lookup index children with
      | none => simp [pathTrieDescend, found, Valid]
      | some child =>
          rw [Valid] at valid
          simpa [pathTrieDescend, found] using (valid.2.2 index child (lookup_mem _ _ _ found)).2

/-- A finite bound computed directly from the input path lengths. -/
def pathBudget (paths : List Path) : Nat := 1 + (paths.map List.length).foldr Nat.max 0

/-- The computed constructor bound covers every input path. -/
theorem pathBudget_sufficient (paths : List Path) (path : Path) (member : path ∈ paths) :
    path.length < pathBudget paths := by
  have bound : ∀ value ∈ paths.map List.length, value ≤ (paths.map List.length).foldr Nat.max 0 := by
    generalize paths.map List.length = values
    intro value present
    induction values with
    | nil => simp at present
    | cons first rest ih =>
        rcases List.mem_cons.mp present with rfl | present
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih present) (Nat.le_max_right _ _)
  have := bound path.length (List.mem_map.mpr ⟨path, member, rfl⟩)
  unfold pathBudget
  omega

/-- The checked counterpart of `toPathTrie`. -/
def toPathTrie (paths : List Path) : Option Trie := build (pathBudget paths) paths

/-- Supported construction succeeds, and conversion back preserves exactly its paths. -/
theorem toPathTrie_correct (paths : List Path) (supported : Supported paths) :
    ∃ trie, toPathTrie paths = some trie ∧ Valid trie ∧ Supported (fromPathTrie trie) ∧
      ∀ path, path ∈ fromPathTrie trie ↔ path ∈ paths := by
  obtain ⟨trie, built, valid, same, _⟩ := build_supported (pathBudget paths) paths supported
    (pathBudget_sufficient paths)
  exact ⟨trie, built, valid, fromPathTrie_supported trie valid, same⟩

/-- Maximum of a finite set of child indices. -/
def maxIndex : List Nat → Option Nat
  | [] => none
  | index :: rest => some (match maxIndex rest with | none => index | some previous => max index previous)

/-- The largest stored child index, as in the Haskell `IntMap.lookupMax`. -/
def getMaxNonemptyIndex : Trie → Option Nat
  | .empty => none
  | .terminal => none
  | .branch children => maxIndex (children.map Prod.fst)

/-- Maximum-index checking is equivalent to checking every stored index. -/
theorem maxIndex_lt (indices : List Nat) (arity : Nat) :
    (maxIndex indices).all (· < arity) = true ↔ ∀ index ∈ indices, index < arity := by
  induction indices with
  | nil => simp [maxIndex]
  | cons index rest ih =>
      cases found : maxIndex rest with
      | none =>
          have all := ih
          simp [found] at all
          simp [maxIndex, found]
          exact fun _ => all
      | some largest =>
          simp [found] at ih
          simp [maxIndex, found, Nat.max_lt, ih]

/-- The maximum child test is exactly the root arity requirement of all represented paths. -/
theorem arity_exact (trie : Trie) (valid : Valid trie) (arity : Nat) :
    (getMaxNonemptyIndex trie).all (· < arity) = true ↔
      ∀ index suffix, index :: suffix ∈ fromPathTrie trie → index < arity := by
  cases trie with
  | empty => simp [getMaxNonemptyIndex, fromPathTrie]
  | terminal => simp [getMaxNonemptyIndex, fromPathTrie]
  | branch children =>
      rw [getMaxNonemptyIndex, maxIndex_lt]
      constructor
      · intro bound index suffix member
        obtain ⟨key, child, rest, entry, _, same⟩ := (mem_fromChildren children _).mp member
        cases same
        exact bound index (List.mem_map.mpr ⟨(index, child), entry, rfl⟩)
      · intro bound index member
        obtain ⟨⟨key, child⟩, entry, same⟩ := List.mem_map.mp member
        change key = index at same
        subst key
        rw [Valid] at valid
        have childValid := valid.2.2 index child entry
        obtain ⟨suffix, present⟩ := valid_has_path child childValid.2 childValid.1
        exact bound index suffix ((mem_fromChildren children _).mpr ⟨index, child, suffix, entry, present, rfl⟩)


/-- Strict subsumption means proper path-prefix containment. -/
def StrictPrefix (first second : Path) : Prop := first.IsPrefix second ∧ first ≠ second

mutual
  /-- The structural class-subsumption test from `hasSubsumingMember`. -/
  def hasSubsumingMember : Trie → Trie → Bool
    | .empty, _ => false
    | _, .empty => false
    | .terminal, .terminal => false
    | .terminal, .branch _ => true
    | .branch _, .terminal => false
    | .branch first, .branch second => subsumingChildren first second
  /-- Compare children only where the two finite maps share an index. -/
  def subsumingChildren : List (Nat × Trie) → List (Nat × Trie) → Bool
    | [], _ => false
    | (index, child) :: rest, second =>
        (match lookup index second with
          | none => false
          | some other => hasSubsumingMember child other) || subsumingChildren rest second
end

/-- Shared-index traversal finds exactly the successful child comparisons. -/
theorem subsumingChildren_true (first second : List (Nat × Trie)) :
    subsumingChildren first second = true ↔
      ∃ index child other, (index, child) ∈ first ∧ lookup index second = some other ∧
        hasSubsumingMember child other = true := by
  induction first with
  | nil => simp [subsumingChildren]
  | cons entry rest ih =>
      obtain ⟨index, child⟩ := entry
      simp only [subsumingChildren, Bool.or_eq_true, ih, List.mem_cons]
      constructor
      · rintro (success | ⟨key, node, other, member, found, success⟩)
        · cases found : lookup index second with
          | none => simp [found] at success
          | some other => exact ⟨index, child, other, Or.inl rfl, found, by simpa [found] using success⟩
        · exact ⟨key, node, other, Or.inr member, found, success⟩
      · rintro ⟨key, node, other, (same | member), found, success⟩
        · cases same
          exact Or.inl (by simpa [found] using success)
        · exact Or.inr ⟨key, node, other, member, found, success⟩

/-- Structural subsumption is exactly the existence of a strict prefix pair. -/
theorem hasSubsumingMember_exact (first second : Trie) (firstValid : Valid first) (secondValid : Valid second) :
    hasSubsumingMember first second = true ↔
      ∃ left, left ∈ fromPathTrie first ∧ ∃ right, right ∈ fromPathTrie second ∧ StrictPrefix left right := by
  cases first with
  | empty => simp [hasSubsumingMember, fromPathTrie]
  | terminal =>
      cases second with
      | empty => simp [hasSubsumingMember, fromPathTrie]
      | terminal => simp [hasSubsumingMember, fromPathTrie, StrictPrefix]
      | branch children =>
          obtain ⟨path, member⟩ := valid_has_path (.branch children) secondValid (by intro impossible; cases impossible)
          have notNil : path ≠ [] := by intro same; subst path; simp [nil_mem] at member
          constructor
          · intro _
            exact ⟨[], by simp [fromPathTrie], path, member, by simp [StrictPrefix, Ne.symm notNil]⟩
          · intro _; rfl
  | branch children =>
      cases second with
      | empty => simp [hasSubsumingMember, fromPathTrie]
      | terminal =>
          simp [hasSubsumingMember, fromPathTrie, StrictPrefix]
      | branch others =>
          rw [hasSubsumingMember, subsumingChildren_true]
          rw [Valid] at firstValid secondValid
          constructor
          · rintro ⟨index, child, other, member, found, success⟩
            have otherMember := lookup_mem index others other found
            obtain ⟨left, leftMember, right, rightMember, initial, different⟩ :=
              (hasSubsumingMember_exact child other (firstValid.2.2 index child member).2
                (secondValid.2.2 index other otherMember).2).mp success
            refine ⟨index :: left, (mem_fromChildren children _).mpr ⟨index, child, left, member, leftMember, rfl⟩,
              index :: right, (mem_fromChildren others _).mpr ⟨index, other, right, otherMember, rightMember, rfl⟩, ?_⟩
            simpa [StrictPrefix] using And.intro initial different
          · rintro ⟨left, leftMember, right, rightMember, initial, different⟩
            obtain ⟨index, child, suffix, member, present, rfl⟩ := (mem_fromChildren children left).mp leftMember
            obtain ⟨key, other, tail, otherMember, tailPresent, rfl⟩ := (mem_fromChildren others right).mp rightMember
            obtain ⟨same, suffixPrefix⟩ := List.cons_prefix_cons.mp initial
            subst key
            have shorter : suffix ≠ tail := by intro same; subst tail; exact different rfl
            refine ⟨index, child, other, member, lookup_of_mem _ _ _ secondValid.2.1 otherMember, ?_⟩
            exact (hasSubsumingMember_exact child other (firstValid.2.2 index child member).2
              (secondValid.2.2 index other otherMember).2).mpr ⟨suffix, present, tail, tailPresent, suffixPrefix, shorter⟩
termination_by sizeOf first
decreasing_by
  all_goals
    have smaller := List.sizeOf_lt_of_mem member
    simp_all only [Prod.mk.sizeOf_spec, Trie.branch.sizeOf_spec]
    omega

/-- One suspended equality obligation and its union-find variable. -/
structure Suspended (Variable : Type) where
  trie : Trie
  var : Variable

/-- Descend each obligation and remove exactly the structurally empty tries. -/
def descendScs (index : Nat) (constraints : List (Suspended Variable)) : List (Suspended Variable) :=
  (constraints.map (fun constraint => ⟨pathTrieDescend constraint.trie index, constraint.var⟩)).filter
    (fun constraint => !isEmpty constraint.trie)

/-- Suspended descent retains exactly the requested suffixes and their original variables. -/
theorem descendScs_exact (index : Nat) (constraints : List (Suspended Variable))
    (valid : ∀ constraint ∈ constraints, Valid constraint.trie) (var : Variable) (suffix : Path) :
    (∃ constraint ∈ descendScs index constraints,
      constraint.var = var ∧ suffix ∈ fromPathTrie constraint.trie) ↔
    ∃ constraint ∈ constraints,
      constraint.var = var ∧ index :: suffix ∈ fromPathTrie constraint.trie := by
  constructor
  · rintro ⟨constraint, member, same, present⟩
    obtain ⟨mapped, _⟩ := List.mem_filter.mp member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp mapped
    exact ⟨original, originalMember, same, (descend_exact original.trie (valid original originalMember) index suffix).mp present⟩
  · rintro ⟨original, member, same, present⟩
    have descended := (descend_exact original.trie (valid original member) index suffix).mpr present
    refine ⟨⟨pathTrieDescend original.trie index, original.var⟩, ?_, same, descended⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨original, member, rfl⟩, ?_⟩
    have notEmpty : isEmpty (pathTrieDescend original.trie index) ≠ true := by
      intro empty
      have noPaths := (empty_exact _ (descend_valid original.trie (valid original member) index)).mp empty
      simp [noPaths] at descended
    simpa using notEmpty


/-- Prefix-free distinctness implies ordinary list distinctness. -/
theorem supported_nodup (paths : List Path) (supported : Supported paths) : paths.Nodup := by
  apply supported.imp
  intro left right separate same
  subst right
  exact separate.1 (List.prefix_refl left)

/-- The round trip preserves path multiplicity as well as membership. -/
theorem toPathTrie_permutation (paths : List Path) (supported : Supported paths) :
    ∃ trie, toPathTrie paths = some trie ∧ Valid trie ∧ (fromPathTrie trie).Perm paths := by
  obtain ⟨trie, built, valid, outputSupported, same⟩ := toPathTrie_correct paths supported
  exact ⟨trie, built, valid, (List.perm_ext_iff_of_nodup
    (supported_nodup _ outputSupported) (supported_nodup _ supported)).mpr same⟩

/-- Successful child-map construction records every recursive call. -/
theorem makeChildren_success (recur : List Path → Option Trie) (paths : List Path)
    (keys : List Nat) (children : List (Nat × Trie)) (success : makeChildren recur paths keys = some children) :
    children.map Prod.fst = keys ∧
      ∀ index child, (index, child) ∈ children → recur (tailsAt index paths) = some child := by
  induction keys generalizing children with
  | nil => simp [makeChildren] at success; subst children; simp
  | cons index rest ih =>
      cases built : recur (tailsAt index paths) with
      | none => simp [makeChildren, built] at success
      | some child =>
          cases tailBuilt : makeChildren recur paths rest with
          | none => simp [makeChildren, built, tailBuilt] at success
          | some remaining =>
              have same : children = (index, child) :: remaining := by
                simpa [makeChildren, built, tailBuilt] using success.symm
              subst children
              obtain ⟨sameKeys, each⟩ := ih remaining tailBuilt
              refine ⟨by simp [sameKeys], ?_⟩
              intro key node member
              rcases List.mem_cons.mp member with equal | member
              · cases equal; exact built
              · exact each key node member

/-- If every first-index group is supported, the nonempty input paths are supported. -/
theorem supported_of_tails (paths : List Path) (nonempty : [] ∉ paths)
    (each : ∀ index ∈ childKeys paths, Supported (tailsAt index paths)) : Supported paths := by
  apply List.pairwise_of_forall_sublist
  intro left right ordered
  have leftMember : left ∈ paths := ordered.subset (by simp)
  have rightMember : right ∈ paths := ordered.subset (by simp)
  cases left with
  | nil => exact False.elim (nonempty leftMember)
  | cons index suffix =>
      cases right with
      | nil => exact False.elim (nonempty rightMember)
      | cons key tail =>
          by_cases same : key = index
          · subst key
            have shortPair := ordered.filterMap (suffixOf index)
            have shortOrdered : [suffix, tail].Sublist (tailsAt index paths) := by
              simpa [suffixOf, tailsAt] using shortPair
            have separate := (each index ((mem_childKeys _ _).mpr ⟨suffix, leftMember⟩)).forall_sublist shortOrdered
            simpa using separate
          · simp [same, Ne.symm same]

/-- Successful construction cannot hide duplicate paths or prefix conflicts. -/
theorem build_requires_supported (fuel : Nat) (paths : List Path) (trie : Trie)
    (success : build fuel paths = some trie) : Supported paths := by
  induction fuel generalizing paths trie with
  | zero =>
      cases paths with
      | nil => simp [Supported]
      | cons path rest => simp [build] at success
  | succ fuel ih =>
      cases paths with
      | nil => simp [Supported]
      | cons path rest =>
          cases path with
          | nil =>
              cases rest with
              | nil => simp [Supported]
              | cons path rest => simp [build] at success
          | cons index suffix =>
              by_cases terminal : [] ∈ (index :: suffix) :: rest
              · simp [build, terminal] at success
              · cases made : makeChildren (build fuel) ((index :: suffix) :: rest) (childKeys ((index :: suffix) :: rest)) with
                | none => simp [build, terminal, made] at success
                | some children =>
                    obtain ⟨keys, each⟩ := makeChildren_success (build fuel) _ _ children made
                    apply supported_of_tails _ terminal
                    intro key member
                    rw [← keys] at member
                    obtain ⟨⟨i, child⟩, entry, same⟩ := List.mem_map.mp member
                    change i = key at same
                    subst i
                    exact ih _ child (each key child entry)

/-- The checked constructor succeeds exactly for distinct prefix-free input paths. -/
theorem toPathTrie_succeeds_iff (paths : List Path) :
    (∃ trie, toPathTrie paths = some trie) ↔ Supported paths := by
  constructor
  · rintro ⟨trie, built⟩
    exact build_requires_supported (pathBudget paths) paths trie built
  · intro supported
    obtain ⟨trie, built, _⟩ := toPathTrie_correct paths supported
    exact ⟨trie, built⟩


/-- Child maps enumerate indices in strictly increasing order. -/
def Ascending : Trie → Prop
  | .empty => True
  | .terminal => True
  | .branch children => (children.map Prod.fst).Pairwise (· < ·) ∧
      ∀ index child, (index, child) ∈ children → Ascending child
termination_by trie => sizeOf trie
decreasing_by
  rename_i member
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec] at smaller
  simp only [Trie.branch.sizeOf_spec]
  omega

/-- The constructor's finite-map keys are strictly increasing. -/
theorem childKeys_increasing (paths : List Path) : (childKeys paths).Pairwise (· < ·) := by
  have ordered : (childKeys paths).Pairwise (· ≤ ·) := by
    have sorted := List.pairwise_mergeSort (le := fun left right : Nat => decide (left ≤ right))
      (by intro left middle right first second; simp only [decide_eq_true_eq] at *; omega)
      (by intro left right; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (paths.filterMap List.head?).eraseDups
    simpa [childKeys] using sorted
  have unique : (childKeys paths).Nodup :=
    (List.mergeSort_perm _ _).symm.nodup (eraseDups_nodup _)
  exact ordered.imp₂ (fun left right bound different => by omega) unique

/-- Every successful constructor result uses ascending maps at every level. -/
theorem build_ascending (fuel : Nat) (paths : List Path) (trie : Trie)
    (success : build fuel paths = some trie) : Ascending trie := by
  induction fuel generalizing paths trie with
  | zero =>
      cases paths with
      | nil => simp [build] at success; subst trie; simp [Ascending]
      | cons path rest => simp [build] at success
  | succ fuel ih =>
      cases paths with
      | nil => simp [build] at success; subst trie; simp [Ascending]
      | cons path rest =>
          cases path with
          | nil =>
              cases rest with
              | nil => simp [build] at success; subst trie; simp [Ascending]
              | cons path rest => simp [build] at success
          | cons index suffix =>
              by_cases terminal : [] ∈ (index :: suffix) :: rest
              · simp [build, terminal] at success
              · cases made : makeChildren (build fuel) ((index :: suffix) :: rest) (childKeys ((index :: suffix) :: rest)) with
                | none => simp [build, terminal, made] at success
                | some children =>
                    have same : trie = .branch children := by simpa [build, terminal, made] using success.symm
                    subst trie
                    obtain ⟨keys, each⟩ := makeChildren_success (build fuel) _ _ children made
                    rw [Ascending]
                    refine ⟨?_, fun key child member => ih _ child (each key child member)⟩
                    rw [keys]
                    exact childKeys_increasing _

/-- Ascending child indices and child paths produce ascending prefixed paths. -/
theorem fromChildren_increasing (children : List (Nat × Trie))
    (ordered : (children.map Prod.fst).Pairwise (· < ·))
    (each : ∀ index child, (index, child) ∈ children → (fromPathTrie child).Pairwise (List.Lex (· < ·))) :
    (fromChildren children).Pairwise (List.Lex (· < ·)) := by
  induction children with
  | nil => simp [fromChildren]
  | cons entry rest ih =>
      obtain ⟨index, child⟩ := entry
      obtain ⟨before, remaining⟩ := List.pairwise_cons.mp ordered
      rw [fromChildren, List.pairwise_append]
      refine ⟨?_, ih remaining (fun key node member => each key node (by simp [member])), ?_⟩
      · exact (each index child (by simp)).map (index :: ·) (fun _ _ smaller => List.Lex.cons smaller)
      · intro left leftMember right rightMember
        obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp leftMember
        obtain ⟨key, node, tail, member, _, rfl⟩ := (mem_fromChildren rest right).mp rightMember
        exact List.Lex.rel (before key (List.mem_map.mpr ⟨(key, node), member, rfl⟩))

/-- Conversion of ascending maps produces strictly sorted paths. -/
theorem fromPathTrie_increasing (trie : Trie) (ordered : Ascending trie) :
    (fromPathTrie trie).Pairwise (List.Lex (· < ·)) := by
  cases trie with
  | empty => simp [fromPathTrie]
  | terminal => simp [fromPathTrie]
  | branch children =>
      rw [Ascending] at ordered
      exact fromChildren_increasing children ordered.1 (fun index child member =>
        fromPathTrie_increasing child (ordered.2 index child member))
termination_by sizeOf trie
decreasing_by
  have smaller := List.sizeOf_lt_of_mem member
  simp_all only [Prod.mk.sizeOf_spec, Trie.branch.sizeOf_spec]
  omega

/-- Constructor output satisfies both preconditions of `Set.fromDistinctAscList`. -/
theorem toPathTrie_sorted_distinct (paths : List Path) (supported : Supported paths) :
    ∃ trie, toPathTrie paths = some trie ∧ Valid trie ∧
      (fromPathTrie trie).Nodup ∧ (fromPathTrie trie).Pairwise (List.Lex (· < ·)) ∧
      (fromPathTrie trie).Perm paths := by
  obtain ⟨trie, built, valid, perm⟩ := toPathTrie_permutation paths supported
  exact ⟨trie, built, valid, supported_nodup _ (fromPathTrie_supported trie valid),
    fromPathTrie_increasing trie (build_ascending _ _ _ built), perm⟩

/-- Descending a sorted child map preserves sorted maps below it. -/
theorem descend_ascending (trie : Trie) (ordered : Ascending trie) (index : Nat) :
    Ascending (pathTrieDescend trie index) := by
  cases trie with
  | empty => simp [pathTrieDescend, Ascending]
  | terminal => simp [pathTrieDescend, Ascending]
  | branch children =>
      rw [Ascending] at ordered
      cases found : lookup index children with
      | none => simp [pathTrieDescend, found, Ascending]
      | some child => simpa [pathTrieDescend, found] using ordered.2 index child (lookup_mem _ _ _ found)


/-- A uniform first index produces exactly one finite-map key. -/
theorem childKeys_uniform (paths : List Path) (index : Nat) (nonempty : paths ≠ [])
    (sameHead : ∀ path ∈ paths, path.head? = some index) : childKeys paths = [index] := by
  have unique : (childKeys paths).Nodup :=
    (List.mergeSort_perm _ _).symm.nodup (eraseDups_nodup _)
  have sameMembers : ∀ key, key ∈ childKeys paths ↔ key ∈ [index] := by
    intro key
    constructor
    · intro member
      obtain ⟨suffix, present⟩ := (mem_childKeys _ _).mp member
      have equal := sameHead (key :: suffix) present
      simpa using equal
    · intro member
      have equal : key = index := by simpa using member
      subst key
      obtain ⟨path, present⟩ := List.exists_mem_of_ne_nil paths nonempty
      cases path with
      | nil => have impossible := sameHead [] present; simp at impossible
      | cons key suffix =>
          have equal : key = index := by simpa using sameHead (key :: suffix) present
          subst key
          exact (mem_childKeys _ _).mpr ⟨suffix, present⟩
  have perm := (List.perm_ext_iff_of_nodup unique (by simp : [index].Nodup)).mpr sameMembers
  simpa using perm

/-- Uniform-head filtering is the source fast path's ordinary tail map. -/
theorem tailsAt_uniform (paths : List Path) (index : Nat)
    (sameHead : ∀ path ∈ paths, path.head? = some index) :
    tailsAt index paths = paths.map List.tail := by
  induction paths with
  | nil => rfl
  | cons path rest ih =>
      have equal := sameHead path (by simp)
      cases path with
      | nil => simp at equal
      | cons key suffix =>
          have same : key = index := by simpa using equal
          subst key
          have remaining := ih (fun path member => sameHead path (by simp [member]))
          change List.filterMap (suffixOf index) rest = List.map List.tail rest at remaining
          simp [tailsAt, suffixOf, remaining]

/-- The single-child optimization is equal to the general grouped constructor. -/
theorem build_uniform_fast_path (fuel : Nat) (paths : List Path) (index : Nat) (nonempty : paths ≠ [])
    (sameHead : ∀ path ∈ paths, path.head? = some index) :
    build (fuel + 1) paths = (build fuel (paths.map List.tail)).map (fun child => .branch [(index, child)]) := by
  have absent : [] ∉ paths := by intro member; have impossible := sameHead [] member; simp at impossible
  have keys := childKeys_uniform paths index nonempty sameHead
  have tails := tailsAt_uniform paths index sameHead
  cases paths with
  | nil => contradiction
  | cons path rest =>
      cases path with
      | nil => simp at absent
      | cons key suffix =>
          simp only [build, ite_eq_right absent, keys, makeChildren, tails]
          cases build fuel (((key :: suffix) :: rest).map List.tail) <;> rfl

end MicroCFTA.EqualityTrie
