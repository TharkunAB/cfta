import MicroCFTA.SourceEqualityNeededMap

/-!
# The source required-path trie

`Needed` differs from an equality-class trie. It permits both a path and
extensions of that path. Empty paths impose no additional requirement.
Construction copies the source right fold and child-map alter operation.
Signed child keys retain the exported raw path domain.
-/
namespace MicroCFTA.SourceEqualityNeeded
open SourceEqualityNeededMap

abbrev Path := List Int

/-- An empty child map ends a required path. -/
inductive Needed where
  | node (children : List (Int × Needed))
  deriving Repr

/-- No child position is required. -/
def empty : Needed := .node []

/-- Insert one source path, retaining any existing deeper requirements. -/
def insert : Path → Needed → Needed
  | [], needed => needed
  | index :: rest, .node children =>
      .node (alter index (fun previous => insert rest (previous.getD empty)) children)

/-- The source folds the path set from the right. -/
def build (paths : List Path) : Needed := paths.foldr insert empty

/-- Every child map is ascending, and every stored descendant is valid. -/
def Valid : Needed → Prop
  | .node children => Ascending children ∧ ∀ index child, (index, child) ∈ children → Valid child
termination_by needed => sizeOf needed
decreasing_by
  have smaller := List.sizeOf_lt_of_mem ‹(index, child) ∈ children›
  simp only [Prod.mk.sizeOf_spec, Needed.node.sizeOf_spec] at *
  omega

/-- Query a required path, including prefixes that have an existing trie node. -/
def demands : Needed → Path → Bool
  | _, [] => true
  | .node children, index :: rest =>
      match lookup index children with
      | none => false
      | some child => demands child rest

/-- Empty maps require only the already existing root. -/
theorem demands_empty (path : Path) : demands empty path = true ↔ path = [] := by
  cases path <;> simp [demands, empty, lookup]

/-- The empty map has no invalid child entry. -/
theorem empty_valid : Valid empty := by simp [Valid, empty, Ascending]

/-- Each source insertion preserves finite child-map validity. -/
theorem insert_valid (path : Path) (needed : Needed) (valid : Valid needed) : Valid (insert path needed) := by
  induction path generalizing needed with
  | nil => exact valid
  | cons index rest ih =>
      cases needed with
      | node children =>
          obtain ⟨ordered, descendants⟩ := (show Ascending children ∧ _ from (by simpa only [Valid] using valid))
          rw [insert, Valid]
          refine ⟨alter_ascending _ _ _ ordered, ?_⟩
          apply alter_all index _ children Valid descendants ?_ ordered
          apply ih
          cases found : lookup index children with
          | none => exact empty_valid
          | some child => exact descendants index child (lookup_mem _ _ _ found)

/-- The complete right fold always builds a valid source trie. -/
theorem build_valid (paths : List Path) : Valid (build paths) := by
  induction paths with
  | nil => exact empty_valid
  | cons path rest ih => exact insert_valid path (build rest) ih

/-- One insertion adds exactly the prefixes of its path. -/
theorem demands_insert (path : Path) (needed : Needed) (valid : Valid needed) (query : Path) :
    demands (insert path needed) query = true ↔ demands needed query = true ∨ query.IsPrefix path := by
  induction path generalizing needed query with
  | nil =>
      cases query <;> simp [insert, demands]
  | cons index rest ih =>
      cases query with
      | nil => simp [demands]
      | cons key suffix =>
          cases needed with
          | node children =>
              obtain ⟨ordered, descendants⟩ := (show Ascending children ∧ _ from (by simpa only [Valid] using valid))
              simp only [insert, demands, lookup_alter index key _ children ordered]
              by_cases same : key = index
              · subst key
                simp only [ite_true]
                cases found : lookup index children with
                | none =>
                    have added := ih empty empty_valid suffix
                    simp only [Option.getD_none, demands_empty] at added ⊢
                    rw [added]
                    cases suffix <;> simp
                | some child =>
                    have childValid := descendants index child (lookup_mem _ _ _ found)
                    simpa only [Option.getD_some, List.cons_prefix_cons, true_and] using ih child childValid suffix
              · simp [same]

/-- Construction retains exactly the prefix closure of all source paths. -/
theorem demands_build (paths : List Path) (query : Path) :
    demands (build paths) query = true ↔
      query = [] ∨ ∃ path ∈ paths, query.IsPrefix path := by
  induction paths with
  | nil => simp [build, demands_empty]
  | cons path rest ih =>
      change demands (insert path (build rest)) query = true ↔ _
      rw [demands_insert path (build rest) (build_valid rest), ih]
      simp only [List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((root | previous) | added)
        · exact Or.inl root
        · exact Or.inr (Or.inr previous)
        · exact Or.inr (Or.inl added)
      · rintro (root | added | previous)
        · exact Or.inl (Or.inl root)
        · exact Or.inr added
        · exact Or.inl (Or.inr previous)

/-- The largest signed key models `IntMap.findMax` without a partial empty case. -/
def maxIndex : List Int → Option Int
  | [] => none
  | index :: rest => some (match maxIndex rest with | none => index | some largest => max index largest)

/-- Empty maps return the original node before any arity or recursive-node test. -/
def fits (needed : Needed) (arity : Nat) : Bool :=
  match needed with
  | .node children => (maxIndex (children.map Prod.fst)).all (fun index => index < (arity : Int))

/-- The source greatest-key comparison checks all stored signed child keys. -/
theorem maxIndex_lt (indices : List Int) (arity : Int) :
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
          simp [maxIndex, found, Int.max_lt, ih]

/-- A stored child entry is exactly a demanded one-step path. -/
theorem child_demand (children : List (Int × Needed)) (ordered : Ascending children) (index : Int) :
    demands (.node children) [index] = true ↔ ∃ child, (index, child) ∈ children := by
  simp only [demands]
  constructor
  · intro required
    cases found : lookup index children with
    | none => simp [found] at required
    | some child => exact ⟨child, lookup_mem _ _ _ found⟩
  · rintro ⟨child, member⟩
    rw [lookup_of_mem _ _ _ ordered member]

/-- The row filter tests every demanded first index, including raw negative keys. -/
theorem fits_exact (needed : Needed) (valid : Valid needed) (arity : Nat) :
    fits needed arity = true ↔ ∀ index, demands needed [index] = true → index < (arity : Int) := by
  cases needed with
  | node children =>
      have ordered : Ascending children := (show Ascending children ∧ _ from (by simpa only [Valid] using valid)).1
      rw [fits, maxIndex_lt]
      constructor
      · intro bounds index required
        obtain ⟨child, member⟩ := (child_demand children ordered index).mp required
        exact bounds index (List.mem_map.mpr ⟨(index, child), member, rfl⟩)
      · intro bounds index member
        obtain ⟨⟨key, child⟩, present, same⟩ := List.mem_map.mp member
        change key = index at same
        subst key
        exact bounds index ((child_demand children ordered index).mpr ⟨child, present⟩)

/-- For normalized nonnegative paths this is the usual first-child arity check. -/
theorem fits_build (paths : List Path) (arity : Nat) :
    fits (build paths) arity = true ↔
      ∀ index suffix, index :: suffix ∈ paths → index < (arity : Int) := by
  rw [fits_exact (build paths) (build_valid paths)]
  constructor
  · intro bounds index suffix member
    apply bounds index
    apply (demands_build paths [index]).mpr
    exact Or.inr ⟨index :: suffix, member, ⟨suffix, rfl⟩⟩
  · intro bounds index required
    rcases (demands_build paths [index]).mp required with impossible | ⟨path, member, initial⟩
    · cases impossible
    · obtain ⟨suffix, rfl⟩ := initial
      exact bounds index suffix (by simpa using member)

/-- A raw negative key passes the source row test even at zero arity. -/
theorem negative_key_boundary : fits (build [[-1]]) 0 = true := by rfl

end MicroCFTA.SourceEqualityNeeded
