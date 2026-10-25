import Std

/-!
# Persistent union-find

The forest operations follow `Internal/UnionFind.hs`. Missing entries denote
singleton roots of size one. A finite execution bound exposes termination;
it does not change a successful lookup. The specification uses finite parent
paths, independently of the executable lookup and compression code.
-/

namespace MicroCFTA.UnionFind

/-- A parent pointer or root with its stored size. -/
inductive Entry where
  | parent (uv : Nat)
  | root (size : Nat)
deriving DecidableEq, Repr

/-- A persistent finite-map interface. Missing variables are allowed. -/
abbrev Forest := Nat → Option Entry

/-- A missing variable denotes a singleton root. -/
def read (forest : Forest) (uv : Nat) : Entry :=
  (forest uv).getD (.root 1)

/-- Replace one entry and retain every other entry. -/
def put (forest : Forest) (uv : Nat) (entry : Entry) : Forest :=
  fun other => if other = uv then some entry else forest other

@[simp] theorem read_put_same (forest : Forest) (uv : Nat) (entry : Entry) :
    read (put forest uv entry) uv = entry := by simp [read, put]

@[simp] theorem read_put_other (forest : Forest) (uv other : Nat) (entry : Entry)
    (different : other ≠ uv) : read (put forest uv entry) other = read forest other := by
  simp [read, put, different]

/-- A finite parent path ends at a root and returns its stored size. -/
inductive Reaches (forest : Forest) : Nat → Nat → Nat → Prop where
  | root (lookup : read forest uv = .root size) : Reaches forest uv uv size
  | parent (lookup : read forest uv = .parent next)
      (tail : Reaches forest next representative size) : Reaches forest uv representative size

/-- A path's final variable is a root. -/
theorem reaches_terminal (path : Reaches forest uv representative size) :
    read forest representative = .root size := by
  induction path with
  | root lookup => exact lookup
  | parent _ _ ih => exact ih

/-- A finite parent path has a unique representative and stored size. -/
theorem reaches_unique (left : Reaches forest uv root₁ size₁)
    (right : Reaches forest uv root₂ size₂) : root₁ = root₂ ∧ size₁ = size₂ := by
  induction left generalizing root₂ size₂ with
  | root lookup =>
    cases right with
    | root other => simp_all
    | parent other tail => simp_all
  | parent lookup tail ih =>
    cases right with
    | root other => simp_all
    | parent other rest =>
      have same : _ := lookup.symm.trans other
      cases same
      exact ih rest

/-- Identical effective entries give identical finite paths. -/
theorem reaches_congr (same : ∀ uv, read left uv = read right uv)
    (path : Reaches left uv representative size) : Reaches right uv representative size := by
  induction path with
  | root lookup => exact .root (by rw [← same]; exact lookup)
  | parent lookup tail ih => exact .parent (by rw [← same]; exact lookup) ih

/-- A root can be stored explicitly without changing the effective forest. -/
theorem insert_missing (missing : forest uv = none) :
    ∀ other, read (put forest uv (.root 1)) other = read forest other := by
  intro other
  by_cases same : other = uv
  · subst other; simp [read, put, missing]
  · simp [read, put, same]

/-- Compress one nontrivial path to its existing representative. -/
theorem compress_preserves (path : Reaches forest uv representative size)
    (different : uv ≠ representative) :
    ∀ {other root count}, Reaches forest other root count →
      Reaches (put forest uv (.parent representative)) other root count := by
  have representativeUnchanged : Reaches (put forest uv (.parent representative)) representative representative size :=
    .root (by rw [read_put_other _ _ _ _ (Ne.symm different)]; exact reaches_terminal path)
  have compressed : Reaches (put forest uv (.parent representative)) uv representative size :=
    .parent (read_put_same ..) representativeUnchanged
  intro other root count original
  induction original with
  | @root other count lookup =>
    by_cases same : other = uv
    · subst other
      obtain ⟨hr, hs⟩ := reaches_unique path (.root lookup)
      exact False.elim (different hr.symm)
    · exact .root (by rw [read_put_other _ _ _ _ same]; exact lookup)
  | @parent other next root count lookup tail ih =>
    by_cases same : other = uv
    · subst other
      obtain ⟨hr, hs⟩ := reaches_unique path (.parent lookup tail)
      simpa only [hr, hs] using compressed
    · exact .parent (by rw [read_put_other _ _ _ _ same]; exact lookup) ih

/-- The lookup result includes the persistent forest after compression. -/
structure Result where
  representative : Nat
  size : Nat
  forest : Forest

/-- Execute the Haskell lookup with an explicit finite recursion bound. -/
def findRoot : Nat → Forest → Nat → Option Result
  | 0, _, _ => none
  | fuel + 1, forest, uv =>
    match forest uv with
    | none => some ⟨uv, 1, put forest uv (.root 1)⟩
    | some (.root size) => some ⟨uv, size, forest⟩
    | some (.parent next) => do
      let found ← findRoot fuel forest next
      some {found with forest := put found.forest uv (.parent found.representative)}

/-- Every successful lookup follows an original path and preserves all original paths. -/
theorem findRoot_correct (fuel : Nat) (forest : Forest) (uv : Nat) (found : Result)
    (result : findRoot fuel forest uv = some found) :
    Reaches forest uv found.representative found.size ∧
      (∀ {other root count}, Reaches forest other root count → Reaches found.forest other root count) := by
  induction fuel generalizing forest uv found with
  | zero => simp [findRoot] at result
  | succ fuel ih =>
    cases lookup : forest uv with
    | none =>
      simp [findRoot, lookup] at result
      subst found
      refine ⟨.root (by simp [read, lookup]), ?_⟩
      intro other root count path
      exact reaches_congr (fun other => (insert_missing lookup other).symm) path
    | some entry =>
      cases entry with
      | root size =>
        simp [findRoot, lookup] at result
        subst found
        exact ⟨.root (by simp [read, lookup]), fun path => path⟩
      | parent next =>
        cases recursive : findRoot fuel forest next with
        | none => simp [findRoot, lookup, recursive] at result
        | some earlier =>
          simp [findRoot, lookup, recursive] at result
          subst found
          obtain ⟨tail, preserved⟩ := ih forest next earlier recursive
          have path : Reaches forest uv earlier.representative earlier.size :=
            .parent (by simp [read, lookup]) tail
          have different : uv ≠ earlier.representative := by
            intro same
            have terminal := reaches_terminal path
            simp [← same, read, lookup] at terminal
          exact ⟨path, fun original => compress_preserves (preserved path) different (preserved original)⟩

/-- Every finite parent path gives a successful bounded execution. -/
theorem findRoot_terminates (path : Reaches forest uv representative size) :
    ∃ fuel found, findRoot fuel forest uv = some found := by
  induction path with
  | @root uv size lookup =>
    cases actual : forest uv with
    | none => exact ⟨1, ⟨uv, 1, put forest uv (.root 1)⟩, by simp [findRoot, actual]⟩
    | some entry =>
      have same : entry = .root size := by simpa [read, actual] using lookup
      subst entry
      exact ⟨1, ⟨uv, size, forest⟩, by simp [findRoot, actual]⟩
  | @parent uv next representative size lookup tail ih =>
    obtain ⟨fuel, found, result⟩ := ih
    cases actual : forest uv with
    | none => simp [read, actual] at lookup
    | some entry =>
      have same : entry = .parent next := by simpa [read, actual] using lookup
      subst entry
      exact ⟨fuel + 1, {found with forest := put found.forest uv (.parent found.representative)},
        by simp [findRoot, actual, result]⟩

/-- Additional execution fuel does not change a successful result. -/
theorem findRoot_moreFuel (fuel extra : Nat) (forest : Forest) (uv : Nat) (found : Result)
    (result : findRoot fuel forest uv = some found) :
    findRoot (fuel + extra) forest uv = some found := by
  induction fuel generalizing forest uv found with
  | zero => simp [findRoot] at result
  | succ fuel ih =>
    rw [Nat.succ_add]
    cases lookup : forest uv with
    | none => simpa [findRoot, lookup] using result
    | some entry =>
      cases entry with
      | root size => simpa [findRoot, lookup] using result
      | parent next =>
        cases recursive : findRoot fuel forest next with
        | none => simp [findRoot, lookup, recursive] at result
        | some earlier =>
          have extended := ih forest next earlier recursive
          simpa [findRoot, lookup, extended, recursive] using result

/-- Every variable in a valid forest has a finite path to a root. -/
def Total (forest : Forest) : Prop := ∀ uv, ∃ representative size, Reaches forest uv representative size

/-- Successful lookup preserves termination of all later lookups. -/
theorem findRoot_total (valid : Total forest)
    (result : findRoot fuel forest uv = some found) : Total found.forest := by
  intro other
  obtain ⟨root, count, path⟩ := valid other
  exact ⟨root, count, (findRoot_correct _ _ _ _ result).2 path⟩

/-- A total forest admits no new root paths after a successful lookup. -/
theorem findRoot_reaches_iff (valid : Total forest)
    (result : findRoot fuel forest uv = some found) (other root count : Nat) :
    Reaches found.forest other root count ↔ Reaches forest other root count := by
  have preserves : ∀ {a r n}, Reaches forest a r n → Reaches found.forest a r n :=
    (findRoot_correct _ _ _ _ result).2
  constructor
  · intro after
    obtain ⟨oldRoot, oldCount, before⟩ := valid other
    obtain ⟨hr, hc⟩ := reaches_unique (preserves before) after
    simpa only [hr, hc] using before
  · exact preserves

/-- Two variables belong to one class when their finite paths reach one root. -/
def SameClass (forest : Forest) (left right : Nat) : Prop :=
  ∃ representative size, Reaches forest left representative size ∧ Reaches forest right representative size

/-- Path compression preserves the exact equivalence classes. -/
theorem findRoot_classes (valid : Total forest)
    (result : findRoot fuel forest uv = some found) (left right : Nat) :
    SameClass found.forest left right ↔ SameClass forest left right := by
  simp only [SameClass, findRoot_reaches_iff valid result]

/-- Attach one root below another and add the two stored sizes. -/
def link (forest : Forest) (loser winner loserSize winnerSize : Nat) : Forest :=
  put (put forest loser (.parent winner)) winner (.root (loserSize + winnerSize))

/-- The root selected after linking two different classes. -/
def redirect (loser winner root : Nat) : Nat := if root = loser then winner else root

/-- Only the two merged classes receive the added root size. -/
def mergedSize (loser winner loserSize winnerSize root size : Nat) : Nat :=
  if root = loser ∨ root = winner then loserSize + winnerSize else size

/-- Linking two roots changes precisely their representatives and stored sizes. -/
theorem link_reaches
    (loserRoot : read forest loser = .root loserSize)
    (winnerRoot : read forest winner = .root winnerSize) (different : loser ≠ winner)
    (path : Reaches forest uv representative size) :
    Reaches (link forest loser winner loserSize winnerSize) uv
      (redirect loser winner representative)
      (mergedSize loser winner loserSize winnerSize representative size) := by
  have winnerPath : Reaches (link forest loser winner loserSize winnerSize) winner winner
      (loserSize + winnerSize) := .root (read_put_same ..)
  have loserPath : Reaches (link forest loser winner loserSize winnerSize) loser winner
      (loserSize + winnerSize) := .parent
        (by simp [link, different]) winnerPath
  induction path with
  | @root uv size lookup =>
    by_cases isLoser : uv = loser
    · subst uv
      simpa [redirect, mergedSize] using loserPath
    · by_cases isWinner : uv = winner
      · subst uv
        simpa [redirect, mergedSize, Ne.symm different] using winnerPath
      · simp only [redirect, mergedSize, isLoser, isWinner, or_self, ↓reduceIte]
        exact .root (by simp [link, isLoser, isWinner, lookup])
  | @parent uv next representative size lookup tail ih =>
    have notLoser : uv ≠ loser := by
      intro same; subst uv; rw [loserRoot] at lookup; cases lookup
    have notWinner : uv ≠ winner := by
      intro same; subst uv; rw [winnerRoot] at lookup; cases lookup
    exact .parent (by simp [link, notLoser, notWinner, lookup]) ih

/-- Linking two distinct roots preserves termination throughout the forest. -/
theorem link_total (valid : Total forest)
    (loserRoot : read forest loser = .root loserSize)
    (winnerRoot : read forest winner = .root winnerSize) (different : loser ≠ winner) :
    Total (link forest loser winner loserSize winnerSize) := by
  intro uv
  obtain ⟨root, size, path⟩ := valid uv
  exact ⟨_, _, link_reaches loserRoot winnerRoot different path⟩

/-- Equality of representatives characterizes class membership. -/
theorem sameClass_iff_roots (left : Reaches forest x root₁ size₁)
    (right : Reaches forest y root₂ size₂) : SameClass forest x y ↔ root₁ = root₂ := by
  constructor
  · rintro ⟨root, size, hx, hy⟩
    exact (reaches_unique left hx).1.trans (reaches_unique right hy).1.symm
  · intro same
    subst root₂
    have sizes : size₁ = size₂ := by
      have equality := (reaches_terminal left).symm.trans (reaches_terminal right)
      cases equality
      rfl
    subst size₂
    exact ⟨root₁, size₁, left, right⟩

/-- A root redirect identifies only the two selected roots. -/
theorem redirect_eq_iff (loser winner left right : Nat) :
    redirect loser winner left = redirect loser winner right ↔
      left = right ∨ (left = loser ∧ right = winner) ∨ (left = winner ∧ right = loser) := by
  simp only [redirect]
  split <;> split <;> grind

/-- Linking merges exactly the selected equivalence classes and no others. -/
theorem link_classes (valid : Total forest)
    (loserRoot : read forest loser = .root loserSize)
    (winnerRoot : read forest winner = .root winnerSize) (different : loser ≠ winner)
    (left right : Nat) :
    SameClass (link forest loser winner loserSize winnerSize) left right ↔
      SameClass forest left right ∨
      (SameClass forest left loser ∧ SameClass forest right winner) ∨
      (SameClass forest left winner ∧ SameClass forest right loser) := by
  obtain ⟨lr, ls, hl⟩ := valid left
  obtain ⟨rr, rs, hr⟩ := valid right
  rw [sameClass_iff_roots (link_reaches loserRoot winnerRoot different hl)
    (link_reaches loserRoot winnerRoot different hr)]
  rw [sameClass_iff_roots hl hr,
    sameClass_iff_roots hl (.root loserRoot), sameClass_iff_roots hr (.root winnerRoot),
    sameClass_iff_roots hl (.root winnerRoot), sameClass_iff_roots hr (.root loserRoot)]
  exact redirect_eq_iff ..

/-- Execute both lookups and merge their classes by the stored size comparison. -/
def union (leftFuel rightFuel : Nat) (forest : Forest) (left right : Nat) : Option Forest := do
  let first ← findRoot leftFuel forest left
  let second ← findRoot rightFuel first.forest right
  if first.representative = second.representative then
    some second.forest
  else if first.size < second.size then
    some (link second.forest first.representative second.representative first.size second.size)
  else
    some (link second.forest second.representative first.representative second.size first.size)

/-- Class membership is symmetric. -/
theorem sameClass_symm (same : SameClass forest left right) : SameClass forest right left := by
  obtain ⟨root, size, hl, hr⟩ := same
  exact ⟨root, size, hr, hl⟩

/-- Class membership is transitive. -/
theorem sameClass_trans (first : SameClass forest left middle)
    (second : SameClass forest middle right) : SameClass forest left right := by
  obtain ⟨r₁, s₁, hl, hm⟩ := first
  obtain ⟨r₂, s₂, hm', hr⟩ := second
  obtain ⟨roots, sizes⟩ := reaches_unique hm hm'
  subst r₂; subst s₂
  exact ⟨r₁, s₁, hl, hr⟩

/-- A class can be named by any variable in it or by its representative. -/
theorem root_membership (valid : Total forest) (path : Reaches forest uv root size) (other : Nat) :
    SameClass forest other root ↔ SameClass forest other uv := by
  obtain ⟨r, n, run⟩ := valid other
  rw [sameClass_iff_roots run (.root (reaches_terminal path)), sameClass_iff_roots run path]

/-- Merging an already equal pair introduces no class relation. -/
theorem redundant_merge (same : SameClass forest left right) (x y : Nat) :
    (SameClass forest x y ∨
      (SameClass forest x left ∧ SameClass forest y right) ∨
      (SameClass forest x right ∧ SameClass forest y left)) ↔ SameClass forest x y := by
  constructor
  · rintro (direct | ⟨xl, yr⟩ | ⟨xr, yl⟩)
    · exact direct
    · exact sameClass_trans (sameClass_trans xl same) (sameClass_symm yr)
    · exact sameClass_trans (sameClass_trans xr (sameClass_symm same)) (sameClass_symm yl)
  · exact Or.inl

/-- A successful union terminates future lookups and merges exactly the requested classes. -/
theorem union_correct (valid : Total forest)
    (result : union leftFuel rightFuel forest left right = some output) :
    Total output ∧ ∀ x y,
      SameClass output x y ↔
        SameClass forest x y ∨
        (SameClass forest x left ∧ SameClass forest y right) ∨
        (SameClass forest x right ∧ SameClass forest y left) := by
  cases firstResult : findRoot leftFuel forest left with
  | none => simp [union, firstResult] at result
  | some first =>
    cases secondResult : findRoot rightFuel first.forest right with
    | none => simp [union, firstResult, secondResult] at result
    | some second =>
      have firstValid := findRoot_total valid firstResult
      have secondValid := findRoot_total firstValid secondResult
      have leftPath := (findRoot_correct _ _ _ _ secondResult).2
        ((findRoot_correct _ _ _ _ firstResult).2 (findRoot_correct _ _ _ _ firstResult).1)
      have rightPath := (findRoot_correct _ _ _ _ secondResult).2
        (findRoot_correct _ _ _ _ secondResult).1
      have leftRoot := reaches_terminal leftPath
      have rightRoot := reaches_terminal rightPath
      have unchanged (x y : Nat) : SameClass second.forest x y ↔ SameClass forest x y :=
        (findRoot_classes firstValid secondResult x y).trans (findRoot_classes valid firstResult x y)
      by_cases same : first.representative = second.representative
      · simp [union, firstResult, secondResult, same] at result
        subst output
        refine ⟨secondValid, ?_⟩
        have sameBefore : SameClass forest left right :=
          (unchanged left right).mp ((sameClass_iff_roots leftPath rightPath).mpr same)
        intro x y
        exact (unchanged x y).trans (redundant_merge sameBefore x y).symm
      · by_cases smaller : first.size < second.size
        · simp [union, firstResult, secondResult, same, smaller] at result
          subst output
          refine ⟨link_total secondValid leftRoot rightRoot same, ?_⟩
          intro x y
          rw [link_classes secondValid leftRoot rightRoot same]
          simp only [root_membership secondValid leftPath, root_membership secondValid rightPath, unchanged]
        · simp [union, firstResult, secondResult, same, smaller] at result
          subst output
          refine ⟨link_total secondValid rightRoot leftRoot (Ne.symm same), ?_⟩
          intro x y
          rw [link_classes secondValid rightRoot leftRoot (Ne.symm same)]
          simp only [root_membership secondValid leftPath, root_membership secondValid rightPath, unchanged]
          grind only

/-- Every requested union of a total forest has sufficient finite execution bounds. -/
theorem union_terminates (valid : Total forest) (left right : Nat) :
    ∃ leftFuel rightFuel output, union leftFuel rightFuel forest left right = some output := by
  obtain ⟨root, size, path⟩ := valid left
  obtain ⟨leftFuel, first, firstResult⟩ := findRoot_terminates path
  obtain ⟨root', size', path'⟩ := findRoot_total valid firstResult right
  obtain ⟨rightFuel, second, secondResult⟩ := findRoot_terminates path'
  refine ⟨leftFuel, rightFuel, ?_⟩
  simp [union, firstResult, secondResult]
  split <;> (try split) <;> exact ⟨_, rfl⟩

/-- The empty Haskell map. -/
def empty : Forest := fun _ => none

/-- Initialize the supplied variables as singleton roots. -/
def withInitialValues (variables : List Nat) : Forest :=
  fun uv => if uv ∈ variables then some (.root 1) else none

@[simp] theorem read_empty (uv : Nat) : read empty uv = .root 1 := rfl

@[simp] theorem read_initial (variables : List Nat) (uv : Nat) :
    read (withInitialValues variables) uv = .root 1 := by
  simp only [read, withInitialValues]
  split <;> rfl

/-- Empty and initialized forests both give terminating singleton paths. -/
theorem empty_total : Total empty := fun uv => ⟨uv, 1, .root rfl⟩

theorem initial_total (variables : List Nat) : Total (withInitialValues variables) :=
  fun uv => ⟨uv, 1, .root (read_initial variables uv)⟩

/-- Initial classes identify no distinct variables, including missing entries. -/
theorem initial_classes (variables : List Nat) (left right : Nat) :
    SameClass (withInitialValues variables) left right ↔ left = right :=
  sameClass_iff_roots (.root (read_initial variables left)) (.root (read_initial variables right))

/-- Allocate the next natural identifier and advance the supply. -/
def nextUVar (supply : Nat) : Nat × Nat := (supply + 1, supply)

/-- The returned identifier was not in the previously allocated dense range. -/
theorem nextUVar_fresh (supply : Nat) :
    (nextUVar supply).2 ∉ List.range supply ∧
      List.range (nextUVar supply).1 = List.range supply ++ [(nextUVar supply).2] := by
  simp [nextUVar, List.range_succ]

/-- Count class members in a finite allocation domain. -/
noncomputable def classCount (forest : Forest) (domain : List Nat) (uv : Nat) : Nat := by
  classical
  exact domain.countP (fun other => decide (SameClass forest uv other))

/-- Equal class predicates have equal finite cardinalities. -/
theorem classCount_congr
    (same : ∀ other ∈ domain, SameClass left x other ↔ SameClass right y other) :
    classCount left domain x = classCount right domain y := by
  classical
  apply List.countP_congr
  intro other member
  simpa using same other member

/-- The cardinality of a disjoint union is the sum of the two cardinalities. -/
theorem countP_or_disjoint (domain : List α) (p q : α → Bool)
    (disjoint : ∀ x ∈ domain, p x = true → q x = false) :
    domain.countP (fun x => p x || q x) = domain.countP p + domain.countP q := by
  induction domain with
  | nil => simp
  | cons x xs ih =>
    have tail := ih (fun y member => disjoint y (by simp [member]))
    have head := disjoint x (by simp)
    simp only [List.countP_cons]
    rw [tail]
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

/-- A valid lookup preserves class cardinalities as well as membership. -/
theorem findRoot_counts (valid : Total forest)
    (result : findRoot fuel forest uv = some found) (domain : List Nat) (other : Nat) :
    classCount found.forest domain other = classCount forest domain other :=
  classCount_congr (fun _ _ => findRoot_classes valid result ..)

/-- The winning root names exactly the union of the two former classes. -/
theorem link_winner_class (valid : Total forest)
    (loserRoot : read forest loser = .root loserSize)
    (winnerRoot : read forest winner = .root winnerSize) (different : loser ≠ winner) (other : Nat) :
    SameClass (link forest loser winner loserSize winnerSize) winner other ↔
      SameClass forest loser other ∨ SameClass forest winner other := by
  obtain ⟨root, size, path⟩ := valid other
  have newWinner : Reaches (link forest loser winner loserSize winnerSize) winner winner
      (loserSize + winnerSize) := .root (read_put_same ..)
  rw [sameClass_iff_roots newWinner (link_reaches loserRoot winnerRoot different path),
    sameClass_iff_roots (.root loserRoot) path, sameClass_iff_roots (.root winnerRoot) path]
  simp only [redirect]
  split <;> grind only

/-- Distinct roots have disjoint classes. -/
theorem root_classes_disjoint (loserRoot : read forest loser = .root loserSize)
    (winnerRoot : read forest winner = .root winnerSize) (different : loser ≠ winner)
    (left : SameClass forest loser other) : ¬SameClass forest winner other := by
  intro right
  exact different ((sameClass_iff_roots (.root loserRoot) (.root winnerRoot)).mp
    (sameClass_trans left (sameClass_symm right)))

/-- The merged root's class cardinality is the sum of the two original cardinalities. -/
theorem link_winner_count (valid : Total forest)
    (loserRoot : read forest loser = .root loserSize)
    (winnerRoot : read forest winner = .root winnerSize) (different : loser ≠ winner)
    (domain : List Nat) :
    classCount (link forest loser winner loserSize winnerSize) domain winner =
      classCount forest domain loser + classCount forest domain winner := by
  classical
  unfold classCount
  have pred (other : Nat) :
      decide (SameClass (link forest loser winner loserSize winnerSize) winner other) =
        (decide (SameClass forest loser other) || decide (SameClass forest winner other)) := by
    simp [link_winner_class valid loserRoot winnerRoot different]
  simp only [pred]
  apply countP_or_disjoint
  intro other _ member
  apply decide_eq_false
  exact root_classes_disjoint loserRoot winnerRoot different (of_decide_eq_true member)

/-- Every variable in one class has the same finite class cardinality. -/
theorem classCount_same (same : SameClass forest left right) (domain : List Nat) :
    classCount forest domain left = classCount forest domain right := by
  apply classCount_congr
  intro other _
  exact ⟨fun h => sameClass_trans (sameClass_symm same) h, fun h => sameClass_trans same h⟩

/-- A finite path puts its initial variable and its root in one class. -/
theorem sameClass_root (path : Reaches forest uv root size) : SameClass forest uv root :=
  ⟨root, size, path, .root (reaches_terminal path)⟩

/-- Linking leaves each third root's class cardinality unchanged. -/
theorem link_other_count (valid : Total forest)
    (loserRoot : read forest loser = .root loserSize)
    (winnerRoot : read forest winner = .root winnerSize) (different : loser ≠ winner)
    (otherRoot : read forest other = .root otherSize)
    (notLoser : other ≠ loser) (notWinner : other ≠ winner) (domain : List Nat) :
    classCount (link forest loser winner loserSize winnerSize) domain other = classCount forest domain other := by
  apply classCount_congr
  intro uv _
  rw [link_classes valid loserRoot winnerRoot different]
  have hl : ¬SameClass forest other loser :=
    fun h => notLoser ((sameClass_iff_roots (.root otherRoot) (.root loserRoot)).mp h)
  have hw : ¬SameClass forest other winner :=
    fun h => notWinner ((sameClass_iff_roots (.root otherRoot) (.root winnerRoot)).mp h)
  simp [hl, hw]

/-- Root metadata equals class cardinality on the allocated domain. -/
def SizesCorrect (forest : Forest) (domain : List Nat) : Prop :=
  ∀ uv ∈ domain, ∀ root size, Reaches forest uv root size → size = classCount forest domain uv

/-- Compression preserves exact size metadata on the allocated domain. -/
theorem findRoot_sizes (valid : Total forest) (sizes : SizesCorrect forest domain)
    (result : findRoot fuel forest uv = some found) : SizesCorrect found.forest domain := by
  intro other member root size path
  rw [findRoot_counts valid result]
  exact sizes other member root size ((findRoot_reaches_iff valid result ..).mp path)

/-- Adding two correct root sizes retains all class cardinality metadata. -/
theorem link_sizes (valid : Total forest) (sizes : SizesCorrect forest domain)
    (loserRoot : read forest loser = .root loserSize)
    (winnerRoot : read forest winner = .root winnerSize) (different : loser ≠ winner)
    (loserCount : loserSize = classCount forest domain loser)
    (winnerCount : winnerSize = classCount forest domain winner) :
    SizesCorrect (link forest loser winner loserSize winnerSize) domain := by
  intro uv member root size path
  obtain ⟨oldRoot, oldSize, oldPath⟩ := valid uv
  have newPath := link_reaches loserRoot winnerRoot different oldPath
  have sameSize := (reaches_unique newPath path).2
  rw [← sameSize, classCount_same (sameClass_root newPath)]
  by_cases wasLoser : oldRoot = loser
  · subst oldRoot
    simp only [redirect, mergedSize, ↓reduceIte, true_or]
    rw [link_winner_count valid loserRoot winnerRoot different, loserCount, winnerCount]
  · by_cases wasWinner : oldRoot = winner
    · subst oldRoot
      simp only [redirect, mergedSize, wasLoser, ↓reduceIte, or_true]
      rw [link_winner_count valid loserRoot winnerRoot different, loserCount, winnerCount]
    · simp only [redirect, mergedSize, wasLoser, wasWinner, ↓reduceIte, or_self]
      rw [link_other_count valid loserRoot winnerRoot different (reaches_terminal oldPath) wasLoser wasWinner]
      rw [← classCount_same (sameClass_root oldPath)]
      exact sizes uv member _ _ oldPath

/-- Singleton initialization gives exact root sizes on a domain without duplicates. -/
theorem initial_sizes (variables domain : List Nat) (unique : domain.Nodup) :
    SizesCorrect (withInitialValues variables) domain := by
  intro uv member root size path
  have same := reaches_unique path (.root (read_initial variables uv))
  rw [same.2]
  classical
  unfold classCount
  have predicates : (fun other => decide (SameClass (withInitialValues variables) uv other)) =
      (fun other => other == uv) := by
    funext other
    by_cases same : uv = other
    · subst other; simp [initial_classes]
    · simp [initial_classes, same, Ne.symm same]
  rw [predicates, ← List.count_eq_countP, unique.count_of_mem member]

/-- Union retains exact root sizes when both queried variables are allocated. -/
theorem union_sizes (valid : Total forest) (sizes : SizesCorrect forest domain)
    (leftMember : left ∈ domain) (rightMember : right ∈ domain)
    (result : union leftFuel rightFuel forest left right = some output) : SizesCorrect output domain := by
  cases firstResult : findRoot leftFuel forest left with
  | none => simp [union, firstResult] at result
  | some first =>
    cases secondResult : findRoot rightFuel first.forest right with
    | none => simp [union, firstResult, secondResult] at result
    | some second =>
      have firstValid := findRoot_total valid firstResult
      have secondValid := findRoot_total firstValid secondResult
      have firstSizes := findRoot_sizes valid sizes firstResult
      have secondSizes := findRoot_sizes firstValid firstSizes secondResult
      have leftPath := (findRoot_correct _ _ _ _ secondResult).2
        ((findRoot_correct _ _ _ _ firstResult).2 (findRoot_correct _ _ _ _ firstResult).1)
      have rightPath := (findRoot_correct _ _ _ _ secondResult).2
        (findRoot_correct _ _ _ _ secondResult).1
      have leftCount : first.size = classCount second.forest domain first.representative :=
        (secondSizes left leftMember _ _ leftPath).trans (classCount_same (sameClass_root leftPath) domain)
      have rightCount : second.size = classCount second.forest domain second.representative :=
        (secondSizes right rightMember _ _ rightPath).trans (classCount_same (sameClass_root rightPath) domain)
      by_cases same : first.representative = second.representative
      · simp [union, firstResult, secondResult, same] at result
        subst output
        exact secondSizes
      · by_cases smaller : first.size < second.size
        · simp [union, firstResult, secondResult, same, smaller] at result
          subst output
          exact link_sizes secondValid secondSizes (reaches_terminal leftPath) (reaches_terminal rightPath)
            same leftCount rightCount
        · simp [union, firstResult, secondResult, same, smaller] at result
          subst output
          exact link_sizes secondValid secondSizes (reaches_terminal rightPath) (reaches_terminal leftPath)
            (Ne.symm same) rightCount leftCount

/-- A valid class size cannot exceed the number of allocated variables. -/
theorem stored_size_bound (sizes : SizesCorrect forest domain) (member : uv ∈ domain)
    (path : Reaches forest uv root size) : size ≤ domain.length := by
  rw [sizes uv member root size path]
  exact List.countP_le_length

/-- An allocation below the machine limit keeps the next identifier representable. -/
theorem nextUVar_bound (supply limit : Nat) (room : supply < limit) :
    (nextUVar supply).1 ≤ limit ∧ (nextUVar supply).2 < limit := by
  simp only [nextUVar]
  omega

/-- An assignment gives equal values to all variables in one forest class. -/
def Satisfies (forest : Forest) (assignment : Nat → α) : Prop :=
  ∀ left right, SameClass forest left right → assignment left = assignment right

/-- Singleton initialization imposes no equality between distinct values. -/
theorem initial_satisfies (variables : List Nat) (assignment : Nat → α) :
    Satisfies (withInitialValues variables) assignment := by
  intro left right same
  exact congrArg assignment ((initial_classes variables left right).mp same)

/-- Compression preserves exactly the assignments permitted by the forest. -/
theorem findRoot_satisfies (valid : Total forest)
    (result : findRoot fuel forest uv = some found) (assignment : Nat → α) :
    Satisfies found.forest assignment ↔ Satisfies forest assignment := by
  simp only [Satisfies, findRoot_classes valid result]

/-- Union adds exactly the requested value equality to the assignment constraints. -/
theorem union_satisfies (valid : Total forest)
    (result : union leftFuel rightFuel forest left right = some output) (assignment : Nat → α) :
    Satisfies output assignment ↔
      Satisfies forest assignment ∧ assignment left = assignment right := by
  have classes := (union_correct valid result).2
  constructor
  · intro after
    refine ⟨fun x y h => after x y ((classes x y).mpr (Or.inl h)), ?_⟩
    obtain ⟨lr, ls, lp⟩ := valid left
    obtain ⟨rr, rs, rp⟩ := valid right
    exact after left right ((classes left right).mpr
      (Or.inr (Or.inl ⟨⟨lr, ls, lp, lp⟩, ⟨rr, rs, rp, rp⟩⟩)))
  · rintro ⟨before, equality⟩ x y h
    rcases (classes x y).mp h with direct | ⟨xl, yr⟩ | ⟨xr, yl⟩
    · exact before x y direct
    · exact (before x left xl).trans (equality.trans (before y right yr).symm)
    · exact (before x right xr).trans (equality.symm.trans (before y left yl).symm)

/-- Roots of allocated variables stay inside the allocation domain. -/
def ClosedDomain (forest : Forest) (domain : List Nat) : Prop :=
  ∀ uv ∈ domain, ∀ root size, Reaches forest uv root size → root ∈ domain

/-- Singleton initialization keeps every allocated representative in the domain. -/
theorem initial_closed (variables domain : List Nat) : ClosedDomain (withInitialValues variables) domain := by
  intro uv member root size path
  have same := (reaches_unique path (.root (read_initial variables uv))).1
  simpa [same] using member

/-- Compression preserves allocation-domain closure. -/
theorem findRoot_closed (valid : Total forest) (closed : ClosedDomain forest domain)
    (result : findRoot fuel forest uv = some found) : ClosedDomain found.forest domain := by
  intro other member root size path
  exact closed other member root size ((findRoot_reaches_iff valid result ..).mp path)

/-- A fresh singleton is separate from all previously allocated classes. -/
theorem fresh_separate (closed : ClosedDomain forest domain) (fresh : uv ∉ domain)
    (singleton : read forest uv = .root 1) (member : other ∈ domain) : ¬SameClass forest other uv := by
  rintro ⟨root, size, otherPath, freshPath⟩
  obtain ⟨same, count⟩ := reaches_unique freshPath (.root singleton)
  subst root
  exact fresh (closed other member uv size otherPath)

/-- Counting a class after appending one allocated identifier adds its membership bit. -/
theorem classCount_append_one (forest : Forest) (domain : List Nat) (uv fresh : Nat)
    [Decidable (SameClass forest uv fresh)] :
    classCount forest (domain ++ [fresh]) uv =
      classCount forest domain uv + if SameClass forest uv fresh then 1 else 0 := by
  classical
  simp [classCount, List.countP_append]

/-- Extending allocation with a fresh singleton retains all root-size metadata. -/
theorem sizes_allocate (sizes : SizesCorrect forest domain) (closed : ClosedDomain forest domain)
    (fresh : uv ∉ domain) (singleton : read forest uv = .root 1) :
    SizesCorrect forest (domain ++ [uv]) := by
  classical
  intro other member root size path
  rcases List.mem_append.mp member with old | new
  · rw [classCount_append_one]
    have separate := fresh_separate closed fresh singleton old
    simp only [separate, ↓reduceIte, Nat.add_zero]
    exact sizes other old root size path
  · have same : other = uv := by simpa using new
    subst other
    have count := (reaches_unique path (.root singleton)).2
    rw [count, classCount_append_one]
    have self : SameClass forest uv uv := ⟨uv, 1, .root singleton, .root singleton⟩
    have emptyClass : classCount forest domain uv = 0 := by
      classical
      apply List.countP_eq_zero.mpr
      intro other member
      simp only [decide_eq_true_eq]
      intro same
      exact fresh_separate closed fresh singleton member (sameClass_symm same)
    simp [self, emptyClass]

/-- Allocation of a fresh singleton preserves domain closure. -/
theorem closed_allocate (closed : ClosedDomain forest domain)
    (singleton : read forest uv = .root 1) : ClosedDomain forest (domain ++ [uv]) := by
  intro other member root size path
  rcases List.mem_append.mp member with old | new
  · exact List.mem_append_left _ (closed other old root size path)
  · have same : other = uv := by simpa using new
    subst other
    have sameRoot := (reaches_unique path (.root singleton)).1
    simp [sameRoot]

/-- Linking to an allocated root keeps representatives inside the domain. -/
theorem link_closed (valid : Total forest) (closed : ClosedDomain forest domain)
    (loserRoot : read forest loser = .root loserSize)
    (winnerRoot : read forest winner = .root winnerSize) (different : loser ≠ winner)
    (winnerMember : winner ∈ domain) : ClosedDomain (link forest loser winner loserSize winnerSize) domain := by
  intro uv member root size path
  obtain ⟨oldRoot, oldSize, oldPath⟩ := valid uv
  have same := (reaches_unique (link_reaches loserRoot winnerRoot different oldPath) path).1
  rw [← same]
  unfold redirect
  split
  · exact winnerMember
  · exact closed uv member oldRoot oldSize oldPath

/-- Union of allocated variables keeps all representatives allocated. -/
theorem union_closed (valid : Total forest) (closed : ClosedDomain forest domain)
    (leftMember : left ∈ domain) (rightMember : right ∈ domain)
    (result : union leftFuel rightFuel forest left right = some output) : ClosedDomain output domain := by
  cases firstResult : findRoot leftFuel forest left with
  | none => simp [union, firstResult] at result
  | some first =>
    cases secondResult : findRoot rightFuel first.forest right with
    | none => simp [union, firstResult, secondResult] at result
    | some second =>
      have firstValid := findRoot_total valid firstResult
      have secondValid := findRoot_total firstValid secondResult
      have firstClosed := findRoot_closed valid closed firstResult
      have secondClosed := findRoot_closed firstValid firstClosed secondResult
      have leftPath := (findRoot_correct _ _ _ _ secondResult).2
        ((findRoot_correct _ _ _ _ firstResult).2 (findRoot_correct _ _ _ _ firstResult).1)
      have rightPath := (findRoot_correct _ _ _ _ secondResult).2
        (findRoot_correct _ _ _ _ secondResult).1
      by_cases same : first.representative = second.representative
      · simp [union, firstResult, secondResult, same] at result
        subst output
        exact secondClosed
      · by_cases smaller : first.size < second.size
        · simp [union, firstResult, secondResult, same, smaller] at result
          subst output
          exact link_closed secondValid secondClosed (reaches_terminal leftPath) (reaches_terminal rightPath)
            same (secondClosed right rightMember _ _ rightPath)
        · simp [union, firstResult, secondResult, same, smaller] at result
          subst output
          exact link_closed secondValid secondClosed (reaches_terminal rightPath) (reaches_terminal leftPath)
            (Ne.symm same) (secondClosed left leftMember _ _ leftPath)

end MicroCFTA.UnionFind
