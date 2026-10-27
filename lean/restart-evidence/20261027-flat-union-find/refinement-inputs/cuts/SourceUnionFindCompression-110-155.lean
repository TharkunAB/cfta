  exact UnionFind.findRoot_total valid completed

/-- Conditional writes preserve exactly the existing union-find classes. -/
theorem findRoot_classes (valid : Total forest)
    (completed : findRoot fuel forest uv = some found) (left right : Nat) :
    SameClass found.forest left right ↔ SameClass forest left right := by
  rw [findRoot_eq] at completed
  exact UnionFind.findRoot_classes valid completed left right

/-- Conditional writes retain all correct stored class sizes. -/
theorem findRoot_sizes (valid : Total forest) (sizes : SizesCorrect forest domain)
    (completed : findRoot fuel forest uv = some found) : SizesCorrect found.forest domain := by
  rw [findRoot_eq] at completed
  exact UnionFind.findRoot_sizes valid sizes completed

/-- Conditional writes preserve all permitted assignments to equality variables. -/
theorem findRoot_satisfies (valid : Total forest)
    (completed : findRoot fuel forest uv = some found) (assignment : Nat → α) :
    Satisfies found.forest assignment ↔ Satisfies forest assignment := by
  rw [findRoot_eq] at completed
  exact UnionFind.findRoot_satisfies valid completed assignment

/-- The public find wrapper returns the representative and compressed state. -/
def find (fuel : Nat) (forest : Forest) (uv : Nat) : Option (Nat × Forest) :=
  (findRoot fuel forest uv).map fun found => (found.representative, found.forest)

/-- The optimized public wrapper has the identical representative and final map. -/
theorem find_eq (fuel : Nat) (forest : Forest) (uv : Nat) :
    find fuel forest uv = (UnionFind.findRoot fuel forest uv).map
      (fun found => (found.representative, found.forest)) := by rw [find, findRoot_eq]

/-- The source union uses conditional-write lookup before its unchanged size-based link. -/
def union (leftFuel rightFuel : Nat) (forest : Forest) (left right : Nat) : Option Forest := do
  let first ← findRoot leftFuel forest left
  let second ← findRoot rightFuel first.forest right
  if first.representative = second.representative then some second.forest
  else if first.size < second.size then
    some (link second.forest first.representative second.representative first.size second.size)
  else some (link second.forest second.representative first.representative second.size first.size)

/-- Both compressed lookups preserve the complete existing union result. -/
theorem union_eq (leftFuel rightFuel : Nat) (forest : Forest) (left right : Nat) :
    union leftFuel rightFuel forest left right = UnionFind.union leftFuel rightFuel forest left right := by
  simp only [union, UnionFind.union, findRoot_eq]

end MicroCFTA.SourceUnionFindCompression
