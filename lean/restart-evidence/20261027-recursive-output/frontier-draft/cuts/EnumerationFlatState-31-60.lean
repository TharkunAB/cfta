  /-- Recursion keys retained at each raw variable. -/
  recursionAncestry : Nat → List RecursionKey
  /-- Recursion keys of the current expansion. -/
  expansionAncestry : List RecursionKey

/-- Core state correspondence retains every field except the forest shape. -/
structure Related (flat : State Symbol Guard) (earlier : EnumerationState.State Symbol Guard) : Prop where
  /-- The current direct-parent representation is valid. -/
  valid : FlatUnionFind.Valid flat.representatives
  /-- Every variable has the same representative and stored class size. -/
  representatives : FlatUnionFind.Represents flat.representatives earlier.representatives
  /-- Both states use the same fresh identifier. -/
  counter : flat.counter = earlier.counter
  /-- All raw value slots are equal. -/
  values : flat.values = earlier.values
  /-- All residual obligations are equal and ordered alike. -/
  obligations : flat.obligations = earlier.obligations
  /-- Both per-variable ancestry functions are equal. -/
  recursionAncestry : flat.recursionAncestry = earlier.recursionAncestry
  /-- Both expansion ancestry lists are equal. -/
  expansionAncestry : flat.expansionAncestry = earlier.expansionAncestry

/-- The root starts at variable zero with a singleton direct-parent forest. -/
def initial (root : Nat) : State Symbol Guard :=
  ⟨1, FlatUnionFind.withInitialValues [0], [.unenumerated (some root) []], [], fun _ => [], []⟩

/-- Initialization relates the complete six-field core states. -/
theorem initial_related (root : Nat) :
    Related (initial (Symbol := Symbol) (Guard := Guard) root) (EnumerationState.initial root) :=
  ⟨FlatUnionFind.initial_valid [0], FlatUnionFind.initial_represents [0], rfl, rfl, rfl, rfl, rfl⟩
