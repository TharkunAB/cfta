/-- Every hole of a fragment names an allocated slot. -/
def FragmentBound (limit : Nat) : Fragment Symbol → Prop
  | .hole uv => uv < limit
  | .node _ children => FragmentsBound limit children

/-- The finite child list contains only allocated holes. -/
def FragmentsBound (limit : Nat) : List (Fragment Symbol) → Prop
  | [] => True
  | child :: rest => FragmentBound limit child ∧ FragmentsBound limit rest
