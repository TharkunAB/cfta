  intro entry member
  have stored := List.mem_zipIdx_iff_getElem?.mp member
  simp only [Function.comp_def, correct.expandable, stored, Option.map_some, Option.getD_some]

/-- Subtract canonical waiting keys without a lookup or a compression write. -/
def find (state : Cached Symbol Guard) : Option (List Nat) :=
  let candidates := EnumerationIndexSelection.candidates state
  if candidates.isEmpty then none
  else some (candidates.filter fun uv => (state.waiting uv).isNone)

/-- Apply the source preference rule to the pure candidate-minus-waiting result. -/
def next (preference : List Nat → Option Nat) (state : Cached Symbol Guard) : Next :=
  pickNext preference (find state)
