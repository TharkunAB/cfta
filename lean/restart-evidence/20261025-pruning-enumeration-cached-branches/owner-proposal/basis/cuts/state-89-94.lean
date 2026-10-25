def reject : EnumerateM Symbol Guard α := fun _ => []

/-- Choose each alternative with the same input state. -/
def choose (values : List α) : EnumerateM Symbol Guard α := fun state =>
  values.map fun value => .ok (value, state)

