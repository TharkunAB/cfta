  | nil => simp [occurrences]
  | cons sc rest ih => simp [occurrences, ih, Int.add_assoc]

/-- The reference scan counts only unenumerated slots. -/
def total (uv : Nat) : List (UVarValue Symbol) → Int
  | [] => 0
  | value :: rest => occurrences uv (references value) + total uv rest

/-- Apply one source `IntMap.alter` update to one raw UVar. -/
