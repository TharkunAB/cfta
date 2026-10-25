  | value :: rest => occurrences uv (references value) + total uv rest

/-- Apply one source `IntMap.alter` update to one raw UVar. -/
def bump (change : Int) (uv : Nat) (waiting : Waiting) : Waiting :=
  fun other => if other = uv then encode (read waiting uv + change) else waiting other

/-- Apply the source's ordered counter fold to all suspended references. -/
def count (change : Int) (scs : List Suspended) (waiting : Waiting) : Waiting :=
  scs.foldl (fun previous sc => bump change sc.var previous) waiting
