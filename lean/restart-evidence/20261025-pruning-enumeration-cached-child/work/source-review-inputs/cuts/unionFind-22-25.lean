
/-- A missing variable denotes a singleton root. -/
def read (forest : Forest) (uv : Nat) : Entry :=
  (forest uv).getD (.root 1)
