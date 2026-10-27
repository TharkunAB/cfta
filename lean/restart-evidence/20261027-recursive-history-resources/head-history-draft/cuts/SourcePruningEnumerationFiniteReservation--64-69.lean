noncomputable def step (depth : Nat) (seed : Seed) (capturedMass inherited : Nat) : Seed :=
  final depth (afterHead seed inherited) (massCeil seed capturedMass inherited)

/-- A sibling schedule retains the same captured mass and inherited length bounds. -/
noncomputable def stage (depth : Nat) (seed : Seed) (capturedMass inherited count : Nat) : Seed :=
  iterate (fun current => step depth current capturedMass inherited) seed count
