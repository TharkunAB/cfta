      iterate (fun current => final depth (afterHead current ceiling) (massCeil current ceiling ceiling))
        (narrowSeed seed) (rows seed)

/-- One sibling pays its head and then its smaller-depth callback. -/
noncomputable def step (depth : Nat) (seed : Seed) (capturedMass inherited : Nat) : Seed :=
  final depth (afterHead seed inherited) (massCeil seed capturedMass inherited)

/-- A sibling schedule retains the same captured mass and inherited length bounds. -/
