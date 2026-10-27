/-- One extra sibling slot also pays a parked expansion when no ordinary row exists. -/
def rows (seed : Seed) : Nat := scalar (narrowSeed seed).2 + 1

/-- The original mass ceiling and depth determine the complete finite forecast. -/
noncomputable def final : Nat → Seed → Nat → Seed
  | 0, seed, _ceiling => seed
  | depth + 1, seed, ceiling =>
      iterate (fun current => final depth (afterHead current ceiling) (massCeil current ceiling ceiling))
        (narrowSeed seed) (rows seed)

/-- One sibling pays its head and then its smaller-depth callback. -/
noncomputable def step (depth : Nat) (seed : Seed) (capturedMass inherited : Nat) : Seed :=
  final depth (afterHead seed inherited) (massCeil seed capturedMass inherited)

/-- A sibling schedule retains the same captured mass and inherited length bounds. -/
noncomputable def stage (depth : Nat) (seed : Seed) (capturedMass inherited count : Nat) : Seed :=
  iterate (fun current => step depth current capturedMass inherited) seed count

/-- Depth zero retains the literal original seed. -/
theorem final_zero (seed : Seed) (ceiling : Nat) : final 0 seed ceiling = seed := rfl

/-- Positive depth uses only its original narrowing seed and original mass ceiling. -/
theorem final_succ (depth : Nat) (seed : Seed) (ceiling : Nat) :
    final (depth + 1) seed ceiling =
      stage depth (narrowSeed seed) ceiling ceiling (rows seed) := rfl

/-- A depth-zero callback does not enlarge the edge endpoint. -/
theorem step_zero (seed : Seed) (capturedMass inherited : Nat) :
    step 0 seed capturedMass inherited = afterHead seed inherited := rfl

/-- An empty sibling schedule retains its seed. -/
theorem stage_zero (depth : Nat) (seed : Seed) (capturedMass inherited : Nat) :
    stage depth seed capturedMass inherited 0 = seed := rfl

/-- The first paired stage precedes the remaining siblings. -/
theorem stage_succ (depth : Nat) (seed : Seed) (capturedMass inherited count : Nat) :
    stage depth seed capturedMass inherited (count + 1) =
      stage depth (step depth seed capturedMass inherited) capturedMass inherited count := rfl

/-- Parts of the same sibling schedule compose at their exact planned seed. -/
theorem stage_add (depth : Nat) (seed : Seed) (capturedMass inherited first last : Nat) :
    stage depth seed capturedMass inherited (first + last) =
      stage depth (stage depth seed capturedMass inherited first) capturedMass inherited last :=
  iterate_add _ seed first last

/-- The next paired forecast follows the entire preceding sibling prefix. -/
theorem stage_succ_right (depth : Nat) (seed : Seed) (capturedMass inherited count : Nat) :
    stage depth seed capturedMass inherited (count + 1) =
      step depth (stage depth seed capturedMass inherited count) capturedMass inherited :=
  stage_add depth seed capturedMass inherited count 1

/-- The first narrowed seed retains all original numeric and guard bounds. -/
theorem narrowSeed_ge (seed : Seed) :
