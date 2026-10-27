    Le (stage depth (narrowSeed seed) ceiling ceiling count).2 (final (depth + 1) seed ceiling).2 ∧
      (stage depth (narrowSeed seed) ceiling ceiling count).1 ⊆ (final (depth + 1) seed ceiling).1 := by
  rw [final_succ]
  exact count_mono depth (narrowSeed seed) ceiling ceiling bounded

/-- A parked route can use the first paired stage without an actual edge execution. -/
theorem first_le_final (depth : Nat) (seed : Seed) (ceiling : Nat) :
    Le (step depth (narrowSeed seed) ceiling ceiling).2 (final (depth + 1) seed ceiling).2 ∧
      (step depth (narrowSeed seed) ceiling ceiling).1 ⊆ (final (depth + 1) seed ceiling).1 :=
  stage_le_final depth seed ceiling 1 (rows_positive seed)

/-- A reservation checks only the recursively planned original query entries. -/
def Reserved : Nat → Nat → Seed → Nat → Prop
  | _bits, 0, _seed, _ceiling => True
  | bits, depth + 1, seed, ceiling =>
      ∀ index, index < rows seed →
        SourcePruningEnumerationIncomingReservation.Reserved bits
          (stage depth (narrowSeed seed) ceiling ceiling index)
          (edgeCount (stage depth (narrowSeed seed) ceiling ceiling index) ceiling) ∧
        Reserved bits depth
          (afterHead (stage depth (narrowSeed seed) ceiling ceiling index) ceiling)
          (massCeil (stage depth (narrowSeed seed) ceiling ceiling index) ceiling ceiling)

/-- Reserve an edge and its smaller-depth callback at the same planned head endpoint. -/
def HeadReserved (bits depth : Nat) (seed : Seed) (capturedMass inherited : Nat) : Prop :=
  SourcePruningEnumerationIncomingReservation.Reserved bits seed (edgeCount seed inherited) ∧
    Reserved bits depth (afterHead seed inherited) (massCeil seed capturedMass inherited)

/-- Reserve every paired entry of one original sibling schedule. -/
def ScanReserved (bits depth : Nat) (seed : Seed) (capturedMass inherited count : Nat) : Prop :=
  ∀ index, index < count →
    HeadReserved bits depth (stage depth seed capturedMass inherited index) capturedMass inherited

/-- Depth zero needs no native query reservation. -/
theorem reserved_zero (bits : Nat) (seed : Seed) (ceiling : Nat) : Reserved bits 0 seed ceiling :=
  True.intro

/-- The positive-depth driver reservation is its exact original sibling reservation. -/
theorem reserved_succ_iff (bits depth : Nat) (seed : Seed) (ceiling : Nat) :
    Reserved bits (depth + 1) seed ceiling ↔
      ScanReserved bits depth (narrowSeed seed) ceiling ceiling (rows seed) := Iff.rfl

/-- A driver reservation supplies its full original sibling schedule. -/
theorem Reserved.scan {bits depth ceiling : Nat} {seed : Seed}
    (reservation : Reserved bits (depth + 1) seed ceiling) :
    ScanReserved bits depth (narrowSeed seed) ceiling ceiling (rows seed) := reservation

/-- An empty sibling schedule requires no paired reservations. -/
