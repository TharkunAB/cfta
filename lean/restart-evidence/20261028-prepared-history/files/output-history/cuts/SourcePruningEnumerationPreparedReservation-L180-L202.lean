          (stage depth (preparedSeed seed) ceiling ceiling index)
          (edgeCount (stage depth (preparedSeed seed) ceiling ceiling index) ceiling) ∧
        Reserved bits depth
          (afterHead (stage depth (preparedSeed seed) ceiling ceiling index) ceiling)
          (massCeil (stage depth (preparedSeed seed) ceiling ceiling index) ceiling ceiling)

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
