  SourcePruningEnumerationIncomingReservation.Reserved bits seed (edgeCount seed inherited) ∧
    Reserved bits depth (afterHead seed inherited) (massCeil seed capturedMass inherited)

/-- Reserve every paired entry of one original sibling schedule. -/
def ScanReserved (bits depth : Nat) (seed : Seed) (capturedMass inherited count : Nat) : Prop :=
  ∀ index, index < count →
    HeadReserved bits depth (stage depth seed capturedMass inherited index) capturedMass inherited

/-- Depth zero needs no native query reservation. -/
