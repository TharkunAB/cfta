
/-- A driver reservation pays any shorter original ordinary row list. -/
theorem Reserved.ordinary {bits depth ceiling : Nat} {seed : Seed}
    (reservation : Reserved bits (depth + 1) seed ceiling) (count : Nat) (bounded : count ≤ rows seed) :
    ScanReserved bits depth (preparedSeed seed) ceiling ceiling count :=
  reservation.scan.prefix bounded

/-- The head reservation covers its actual edge cost without another execution premise. -/
theorem HeadReserved.edge {bits depth capturedMass inherited actualCost : Nat} {seed : Seed}
    (reservation : HeadReserved bits depth seed capturedMass inherited)
    (bounded : actualCost ≤ edgeCount seed inherited) :
    SourcePruningEnumerationIncomingReservation.Reserved bits seed actualCost :=
  reservation.1.prefix bounded

/-- The callback retains the planned mass ceiling rather than changing its recursive reservation. -/
theorem HeadReserved.callback {bits depth capturedMass inherited : Nat} {seed : Seed}
    (reservation : HeadReserved bits depth seed capturedMass inherited) :
    Reserved bits depth (afterHead seed inherited) (massCeil seed capturedMass inherited) :=
