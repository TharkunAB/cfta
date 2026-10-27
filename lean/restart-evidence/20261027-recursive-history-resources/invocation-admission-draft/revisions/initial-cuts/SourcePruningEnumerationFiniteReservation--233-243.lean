
/-- A nonempty scan supplies the current edge and callback reservation. -/
theorem ScanReserved.head {bits depth capturedMass inherited count : Nat} {seed : Seed}
    (reservation : ScanReserved bits depth seed capturedMass inherited (count + 1)) :
    HeadReserved bits depth seed capturedMass inherited :=
  ((scan_reserved_succ_iff bits depth seed capturedMass inherited count).mp reservation).1

/-- The remaining scan uses the paired step's exact planned endpoint. -/
theorem ScanReserved.tail {bits depth capturedMass inherited count : Nat} {seed : Seed}
    (reservation : ScanReserved bits depth seed capturedMass inherited (count + 1)) :
    ScanReserved bits depth (step depth seed capturedMass inherited) capturedMass inherited count :=
