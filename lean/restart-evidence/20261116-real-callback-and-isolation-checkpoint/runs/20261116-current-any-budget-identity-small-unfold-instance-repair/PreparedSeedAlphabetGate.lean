import MicroCFTA.SourcePruningEnumerationSharedPreparedReservation

namespace MicroCFTA.SourcePruningEnumerationPreparedSeedAlphabetGate
set_option autoImplicit false
set_option maxHeartbeats 500000
open SourcePruningEnumerationSharedIncomingReservation (Seed)

/-- Check the original first-projection proof with normal imports. -/
theorem prepared_seed_alphabet (seed : Seed) :
    (SourcePruningEnumerationSharedPreparedReservation.preparedSeed seed).1 = seed.1 := by
  rfl

end MicroCFTA.SourcePruningEnumerationPreparedSeedAlphabetGate
