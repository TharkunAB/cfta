SOURCE-ONLY assessment. No theorem body, compiler check, numeric evaluation or finite-call theorem is supplied.
Keep this count assessment separate from the accepted completed-closure refactor.
The smallest missing pure contract is count inherited value ≤ InternedValueMass.value value, with arbitrary inherited records and any value [S1].
No fixedness, coherence, closedness, readiness or actual-execution premise is needed for this contract.
The existing candidates function admits the stronger private bound: for EVERY fuel and value, (candidates fuel value).length ≤ mass(value) [S1,S2].
Induct on fuel with value generalized. Fuel zero returns the empty list. Positive fuel adds one root candidate.
For a node, sum the child candidate bounds over the actual rows and zipIdx children. Mapping child-index prefixes does not change length [S1].
That sum is bounded by the sum of child masses. Node mass also includes the value, row and list constructors [S2].
For a union, sum member candidate bounds. Union mass contains the root plus every member mass and list constructor [S2].
For Empty and reference, one root candidate has unit mass. Mu is opaque to candidates and contributes one candidate, while mass includes all three Mu payload fields [S1,S2].
The same child index may occur in different rows; duplicate candidate paths do not weaken this length upper bound.
Filtering by PositiveAt and each eraseDups can only reduce length. Quotient.map preserves length, so the uniform candidate bound implies the public count bound [S1].
This is a proof route, not a checked new lemma. No new enumeration or quotient framework is needed.
An additive private candidate-length lemma plus one public count_le_mass in the EXISTING count module can access its private definitions directly.
A separate module cannot access those private definitions by their source names; do not copy another enumeration merely to expose this bound.
The actual mass bridge ALREADY EXISTS: Fits.stored and InternedValueMassHeap.available give mass(value)≤profile.mass for Available value in the SAME checked heap [S3,S4].
Compose that bridge with the missing pure count bound to obtain BOTH count and mass≤profile.mass at a genuine entry.
Thus a finite grid 0≤count≤M, 0≤mass≤M with M=entryProfile.mass covers every actual available entry value, for every inherited payload.
C depends only on budget, these two numbers and the exact entry seed. No inherited-record enumeration or C monotonicity is required [S5].
For each grid pair, the proposed reservation joins C.output and oldSchedule.node(C.W), both computed at the SAME current seed [S5,S6].
Joining all profiles and alphabets with the entry seed gives one finite next seed. Iterating that construction N times before selecting bits is a plausible same-width reservation route.
That finite-N coverage/packet-transport theorem remains unproved. Do not replace it by an arbitrary future Room premise or assume that the first Room reserves later calls.
Completed closure, resource-writer Origins and actual return-resource projections still need their own public entry-packet assembly.
The existing coarse capacity lower-bound assessment remains unchanged: a mathematical finite width can be very large; this proposal gives no fixed-64-bit feasibility or Haskell runtime claim.
