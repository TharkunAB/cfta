# Observed opaque receipt: constructor annotation repair

Status: UNCOMPILED. Root owns strict validation and publication.
The original observed-shared-opaque packet remains immutable.

The previous new header did not elaborate. Its three standalone equalities
used `.complete` without an expected receipt type. The right-side constructors
and two `finished.core` projections then failed as well. The original resource
producer header was checked before this draft and remains unchanged.

This candidate qualifies only the three left-side constructors as
`SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result.complete`.
The actual caller argument determines the width. This gives each equality its
actual selected-edge receipt type. Lean can then infer the right-side receipt
constructor and the existential cache types.

The three qualifications occur in the retained complete, stopped and rejected
resource alternatives. This change normalizes annotations in the previously
ill-elaborated new header. It does not change a checked theorem statement.
Removing exactly these three qualifications recovers the previous candidate
byte for byte. The theorem proof body and every premise remain byte for byte.
The resource fields and their order remain unchanged.

RAW-ILL-ELABORATED-OBSERVED-HEADER.lean.txt preserves the previous raw header.
NORMALIZED-OBSERVED-HEADER-UNCOMPILED.lean.txt preserves the repaired new header.
ORIGINAL-OPAQUE-RESOURCE-HEADER.lean.txt preserves the checked producer header.
Source pins include the original diagnostic log. ORIGINAL-DIAGNOSTICS.txt keeps
only its error lines. This packet contains no compiler run or successful result.

The complete emitted-resource worker, prepared-fold producer and common finite
original-root witness remain OPEN. No Haskell defect is established. No Haskell
source, contract or FINDINGS file changed. The clear-writing checks were applied.
