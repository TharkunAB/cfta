# Sequential reconstruction proposal

This package contains finite checks. It proves no general reconstruction equality.
It changes no production source and records no Haskell defect.

The executable fixture builds a closed outer raw Mu from empty.
Its ordinary node contains an outer-self child and a nested raw Mu.
One source ignores the inner local. The other source uses both locals.
The test selects the outer Mu or the stored inner Mu.
Each test reconstructs the stored body first and the ordinary probe second.
Both reconstructions use the same replacement and the second starts at the first returned heap.

The executable grid has 40 cases. All cases return successfully.
All result reference pairs agree. The second call allocates no further node identity.
Thirty cases have `usesLocal = true`. The other ten select the unused inner Mu.
The ten replacements include empty, Depth, selected ordinary and self references,
the captured outer self, the inner ordinary reference, and actual composite payloads.
The grid checks result references. It does not prove a universal value law.

Two kernel integrations prove complete `Value` equality.
The first uses the outer Mu with a raw unused inner Mu and the own ordinary reference.
The second uses the open inner used Mu and replaces its self with its captured outer self.
Both derive Ready from their own closed source construction.
Both derive replacement availability and the actual first-writer history.
Both retain the original selected Mu and prove exact warm replay at the common final heap.
The second proves that the root is closed and the selected inner Mu is open.
The selected integrations use only propext, Classical.choice, and Quot.sound.

The earlier StoredRebindBoundary remains valid.
It compares a repaired body result with an unreconstructed original ordinary probe.
These checks reconstruct both sides. They therefore test a different proposition.
The Haskell substitution comments permit smart removal of the open raw unused inner wrapper.

A possible general theorem would add equality to StoredReconstructionReplay.mu
for an actual source-started selected Mu and an available replacement.
It must derive equality through arbitrary nested used-Mu callbacks and earlier warm winners.
Two-call completion, availability, publication history, and common-final replay already exist.
They do not prove the required equality or a row-origin relation.
The remaining proof needs normalization and substitution fusion on both callback results.
It must retain the original fresh ordinary/reserved names and exact selected probes.
Depth can alias a capture. No global Depth freshness is justified.
These finite cases require no fresh replacement: several replacements deliberately alias markers or captures.
