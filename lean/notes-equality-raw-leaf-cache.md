# Physical raw leaf construction and identity

`EqualityRawLeafConstruction` executes every raw source edge request.
The constructor rejects literal Bottom and extracted equalities that fail
the nullary arity check. Rejection still interns the source empty-edge
sentinel. Node normalization removes that edge after the request completes.
The proof preserves its allocation and complete cached payload.

`build_keys` and `build_read` derive exact readback from coherent finite
edge and node caches. The surviving alternatives are precisely the accepted
original declarations. Residual guard syntax remains unchanged. No initial
guard normalization or caller-supplied admission law is required.

`EqualityRawLeafIdentity` compares two completed constructions in an actual
common cache. `same_records` derives equality of complete node payloads
from equality of accepted raw row sets. Rejected requests, source row order,
and duplicate occurrences can differ. `raw_identity_iff` proves that the
global source identity test agrees exactly with equality of the raw progress
states. It does not compare constructor symbols separately.

The next obligation connects actual Cartesian construction with the raw
guard product. Whole stateful projected-pass composition remains separate.
