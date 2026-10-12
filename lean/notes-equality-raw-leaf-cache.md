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

`EqualityRawLeafProduct` connects actual Cartesian construction with the
raw guard product. It reads physical input declarations, retains the source
hash-join order, and executes all joined requests. The proof derives the
stored empty equality field. Source conjunction preserves that field and
merges the residuals. `intersect_read` covers the identity shortcut and the
Cartesian branch, including rejected output rows.

`EqualityRawLeafProgress` derives finite raw certificates for the exact
ordered output request list. `intersect_strict` proves that a changed
physical identity decreases the derived raw leaf rank. It derives the
semantic change from physical identity and complete record readback.
No caller-supplied injectivity or progress law is required.

`EqualityRawLeafAvailability` retains complete child payloads through both
accepted and rejected requests. `raw_leaves` discharges the occurrence
compiler's leaf contract. `built_nullary` proves that every surviving
outgoing edge has no child records. `raw_ordinary` derives ordinary worker
inputs, and `built_require` gives the exact allocation-free requirement
result. Whole stateful projected-pass composition remains separate.
