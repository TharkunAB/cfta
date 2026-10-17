# Review of actual native operation invariants

Reviewed at 2026-10-18 01:49 CEST. This review runs no new build or theorem pair.

Cells retains physical machine validity and both native cell families.
Its key predicate is True. NodeGood and EdgeGood still require resident
captured operands and resident returned values. Good also requires heap
Ready, full operation-memo Valid and allocated Fields. Good.of_checked
forgets key-range checks from the earlier stronger physical invariant.

The proof inducts on actual raw Steps. It splits both nested compilation
and the following protected finish step. A warm hit reads availability
from the stored captured cell. A suspended cell compiles its actual stored
request. The proof does not assume that this request equals the requester.
This is sufficient for the physical invariant and is not a semantic-key law.
The edge-body case constructs the actual allocated field prefix. Heap work,
optional Mu, environment entry and read retain their full states. Initial
code safety and operand laws construct the continuation facts. node and
edge derive those initial code laws from NodeReady or EdgeReady; their
public producers require no InputsThrough, Ranges, Graph or future Good.

The generic code theorem still requires initial Safe, Operands and code
field facts. It does not permit arbitrary unchecked bytecode. The node and
edge theorems require an actual completed execution equation. They preserve
invariants but do not construct general recursive completion. node_dispatch
then descends an initially Ready inherited value in the actual returned
operation state and derives new Ready and Valid. No future invariant is a
producer input. Full Parent and outer-worker invariant composition is open.
