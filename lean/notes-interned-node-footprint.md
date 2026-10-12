# Node identities throughout stored probe records

`InternedNodeIdentityFootprint.Occurs` visits recursive references and node
entries throughout a complete value. It descends into ordinary children,
union members, and the body and both probes of a stored Mu. Thus it includes
bound names that cached free-name metadata removes. It does not mix node
identities with the separate edge-cache identities.

`available_issued` derives actual reservation provenance for each occurrence
from `Available` and coherent canonical readback. `available_below` places
every such identity below the state's next node identity.

`closed_pending_old_footprint` applies this result to arbitrary source
syntax and the actual reservation origin of any hypothetical pending key.
It supplies the state before the reservation. Every node identity and bound
reference anywhere in either resident probe record lies below that state's
fresh supply. The reserved identity itself is now issued under the pending
key. This result does not require a syntax fragment or an initial successful
execution.

This strengthens the pending-key free-name result. The unresolved general
replay case cannot hide a later node or bound reference inside a Mu that has
an empty free-name list. General completion still requires correspondence
between the original probe trace and a later normalized callback whose
result contains only the earlier identities.
